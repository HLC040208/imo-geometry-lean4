# 场景 A：测评单个文件
# 如果你只想测试某一个 IMO 题目或特定的 Lean 文件，在终端输入：
# python leanscope.py 文件名

# 场景 B：批量测评整个文件夹
# 如果你想一次性跑完所有的题目，直接指向文件夹路径：
# python leanscope.py 文件夹路径
# 脚本会自动递归搜索该文件夹下所有的 .lean 文件并逐一运行。

# 场景 C：自定义超时时间
# 有些 IMO 难题（比如涉及复杂圆锥曲线或大搜索空间的题目）可能需要很久。
# 如果你不想等太久，可以设置 1 分钟强制停止：
# python leanscope.py 文件名/文件夹路径 --timeout 60

import argparse
import csv
import json
import re
import subprocess
import time
from pathlib import Path


def find_project_root(start: Path) -> Path:
    """
    向上寻找包含 lakefile.lean 的 Lean 项目根目录。
    这样脚本不管从哪一层目录调用，都能在正确的项目上下文里执行 `lake env lean`。
    """
    for path in [start, *start.parents]:
        if (path / "lakefile.lean").exists():
            return path
    raise FileNotFoundError(
        f"Cannot find lakefile.lean when searching upward from: {start}"
    )


class LeanScope:
    """
    LeanScope: Lean 4 形式化证明通用性能监测工具
    设计理念：非侵入式探测，通过拦截编译器诊断流实现多维度性能指标采集。
    """

    def __init__(self, timeout=300, project_root: Path | None = None):
        self.timeout = timeout
        self.results = []
        self.project_root = project_root or find_project_root(Path.cwd())

    def _empty_metrics(self, file_path: Path) -> dict:
        return {
            "file_name": file_path.name,
            "file_path": str(file_path),
            "time_s": 0.0,
            "heartbeats": 0,
            "max_tactic_s": 0.0,
            "errors": 0,
            "status": "Error",
            "returncode": None,
            "message": "",
        }

    def _extract_error_summary(self, output: str) -> str:
        for line in output.splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            if " error:" in stripped or stripped.startswith("error:"):
                return stripped
        return ""

    def _coerce_text(self, data) -> str:
        if data is None:
            return ""
        if isinstance(data, bytes):
            return data.decode("utf-8", errors="replace")
        return str(data)

    def _seconds_from_duration(self, value: str, unit: str) -> float:
        duration = float(value)
        return duration / 1000 if unit == "ms" else duration

    def _parse_json_error(self, line: str) -> str:
        try:
            payload = json.loads(line)
        except json.JSONDecodeError:
            return ""

        if payload.get("severity") != "error":
            return ""

        file_name = payload.get("fileName", "")
        pos = payload.get("pos") or {}
        line_no = pos.get("line")
        col_no = pos.get("column")
        location_parts = []
        if file_name:
            location_parts.append(file_name)
        if line_no is not None and col_no is not None:
            location_parts.append(f"{line_no}:{col_no}")
        location = ":".join(location_parts)

        message = str(payload.get("data", "")).strip()
        if location and message:
            return f"{location}: {message}"
        return location or message

    def _parse_output(self, output: str, elapsed_s: float | None = None) -> dict:
        """
        利用正则表达式从 Lean 的输出中提取量化指标。
        新版本同时扫描 stdout/stderr，避免不同 Lean 版本或 lake 包装行为导致漏检。
        """
        time_s = round(elapsed_s, 3) if elapsed_s is not None else 0.0
        if time_s == 0.0:
            compilation_matches = re.findall(
                r"compilation of .*? took (\d+(?:\.\d+)?)ms", output
            )
            if compilation_matches:
                time_s = round(float(compilation_matches[-1]) / 1000, 3)
            else:
                profile_matches = re.findall(
                    r"\b(?:import|elaboration)\s+took\s+(\d+(?:\.\d+)?)(ms|s)\b",
                    output,
                )
                if profile_matches:
                    value, unit = profile_matches[-1]
                    time_s = round(self._seconds_from_duration(value, unit), 3)

        old_hb_matches = [int(match) for match in re.findall(r"heartbeats:\s*(\d+)", output)]
        trace_hb_matches = [
            int(round(float(match)))
            for match in re.findall(
                r"\[[A-Za-z][A-Za-z0-9_.]*\]\s*\[(\d+(?:\.\d+)?)\]",
                output,
            )
        ]
        heartbeat_candidates = old_hb_matches + trace_hb_matches
        heartbeats = max(heartbeat_candidates) if heartbeat_candidates else 0

        tactic_matches = [
            self._seconds_from_duration(value, unit)
            for value, unit in re.findall(
                r"tactic execution(?: of [^\n]+?)?(?: took)?\s+(\d+(?:\.\d+)?)(ms|s)",
                output,
            )
        ]
        max_tactic_s = round(max(tactic_matches), 3) if tactic_matches else 0.0

        text_error_count = len(re.findall(r"(^|\n).*?\berror:\b", output))
        json_error_count = len(re.findall(r'"severity"\s*:\s*"error"', output))
        error_count = text_error_count + json_error_count

        message = self._extract_error_summary(output)
        if not message:
            for line in output.splitlines():
                message = self._parse_json_error(line.strip())
                if message:
                    break

        return {
            "time_s": time_s,
            "heartbeats": heartbeats,
            "max_tactic_s": max_tactic_s,
            "errors": error_count,
            "message": message,
        }

    def _extra_dynlibs(self) -> list[str]:
        candidates = [
            self.project_root / ".lake" / "packages" / "cvc5" / ".lake" / "build" / "lib",
        ]
        dynlibs: list[str] = []
        patterns = ["libcvc5-Solver-*.so", "libcvc5-Solver-*.dylib"]
        for lib_dir in candidates:
            if not lib_dir.exists():
                continue
            for pattern in patterns:
                for path in sorted(lib_dir.glob(pattern)):
                    dynlibs.append(str(path))
        return dynlibs

    def run_file(self, file_path):
        """
        启动 Lean 编译器并采集诊断数据。
        """
        file_path = Path(file_path).resolve()
        metrics = self._empty_metrics(file_path)
        print(f"🔬 Testing: {file_path.name}", end=" ", flush=True)

        cmd = [
            "lake",
            "env",
            "lean",
            "--json",
        ]
        for dynlib in self._extra_dynlibs():
            cmd.extend(["--load-dynlib", dynlib])
        cmd += [
            "-D",
            "profiler=true",
            "-D",
            "diagnostics=true",
            "-D",
            "trace.profiler=true",
            "-D",
            "trace.profiler.useHeartbeats=true",
            "-D",
            "trace.profiler.threshold=1000",
            str(file_path),
        ]

        process = None
        start_time = time.perf_counter()
        try:
            process = subprocess.Popen(
                cmd,
                cwd=self.project_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            stdout, stderr = process.communicate(timeout=self.timeout)
            output = "\n".join(part for part in [stdout, stderr] if part)
            elapsed_s = time.perf_counter() - start_time

            metrics.update(self._parse_output(output, elapsed_s=elapsed_s))
            metrics["returncode"] = process.returncode
            metrics["status"] = "Success" if process.returncode == 0 else "Error"

            self.results.append(metrics)
            print(
                f"| Status: {metrics['status']} | "
                f"Time: {metrics['time_s']}s | "
                f"Heartbeats: {metrics['heartbeats']}"
            )

        except subprocess.TimeoutExpired as exc:
            partial_stdout = self._coerce_text(exc.stdout)
            partial_stderr = self._coerce_text(exc.stderr)

            if process is not None:
                process.kill()
                stdout, stderr = process.communicate()
            else:
                stdout, stderr = "", ""

            stdout = self._coerce_text(stdout)
            stderr = self._coerce_text(stderr)

            output = "\n".join(
                part
                for part in [partial_stdout, partial_stderr, stdout, stderr]
                if part
            )
            elapsed_s = time.perf_counter() - start_time

            metrics.update(self._parse_output(output, elapsed_s=elapsed_s))
            metrics["time_s"] = round(metrics["time_s"], 3)
            metrics["status"] = "Timeout"
            metrics["returncode"] = None
            if not metrics["message"]:
                metrics["message"] = "Process exceeded timeout"

            self.results.append(metrics)
            print(
                f"| Status: Timeout | "
                f"Time: {metrics['time_s']}s | "
                f"Heartbeats: {metrics['heartbeats']}"
            )

        except FileNotFoundError as exc:
            metrics["status"] = "Error"
            metrics["message"] = str(exc)
            self.results.append(metrics)
            print("| ❌ Missing executable or project root")

    def save_report(self, fmt="csv"):
        """
        导出 CSV/JSON 报告。
        所有结果行都使用固定 schema，避免第一条记录刚好超时时导致后续写表失败。
        """
        if not self.results:
            return

        output_file = f"perf_report.{fmt}"
        fieldnames = [
            "file_name",
            "file_path",
            "status",
            "returncode",
            "time_s",
            "heartbeats",
            "max_tactic_s",
            "errors",
            "message",
        ]

        if fmt == "csv":
            with open(output_file, "w", newline="", encoding="utf-8") as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writeheader()
                writer.writerows(self.results)
        else:
            with open(output_file, "w", encoding="utf-8") as f:
                json.dump(self.results, f, indent=2, ensure_ascii=False)

        print(f"✅ Report saved to {output_file}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Lean 4 General Performance Scoper")
    parser.add_argument("target", help="Lean file or directory to test")
    parser.add_argument("--timeout", type=int, default=3600, help="Timeout in seconds")
    parser.add_argument(
        "--format",
        choices=["csv", "json"],
        default="csv",
        help="Report output format",
    )
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    project_root = find_project_root(script_dir)

    scope = LeanScope(timeout=args.timeout, project_root=project_root)
    raw_target = Path(args.target)
    if raw_target.is_absolute():
        target = raw_target.resolve()
    else:
        cwd_target = raw_target
        script_target = script_dir / raw_target
        project_target = project_root / raw_target
        if cwd_target.exists():
            target = cwd_target.resolve()
        elif script_target.exists():
            target = script_target.resolve()
        else:
            target = project_target.resolve()

    if target.is_file():
        scope.run_file(target)
    elif target.is_dir():
        for lean_file in sorted(target.rglob("*.lean")):
            scope.run_file(lean_file)
    else:
        raise SystemExit(f"Target does not exist: {target}")

    scope.save_report(args.format)
