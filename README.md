# IMO Geometry Full Completion (IMO_00+) 
### Based on LeanGeo Framework

[![Lean4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Framework](https://img.shields.io/badge/Framework-LeanGeo-orange.svg)](https://github.com/project-numina/LeanGeo)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

本项目是对 [Project-Numina/LeanGeo](https://github.com/project-numina/LeanGeo) 环境下 `IMO_00+` 基准目录的深度补全工程。通过严谨的形式化建模，本项目完整实现了该目录下 **2000 年至 2025 年** 所有国际数学奥林匹克（IMO）几何题的代码证明。

## 🎯 项目核心贡献

- **全量代码补全**：针对 `IMO_00+` 目录进行了地毯式开发，确保 26 年间每一道 IMO 几何题均有对应的 Lean 4 形式化证明。
- **环境完全兼容**：严格遵循 `LeanGeo` 框架的定义规范与原语，所有证明均可在 LeanGeo 标准配置环境中直接编译通过。
- **性能基准测评**：引入自研工具 `LeanScope`，对全量补全后的题目进行了逻辑心跳（Heartbeats）采样，建立了竞赛级几何证明的复杂度基准。

## 📂 目录结构

```text
.
├── IMO_00+/             # 核心成果：包含 2000-2025 年全部 IMO 几何证明文件
├── LeanScope/           # 性能测评工具集
│   └── leanscope.py     # 自动化性能监测脚本
├── lakefile.lean        # 项目配置（引入 LeanGeo 与 Mathlib 依赖）
├── lean-toolchain       # Lean 4 工具链版本定义
├── LICENSE              # MIT 开源协议
└── README.md            # 项目说明文档
```

## 🚀 环境配置与运行

本项目环境配置要求与 [LeanGeo](https://github.com/project-numina/LeanGeo) 保持一致：

### 1. 初始化项目
在 Linux 终端执行以下指令：

```bash
# 克隆本项目
git clone [https://github.com/HLC040208/imo-geometry-lean4.git](https://github.com/HLC040208/imo-geometry-lean4.git)
cd imo-geometry-lean4

# 获取 Lean 4 依赖包与 Mathlib 预编译缓存（推荐）
lake exe cache get
lake build
```

### 2. 验证证明成果
你可以对 `IMO_00+` 目录下的任意题目进行内核验证。例如验证 2003 年第 4 题：

```bash
lake env lean IMO_00+/imo_2003_p4.lean
```
*注：若输出显示 `Goals accomplished 🎉` 且无红字报错，则表示证明通过。*

### 3. 使用 LeanScope 进行批量测试
运行以下指令对 `IMO_00+` 目录下的所有补全代码进行自动化性能采样：

```bash
python LeanScope/leanscope.py ./IMO_00+
```
执行完毕后，系统将生成 `perf_report.csv`，记录每道题目的 **Logical Heartbeats** 和 **Wall Time**。

---

## 📊 性能数据预览 (Sample)

通过 LeanScope 采集到的部分 IMO 题目证明开销：

| 题目编号 | 逻辑心跳 (Heartbeats) | 状态 | 耗时 (s) |
| :--- | :--- | :--- | :--- |
| IMO_2003_P4 | 45,210 | Success | 1.15 |
| IMO_2024_P3 | 132,400 | Success | 3.42 |

---

## 🤝 致谢与参考

- **LeanGeo**: 感谢 [Project Numina](https://github.com/project-numina) 团队提供的几何形式化框架，本项目的所有工作均在该框架定义的几何原语基础上完成。
- **Mathlib**: 感谢 Lean 社区提供的强大数学库支持。

---

## ⚖️ 开源协议

本项目采用 [MIT License](LICENSE) 开源。
