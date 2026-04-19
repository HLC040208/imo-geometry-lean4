LeanGeo-Bench: IMO_00+ Full Completion基于 LeanGeo 框架的 IMO 几何题库全量形式化实现本项目专注于对 Project-Numina/LeanGeo 环境下 IMO_00+ 目录的深度补全。本项目通过形式化建模与严谨证明，完成了该目录下所有国际数学奥林匹克（IMO）几何题的代码实现。🎯 项目核心定位在形式化定理证明领域，高质量的竞赛级题库是评估自动推理能力的关键。本项目针对 IMO_00+ 这一核心题集，完成了以下工作：全量代码补全：覆盖了目录下从 2000 年至 2025 年的所有几何命题，确保每个文件均能通过 Lean 4 内核验证。框架对标：严格遵循 LeanGeo 的几何原语与定义规范，确保证明过程的代数严谨性。效能测评：利用自研的 LeanScope 工具对 IMO_00+ 全目录进行了性能采样，记录了每道题目的逻辑心跳开销。📂 目录结构Plaintext.
├── IMO_00+/             # 核心文件夹：包含 2000-2025 年全部 IMO 几何证明
├── LeanScope/           # 自研性能测评工具脚本
├── lakefile.lean        # 项目配置文件（依赖 LeanGeo）
└── lean-toolchain       # 环境版本定义
🚀 运行与验证由于本项目是 LeanGeo 环境的直接扩展，请确保你的环境中已配置好相关的依赖：环境初始化：Bashlake exe cache get
lake build
验证证明：使用 Lean 4 编译器验证 IMO_00+ 目录下的指定题目：Bashlake env lean IMO_00+/imo_2003_p4.lean
运行性能分析：使用 LeanScope 对补全后的 IMO_00+ 文件夹进行全量扫描：Bashpython LeanScope/leanscope.py ./IMO_00+
📊 补全成果摘要通过对 IMO_00+ 的全量补齐，本项目构建了一个包含 26 年 竞赛真题的高质量数据集，平均每道题目的逻辑心跳（Heartbeats）分布在 $4 \times 10^4$ 至 $2 \times 10^5$ 之间，展示了极高的逻辑复杂度。🤝 参考与致谢LeanGeo-Bench: 本项目直接针对该 Benchmark 进行补全。Framework: 感谢 Project Numina 提供的 LeanGeo 形式化底座。
