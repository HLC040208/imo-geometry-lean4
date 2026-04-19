# IMO Geometry Full Completion (IMO_00+) 
### Based on LeanGeo Framework

[![Lean4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Framework](https://img.shields.io/badge/Framework-LeanGeo-orange.svg)](https://github.com/project-numina/LeanGeo)

本项目是对 [Project-Numina/LeanGeo](https://github.com/project-numina/LeanGeo) 环境下 `IMO_00+` 基准目录的深度补全工程。通过形式化建模与严谨证明，本项目完整实现了该目录下 **2000 年至 2025 年** 所有国际数学奥林匹克（IMO）几何题的代码证明。

## 🎯 项目核心贡献

- **全量代码补全**：针对 `IMO_00+` 目录进行了地毯式开发，确保每一道 IMO 几何题均有对应的 Lean 4 形式化证明。
- **环境完全兼容**：严格遵循 `LeanGeo` 框架的定义规范与原语，所有证明均可在 LeanGeo 官方配置的环境中直接编译通过。
- **性能诊断支撑**：引入自研工具 `LeanScope`，对全量补全后的题目进行了逻辑心跳（Heartbeats）采样，建立了竞赛级几何证明的性能基准数据。

## 📂 目录结构

```text
.
├── IMO_00+/             # 核心成果：包含 2000-2025 年全部 IMO 几何证明文件
├── LeanScope/           # 性能测评框架（探测层、解析层、报告层）
│   └── leanscope.py     # 自动化性能监测脚本
├── lakefile.lean        # 项目配置（引入 LeanGeo 与 Mathlib 依赖）
├── lean-toolchain       # Lean 4 工具链版本定义
└── README.md            # 项目说明文档

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
