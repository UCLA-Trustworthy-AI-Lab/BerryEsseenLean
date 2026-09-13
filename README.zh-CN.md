# Berry–Esseen 界的 Lean 形式化

[English](README.md)

本工程对应 Hengzhi He、Guang Cheng 的论文 [The Berry–Esseen Bound is Sharp for All Sufficiently Large Sample Sizes](https://arxiv.org/abs/2609.06358)。核对所用的原稿完整保存在 [reference/aop-sample.tex](reference/aop-sample.tex)。

在代码明确列出的外部经典结果成立的前提下，Lean 证明了：存在对所有标准化实分布统一的样本量阈值，使 Berry–Esseen 界中的 Esseen 常数成立；同时给出原稿的显式阈值和常数最优性结论。

## 从这里开始

| 内容 | 入口 |
|---|---|
| 主要定理、显式阈值、最优性 | [StrictResults.lean](BerryEsseen/StrictResults.lean) |
| 概率分布和待证命题的实际定义 | [Statement.lean](BerryEsseen/Statement.lean) |
| 外部前提、文献与具体页码 | [ASSUMPTIONS.md](docs/ASSUMPTIONS.md) |
| 原稿的定理引理与 Lean 对应表 | [STATEMENT_MAP.md](docs/STATEMENT_MAP.md) |
| 机器检查的范围与复现方法 | [VERIFICATION.md](docs/VERIFICATION.md) |
| 本次发布包的检查记录 | [verification/README.md](verification/README.md) |
| 上传 GitHub 的操作步骤 | [UPLOAD.zh-CN.md](docs/UPLOAD.zh-CN.md) |

## 复现

需要安装 [elan](https://github.com/leanprover/elan)、Git 和 Python 3.10 或更高版本。本次验证和 CI 使用 Linux；Windows 用户可在 WSL 中执行检查。在仓库根目录执行：

```bash
lake exe cache get
python3 scripts/verify.py --jobs 3
```

`lean-toolchain` 固定为 Lean 4.28.0；`lakefile.toml` 和 `lake-manifest.json` 固定 mathlib 及其依赖。首次运行需要联网下载工具链和依赖，内存较少时可使用 `--jobs 1`。

验证脚本重新编译全部 361 个数学模块，并运行端点类型、公理、原稿陈述覆盖、原证明路径以及 bounded-extremizers 完整合取结论等检查。结果写入 `validation/`。普通 `lake build` 可用于日常构建；完整审计使用上面的 Python 命令。

## 如何理解验证结论

外部结果通过显式定理参数传入。应同时阅读这些参数的数学陈述和文献对应表；仅看到公理列表中没有 `sorryAx`，不能据此认定外部结果也已在本工程内部证明。

Villani 的 Wasserstein 两项以 **2008 年 6 月 13 日作者书稿**为当前核对来源；Schulz 的 Bernoulli 结果来自公开博士论文。其他外部输入的出版类型与公式定位也分别列明。

Lean 检查形式化陈述及证明项。原稿文字与形式化陈述、证明路线的对应属于另行审阅的部分，机器检查不自动读取或裁定自然语言证明的忠实性。

本包包含可提交的源码、文档和自动检查配置。论文 TeX 保留核对时的原始字节；两处 Shevtsova 引用页码的修正另见 [勘误](reference/errata-current-recheck.md)。
