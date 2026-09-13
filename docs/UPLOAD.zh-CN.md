# 上传到 GitHub

解压发布包后，`BerryEsseenLean/` 是仓库根目录：这一层应直接包含 `README.md`、`lakefile.toml`、`lean-toolchain`、`BerryEsseen/` 和 `.github/`。

## 推荐：使用 Git 推送

1. 在 GitHub 创建一个空仓库，例如 `BerryEsseenLean`，先不要让 GitHub 自动生成 README、许可证或 `.gitignore`。
2. 打开终端，进入解压后的 `BerryEsseenLean` 目录。
3. 执行下面的命令，并把 `YOUR_ACCOUNT` 和仓库名改为你的实际地址：

```bash
git init -b main
git add .
git commit -m "Add Berry-Esseen Lean formalization"
git remote add origin https://github.com/YOUR_ACCOUNT/BerryEsseenLean.git
git push -u origin main
```

这些命令适用于新建空仓库。若要放进已有仓库，先克隆该仓库，再复制本包文件并按已有分支流程提交。

`.gitignore` 已排除 `.lake/`、编译产物和本地运行日志。`.github/workflows/lean.yml` 会随 `git add .` 一同提交。不要只上传 ZIP 文件；GitHub 需要解压后的文件才能显示工程内容并运行工作流。

## 不使用命令行

可以用 [GitHub Desktop](https://desktop.github.com/) 将解压后的目录添加为本地仓库，再选择 Publish repository。包内有数百个源码文件，使用 Git 或 Desktop 更便于一次保留完整目录和 `.github` 配置。

## 上传后

在仓库的 Actions 页面查看 **Lean verification**。工作流会安装固定版本的 Lean，下载 mathlib 缓存，重新编译数学模块并运行完整审计。每次运行的日志作为工作流附件保留；本包附带的本地验证记录见 [verification/README.md](../verification/README.md)。

仓库描述可填写：

> Lean 4 formalization of the Berry–Esseen sharp-constant theorem, conditional on explicitly stated literature results.

本包没有替作者选定代码分发许可证。若希望授予他人使用、修改和分发代码的权利，可由权利人选择许可证，加入 `LICENSE`，并同步更新 `formalization.yaml` 的 `project.license`。论文作者信息已经保留在原稿与文献记录中。
