---
name: mathlib-pr-selective-port
description: 从某个 mathlib PR 中只抽取指定文件的改动，迁移到新的 branch，再向 `leanprover-community/mathlib4` 开 PR。
---

## 默认原则

- 不要污染用户当前工作区, 新建 `git worktree`
- 不要回滚或覆盖用户已有改动
- 不跑 `lake build`、不做编译检查
- 不要依赖本地是否配置了 `upstream` remote；直接从 GitHub URL 抓取 `master` 和 PR head
- 如果目标 branch 已存在于本地或远程，任务终止, 询问用户.
- 清理建立的 `worktree`

## 需要确认的输入

1. 源 PR 编号或 URL
2. 要抽取的文件列表

- base 仓库是 `leanprover-community/mathlib4`
- base branch 是 `master`
- push 到当前仓库的 `origin`
- 只做 patch 迁移，不做编译

## 推荐流程

1. 检查当前仓库状态

   - 看 `git status --short --branch`
   - 看 `git remote -v`

2. 确定 branch 命名,
   - 假如这个领域是 `MeasureTheory` , 则命名为 `M_<num>` , 其中 <num> 代表一个正整数使得 branch 名称不和存在的 branch 重复, 命名比如 `M_25`
   - 假如这个领域是 `NumberTheory` , 则命名为 `N_<num>` , 其中 <num> 代表一个正整数, 命名比如 `N_37`
   - 假如这个领域是 `Analysis` , 则命名为 `A_<num>` , 其中 <num> 代表一个正整数, 命名比如 `A_11`


3. 读取用户上下文

   - 整理出目标文件列表
   - 整理出目标 branch 名
   - 记录 PR 标题格式要求

4. 抓取最新 `master` 和源 PR head

   ```bash
   git fetch https://github.com/leanprover-community/mathlib4 \
     refs/heads/master:refs/remotes/temp_upstream/master

   git fetch https://github.com/leanprover-community/mathlib4 \
     pull/<PR号>/head:refs/remotes/temp_prs/<PR号>-head
   ```

   不要依赖本地旧的 `upstream/master`，它可能过期。

5. 计算 patch 基线

   ```bash
   BASE=$(git merge-base temp_upstream/master temp_prs/<PR号>-head)
   ```

   然后先检查指定文件在该 PR 中是否真的有改动：

   ```bash
   git diff --stat "$BASE"..temp_prs/<PR号>-head -- <文件1> <文件2> ...
   ```

6. 建干净 worktree 和新 branch

   推荐把 worktree 建在仓库同级目录，避免碰当前工作区：

   ```bash
   git worktree add -b <新branch> <同级目录下的新路径> temp_upstream/master
   ```

7. 只应用指定文件的 patch

   先做 `--check`：

   ```bash
   git diff "$BASE"..temp_prs/<PR号>-head -- <文件1> <文件2> ... \
     | git -C <worktree路径> apply --check -
   ```

   如果通过，再正式应用：

   ```bash
   git diff "$BASE"..temp_prs/<PR号>-head -- <文件1> <文件2> ... \
     | git -C <worktree路径> apply -
   ```

   应用后检查：

   ```bash
   git -C <worktree路径> status --short --branch
   git -C <worktree路径> diff --stat
   git -C <worktree路径> diff -- <文件1> <文件2> ...
   ```

8. 失败时的处理

   - 如果 `git apply --check` 失败，先确认是不是 `master` 漂移导致的 context mismatch
   - 可以尝试重新抓最新 `master`
   - 如果仍失败，就在 worktree 里手工只迁移目标文件的改动
   - 禁止直接整条 `cherry-pick` 后再大面积回退无关文件，除非非常确定不会污染结果

9. 提交 branch

   ```bash
   git -C <worktree路径> add <文件1> <文件2> ...
   git -C <worktree路径> commit -m "<简洁提交信息>"
   git -C <worktree路径> push -u origin <新branch>
   ```

10. 开 PR

   优先用 GitHub MCP：

   - `base`: `master`
   - `head`: `<你的GitHub用户名>:<新branch>`
   - `owner/repo`: `leanprover-community/mathlib4`

   PR title 示例

   ```
   refactor(Analysis): golf `Mathlib/Analysis/Analytic/IteratedFDeriv`
   ```

   PR message 示例
   ```
   - refactors `Padics/Hensel` by extracting the duplicated root-uniqueness argument into a shared private lemma `a_soln_is_unique`
   - rewrites `soln_unique` to first transport the distance bound to `soln` via `soln_deriv_norm`, then close the proof by applying that shared uniqueness lemma, instead of redoing the full binomial-expansion argument inline
   - refactors `NumberField/Norm` by moving `isUnit_norm_of_isGalois` to sit after `dvd_norm` and shortening its proof to a direct application of `dvd_norm` together with `isUnit_of_dvd_unit`

   Extracted from #37968

   [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
   ```

   严格模仿示例, 不要加如 `test`, `This is a patch-only selective port prepared without running a build.` 类似的额外信息.
   总结尽可能简洁精炼, 不要啰嗦! 重点写清楚这个文件修改了什么.

10. 调用 $lean-pr-profiler-compare 这个 skill, 分析性能变化并发送到评论区. 并且把 PR 的 tag 加上 `LLM-generated` , `codex` 的标签

11. 到 Extract 的 PR 评论区, 把新开的 PR 编号添加到 PR_message 的 dependcy 里, 选择 update PR message 而不是发一条新的评论.

13. 收尾

   - 把新 PR 链接回报给用户
   - 说明分支名
   - 清理新建的 worktree


