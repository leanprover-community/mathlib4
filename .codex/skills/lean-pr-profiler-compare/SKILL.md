---
name: lean-pr-profiler-compare
description: 对 mathlib 的 GitHub PR 中被修改的定理做 before/after `trace.profiler` 性能对比。
---

# Lean-pr-profiler-compare

0. 给定 PR 编号

1. 确认 PR 的 head branch 和 base branch。
2. 将本地仓库切换到 PR 对应 branch。
3. 对每个被修改的声明分别比较：
   - PR head branch 上的版本，也就是 `after`
   - PR 相对 base 的 merge-base 上的版本, 也就是 `before`
4. 完整地恢复用户原本的本地状态。
5. 输出报告, 把英文总结发给用户
5. 如果用户明确表示, 就把英文总结发到 PR 讨论区. 如果用户没有提到"发评论"相关的指令, 则不要在 Github 上发消息.

**工具**

- 优先使用 GitHub MCP 读取 PR 元数据、改动文件。

**流程**

1. 确认 PR 上下文

    - 用 GitHub MCP 读取 PR。
    - 记录：
      - PR head ref
      - PR head SHA
      - PR base ref
      - 改动文件列表
      - 每个文件改动了哪些 theorem / lemma / instance / def , 确定声明的位置. 纯空白、纯注释改动可以忽略。
    - 在切到 PR branch 之后，用本地 git 计算 merge-base：
      - `git merge-base <head-branch> <base-remote>/<base-branch>`
    - 如果 PR 里给出的 base SHA 恰好就是实际 merge-base，也可以直接用。

2. 用`git worktree` 创建 after 和 before 相应的 PR branch 工作区

3. 在每个 worktree 上分别执行 `lake -R exe cache get ` 获取编译源代码.

4. 在 `after` 和 `before` 上找出实际被修改的声明, 然后在目标声明前面加一行  `set_option trace.profiler true in` , 禁止自作主张用其他方式测量.

5. 如果有多个文件, 请在 worktree 上 `lake env lean <file>` 逐一测试, 等一个测试完成后恢复原状, 再测试下一个. 禁止并行测试, 这可能导致一些编译问题. 每当一个文件测试完成, 将结果记录到 `/tmp` 下的一个 markdown 文件中, 同时告诉用户结果. 禁止用 `lean-lsp-mcp` 因为这是原仓库的 `lean` 编译, 不一定得到希望的结果.

6. 写英文总结

    ```markdown
    I ran a profiler comparison for the changed declarations in this PR.

    Results (seconds):
    - `<decl1>`: `<before> -> <after>` (`<percent>%`)
    - `<decl2>`: `<before> -> <after>` (`<percent>%`)

    Overall:
    - brief conclusion
    ```

    - 如果用户要求把结果发到 PR 下方, 评论尽量简洁、具体, 同样使用上述模板.

    - 其中必须包含 : 定理名称, before 时间, after 时间, 相对变化百分比

    - 总结时保持直接：哪些改动提速了, 哪些改动退化了

    - 如果某个声明在一侧无法成功 elaboration，不要为了凑数硬比较；把它列到 `Not comparable`，并写明失败原因.

7. 删除新建的 worktree, 恢复现场.
