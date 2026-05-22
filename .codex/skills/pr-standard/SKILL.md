---
name: pr-standard
description: 输入一些 PR 编号, 将 PR 整理的符合 Mathlib 规范
---

1. 用 gihub-mcp 查看对应 PR 的 branch_name, 随后在本地开一个 worktree 切换到对应 branch

2. 在这个 branch 上 lake exe cache get && lake build

3. 用 github-mcp 读取对应 PR 的file changes, 接下来的修改只允许看我修改的定理, 不允许修改其他定理或者其他我文件.

4. 检查有没有地方用 `=>` , 尝试修改为 `↦`, 检查有的地方是否有多于的 namespace 可以去掉, 你只能去掉 namespace, 不能拿自己 open namespace, 确保去掉后可以通过编译.

  例子
  ```
  open Valuation
  ....
  exact Valuation.restrict_def
  ```
  精简为
  ```
  open Valuation
  ....
  exact restrict_def
  ```

5. 检查有的地方的显式传参 `thm (p := arg)` 是否可以去掉为 `thm` 或者变成正常传参 `thm arg`, 确保修改后能编译

  例子:
  ```
  ContinuousAt.comp_of_eq (g := fun p : EReal × EReal ↦ p.1 * p.2) (f := fun x ↦ (c, x))
    (y := (c, x))
    (EReal.continuousAt_mul (p := (c, x)) (Or.inl hc) (Or.inl hc) (Or.inr hx0) (Or.inr hx0))
    (continuousAt_const.prodMk continuousAt_id) rfl
  ```
  精简为
  ```
  ContinuousAt.comp_of_eq (Or.inl hc) (Or.inl hc) (Or.inr hx0) (Or.inr hx0))
    (continuousAt_const.prodMk continuousAt_id) rfl
  ```

6. 检查有没有 `rw` , `simp` 或者 `simp_rw` 链, 可以尝试把相邻的 `rw` 和 `simp` 合并到一起, 确保通过编译.

  例子 :
  ```
  - simp only [equiv_symm_apply, Units.val_mk0, Set.mem_setOf_eq, lt_div_iff₀ hs0'] at hx
  - rw [← map_mul, restrict_lt_iff] at hx
  + simp only [equiv_symm_apply, Units.val_mk0, Set.mem_setOf_eq, lt_div_iff₀ hs0', ← map_mul,
  +   restrict_lt_iff] at hx
  ```

7. 尝试把定理结尾处的 `simp only` 变成 `simp`, 并且尝试减少一些 args, 希望用最少的 args 通过编译. 不用对中间的 `simp only` 进行这样的操作, 因为 Linter 会要求中间的地方都用 `simp only` 展开确保稳定性.

  例子 :
  ```
  - simp only [Valued.v.norm_def, RankOne.hom_eq_embedding, Valuation.restrict_def]
  + simp [Valuation.restrict_def]
  ```
  如果一个 `simpa` 可以直接改成 `exact`, 先用 `exact`. 如果不行, 优先尝试 `simp [...]`, 其次 `simpa using ...`, 最后才用 `simpa only [...] using ...`.


8. 为了可读性, 不要把 `have : statement := foo` 压成 `have := foo`.

   而且如果 `simpa [...] using something` 后面的 `something` 的包含了 tactic, 则为了可读性, 应该改为

   ```
   have : state := by something
   simpa [...]
   ```

   例如

   ```
   - simpa using by lia
   + simp
   + lia
   ```

   ```
   - simpa [...] using by foo (by simp) boo
   + have : statement := foo (by simp) boo
   + simpa
   ```

9. 如果当前证明已经是清晰的 `calc` 链, 不要为了压成一条 `simpa` 而改写整体结构; 优先保留 `calc`, 只精简链上的局部步骤.

10. 确保修改后的内容可以通过编译, 且没有 warning, 如果有warning ,则需要按照linter要求修改, 而不能set_option 把 linter 关掉当鸵鸟.

10. 如果用户没有明确要求 commit & push, 禁止 commit & push
