import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Init.SetNotation
import Mathlib.Init.Set
import Mathlib.Tactic.Ext

open Lean Meta Elab Tactic

initialize mfldSetTacExt : SimpExtension ←
  registerSimpAttr `mfld_simps (extName := `Tactic.MfldSetTac.mfldSetTacExt) $
    "The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.
The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.
"

elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← getMVarDecl g).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[ty, e₁, e₂]) =>
    evalTactic (← `(tactic| ext my_y; split; intro h_my_y;
                            try { sorry }))
  | (``Subset.subset, #[ty, inst, e₁, e₂]) =>
    evalTactic (← `(tactic| intro my_y h_my_y;
                            try { sorry }))
  | _ => throwError "goal should be an equality or an inclusion"

  --match goal with
  --| `(%%e₁ = %%e₂) :=
  --    `[ext my_y,
  --      split;
  --      { assume h_my_y,
  --        try { simp only [*, -h_my_y] with mfld_simps at h_my_y },
  --        simp only [*] with mfld_simps }]
  --| `(%%e₁ ⊆ %%e₂) :=
  --    `[assume my_y h_my_y,
  --      try { simp only [*, -h_my_y] with mfld_simps at h_my_y },
  --      simp only [*] with mfld_simps]
  --| _ := tactic.fail "goal should be an equality or an inclusion"
  --end

example : 2 + 2 = 4 := by
  simp with mfld_simps
