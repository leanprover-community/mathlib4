import Mathlib.Tactic.MfldSetTac.Attr
import Mathlib.Tactic.Ext
import Mathlib.Init.Logic

open Lean Meta Elab Tactic

@[ext]
theorem Set.ext {α : Type u} {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) :
a = b := sorry

elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← getMVarDecl g).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| apply Set.ext;  intro my_y; constructor <;> { intro h_my_y;
                            try { simp only [*, mfld_simps] at h_my_y
                                  simp only [*, mfld_simps] } }))
  | (``Subset.subset, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| intro my_y h_my_y;
                            try { simp only [*, mfld_simps] at h_my_y
                                  simp only [*, mfld_simps] }))
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

--attribute [mfld_simps] mul_one
--
--example (x : Nat) : x * 1 = x := by
--  simp only [mfld_simps]

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply
