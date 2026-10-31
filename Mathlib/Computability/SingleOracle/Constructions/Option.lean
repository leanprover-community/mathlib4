/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Constructions.Primitive

/-!
# Construction of basic primitive recursive functions on option types

This file defines basic primitive recursive codes for basic functions on option types.

In docstrings, `[c]` denotes the function computed by the code `c`, and `[c](x)` its value at `x`.

-/

@[expose] public section

open Nat Denumerable Encodable List
section isSome
namespace Oracle.Single.Code
/-- This code defines the function `fun o ↦ b'2n (n2o o).isSome`. -/
def cIsSome := cSg'
@[cp] theorem cIsSome_prim : IsPrim cIsSome := by unfold cIsSome; apply_cp
@[simp, evp_simps] theorem cIsSome_evp {O : ℕ → ℕ} :
    evalp O cIsSome = fun o => b'2n <| (n2o o).isSome := by
  funext x; cases x <;> simp [cIsSome, b'2n, n2o]
@[simp, ev_simps] theorem cIsSome_ev {O : ℕ → ℕ} :
    eval O cIsSome = fun o => b'2n <| (n2o o).isSome := by
  rw [← evalp_eq_eval cIsSome_prim]; simp only [cIsSome_evp];
end Oracle.Single.Code
end isSome

section opt_iget
namespace Oracle.Single.Code
/-- This code defines the function `fun o ↦ (n2o o).getD 0`. -/
def cOptIget := cPred
@[cp] theorem cOptIget_prim : IsPrim cOptIget := by unfold cOptIget; apply_cp
@[simp, evp_simps] theorem cOptIget_evp {O : ℕ → ℕ} {o} :
    evalp O cOptIget o = Option.getD (n2o o) 0 := by
  simp [cOptIget]
  by_cases ho : o=0
  · simp [ho];
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho) with ⟨k,hk⟩
    simp [←hk]
@[simp, evp_simps] theorem iget_evp_2 {o} (h : o ≠ 0) : Option.getD (n2o o) 0 = o-1 :=  by
  rw [Eq.symm (succ_pred_eq_of_ne_zero h)]
  exact rfl

@[simp, ev_simps] theorem cOptIget_ev {O o} : eval O cOptIget o = Option.getD (n2o o) 0 := by
  simp [← evalp_eq_eval cOptIget_prim]
end Oracle.Single.Code
end opt_iget
section opt_getD
namespace Oracle.Single.Code
/-- This code defines the function `fun ⟪o, d⟫ ↦ (n2o o).getD d`. -/
def cOptGetD := cIfz.comp₃ left right (cOptIget.comp left)
@[cp] theorem cOptGetD_prim : IsPrim cOptGetD := by unfold cOptGetD; apply_cp
@[simp, evp_simps] theorem cOptGetD_evp {O : ℕ → ℕ} {o d} :
    evalp O cOptGetD (Nat.pair o d) = (n2o o).getD d := by
  simp [cOptGetD]
  by_cases ho : o=0
  · simp [ho];
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho) with ⟨k,hk⟩
    simp [←hk]
@[simp, ev_simps] theorem cOptGetD_ev {O : ℕ → ℕ} {o d} :
    eval O cOptGetD (Nat.pair o d) = (n2o o).getD d := by
  simp [← evalp_eq_eval cOptGetD_prim]
end Oracle.Single.Code
end opt_getD

section opt_none
namespace Oracle.Single.Code
/-- This code defines the function `fun _ ↦ o2n none`. -/
def cOptNone := cConst 0
@[cp] theorem cOptNone_prim : IsPrim cOptNone := by
  unfold cOptNone; apply_cp
@[simp, evp_simps] theorem cOptNone_evp {O : ℕ → ℕ} {o} :
    evalp O cOptNone o = o2n Option.none := by
  simp [cOptNone]
@[simp, ev_simps] theorem cOptNone_ev {O : ℕ → ℕ} {o} :
    Part.map n2o (eval O cOptNone o) = (Option.none : Option ℕ) := by
  simp [← evalp_eq_eval cOptNone_prim]
end Oracle.Single.Code
end opt_none

private lemma isSome_of_n2o {i} (h : i ≠ 0) : (n2o i).isSome := by
  rewrite [(succ_pred_eq_of_ne_zero h).symm]; rfl
section opt_bind
namespace Oracle.Single.Code
/-- Given codes `cf`, `cg`, this code defines the function
`fun x ↦ o2n ((n2o [cf](x)).bind fun t ↦ n2o [cg](⟪x, t⟫))`. -/
def cOptBind (cf cg : Code) :=  cIfz.comp₃ cf zero (cg.comp₂ cId (cOptIget.comp cf))
@[cp] theorem cOptBind_prim {cf cg : Code} (hcf : IsPrim cf) (hcg : IsPrim cg) :
  IsPrim (cOptBind cf cg) := by unfold cOptBind; apply_cp
@[simp, evp_simps] theorem cOptBind_evp {O : ℕ → ℕ} {cf cg : Code} {x} :
    evalp O (cOptBind cf cg) x =
    o2n do
      let t ← n2o (evalp O cf x)
      let r ← n2o (evalp O cg (Nat.pair x t))
      return r := by
  simp only [cOptBind, evp_simps]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp only [ne_eq, h, not_false_eq_true, iget_evp_2, ↓reduceIte,
      Option.bind_eq_bind]
    simp only [Option.isSome.bind <| isSome_of_n2o h, encode_ofNat]
    congr
    have goal {o h} : o - 1 = (n2o o).get h := by
      have (h : (n2o o).isSome) : o ≠ 0 := by
        contrapose h
        simp [h]
      simp (config := {singlePass := true}) [(succ_pred_eq_of_ne_zero (this h)).symm]
    exact goal
end Oracle.Single.Code
end opt_bind

section opt_bind'
namespace Oracle.Single.Code
/-- Given codes `cf`, `cg`, this code defines the function
`fun x ↦ o2n ((n2o [cf](x)).bind fun _ ↦ n2o [cg](x))`. -/
def cOptBind' (cf cg : Code) :=  cIfz.comp₃ cf zero cg
@[cp] theorem cOptBind'_prim {cf cg : Code} (hcf : IsPrim cf) (hcg : IsPrim cg) :
  IsPrim (cOptBind' cf cg) := by unfold cOptBind'; apply_cp
@[simp, evp_simps] theorem cOptBind'_evp {O : ℕ → ℕ} {cf cg : Code} {x} :
    evalp O (cOptBind' cf cg) x =
    o2n do
      let _ ← n2o (evalp O cf x)
      let r ← n2o (evalp O cg x)
      return r := by
  simp only [cOptBind', evp_simps]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp [h]
    simp [Option.isSome.bind <| isSome_of_n2o h]
end Oracle.Single.Code
end opt_bind'

section part_bind
namespace Oracle.Single.Code
/-- Given codes `cf`, `cg`, this code defines the (partial) function
`fun x ↦ [cf](x) >>= fun t ↦ [cg](⟪x, t⟫)`. -/
def cPartBind (cf cg : Code) := cg.comp₂ cId cf
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem cPartBind_ev {O : ℕ → ℕ} {cf cg : Code} {x} :
  eval O (cPartBind cf cg) x =
  do
    let t ← eval O cf x
    let r ← eval O cg (Nat.pair x t)
    return r := by
 simp [cPartBind, Seq.seq]

end Oracle.Single.Code
end part_bind
