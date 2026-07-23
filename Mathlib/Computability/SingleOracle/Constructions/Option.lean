/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Constructions.Primitive
-- import Mathlib.Computability.SingleOracle.Helper.Partial

/-!
# Construction of basic primitive recursive functions on option types

This file defines basic primitive recursive codes for basic functions on option types.

-/

open Nat Denumerable Encodable List
section isSome
namespace Oracle.Single.Code
def c_isSome := c_sg'
@[cp] theorem c_isSome_prim : code_prim c_isSome := by unfold c_isSome; apply_cp
@[simp, evp_simps] theorem c_isSome_evp {O : ℕ → ℕ} :
    evalp O c_isSome = fun o => b'2n <| (n2o o).isSome := by
  funext x; cases x <;> simp [c_isSome, b'2n, n2o]
@[simp, ev_simps] theorem c_isSome_ev {O : ℕ → ℕ} :
    eval O c_isSome = fun o => b'2n <| (n2o o).isSome := by
  rw [← evalp_eq_eval c_isSome_prim]; simp only [c_isSome_evp];
end Oracle.Single.Code
end isSome

section opt_iget
namespace Oracle.Single.Code
def c_opt_iget := c_pred
@[cp] theorem c_opt_iget_prim : code_prim c_opt_iget := by unfold c_opt_iget; apply_cp
@[simp, evp_simps] theorem c_opt_iget_evp {O : ℕ → ℕ} {o} :
    evalp O c_opt_iget o = Option.getD (n2o o) 0 := by
  simp [c_opt_iget]
  by_cases ho : o=0
  · simp [ho];
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho) with ⟨k,hk⟩
    simp [←hk]
@[simp, evp_simps] theorem iget_evp_2 {o} (h : o ≠ 0) : Option.getD (n2o o) 0 = o-1 :=  by
  rw [Eq.symm (succ_pred_eq_of_ne_zero h)]
  exact rfl

@[simp, ev_simps] theorem c_opt_iget_ev {O o} : eval O c_opt_iget o = Option.getD (n2o o) 0 := by
  simp [← evalp_eq_eval c_opt_iget_prim]
end Oracle.Single.Code
end opt_iget
section opt_getD
namespace Oracle.Single.Code
def c_opt_getD := c_ifz.comp₃ left right (c_opt_iget.comp left)
@[cp] theorem c_opt_getD_prim : code_prim c_opt_getD := by unfold c_opt_getD; apply_cp
@[simp, evp_simps] theorem c_opt_getD_evp {O : ℕ → ℕ} {o d} :
    evalp O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by
  simp [c_opt_getD]
  by_cases ho : o=0
  · simp [ho];
  · rcases exists_add_one_eq.mpr (one_le_iff_ne_zero.mpr ho) with ⟨k,hk⟩
    simp [←hk]
@[simp, ev_simps] theorem c_opt_getD_ev {O : ℕ → ℕ} {o d} :
    eval O c_opt_getD (Nat.pair o d) = (n2o o).getD d := by
  simp [← evalp_eq_eval c_opt_getD_prim]
end Oracle.Single.Code
end opt_getD

section opt_none
namespace Oracle.Single.Code
def c_opt_none := c_const 0
@[cp] theorem c_opt_none_prim : code_prim c_opt_none := by
  unfold c_opt_none; apply_cp
@[simp, evp_simps] theorem c_opt_none_evp {O : ℕ → ℕ} {o} :
    evalp O c_opt_none o = o2n Option.none := by
  simp [c_opt_none]
@[simp, ev_simps] theorem c_opt_none_ev {O : ℕ → ℕ} {o} :
    n2o <$> (eval O c_opt_none o) = (Option.none : Option ℕ) := by
  simp [← evalp_eq_eval c_opt_none_prim]
end Oracle.Single.Code
end opt_none

lemma isSome_of_n2o {i} (h : i ≠ 0) : (n2o i).isSome := by
  rewrite [(succ_pred_eq_of_ne_zero h).symm]; rfl
section opt_bind
namespace Oracle.Single.Code
def c_opt_bind (cf cg : Code) :=  c_ifz.comp₃ cf zero (cg.comp₂ c_id (c_opt_iget.comp cf))
@[cp] theorem c_opt_bind_prim {cf cg : Code} (hcf : code_prim cf) (hcg : code_prim cg) :
  code_prim (c_opt_bind cf cg) := by unfold c_opt_bind; apply_cp
@[simp, evp_simps] theorem c_opt_bind_evp {O : ℕ → ℕ} {cf cg : Code} {x} :
    evalp O (c_opt_bind cf cg) x =
    o2n do
      let t ← n2o (evalp O cf x)
      let r ← n2o (evalp O cg (Nat.pair x t))
      return r := by
  simp only [c_opt_bind, evp_simps]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp only [ne_eq, h, not_false_eq_true, iget_evp_2, ↓reduceIte,
      Option.pure_def, Option.bind_eq_bind, Option.bind_fun_some]
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
def c_opt_bind' (cf cg : Code) :=  c_ifz.comp₃ cf zero cg
@[cp] theorem c_opt_bind'_prim {cf cg : Code} (hcf : code_prim cf) (hcg : code_prim cg) :
  code_prim (c_opt_bind' cf cg) := by unfold c_opt_bind'; apply_cp
@[simp, evp_simps] theorem c_opt_bind'_evp {O : ℕ → ℕ} {cf cg : Code} {x} :
    evalp O (c_opt_bind' cf cg) x =
    o2n do
      let _ ← n2o (evalp O cf x)
      let r ← n2o (evalp O cg x)
      return r := by
  simp only [c_opt_bind', evp_simps]
  cases Classical.em (evalp O cf x = 0) with
  | inl h => simp [h]
  | inr h =>
    simp [h]
    simp [Option.isSome.bind <| isSome_of_n2o h]
end Oracle.Single.Code
end opt_bind'

section part_bind
namespace Oracle.Single.Code
def c_part_bind (cf cg : Code) := cg.comp₂ c_id cf
@[simp, ev_simps] theorem c_part_bind_ev {O : ℕ → ℕ} {cf cg : Code} {x} :
  eval O (c_part_bind cf cg) x =
  do
    let t ← eval O cf x
    let r ← eval O cg (Nat.pair x t)
    return r := by
 simp [c_part_bind, Seq.seq]

end Oracle.Single.Code
end part_bind
