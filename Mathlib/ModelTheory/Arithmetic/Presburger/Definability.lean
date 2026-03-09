/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic
public import Mathlib.ModelTheory.Definability

import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Presburger definability and semilinear sets

This file formalizes the classical result that Presburger definable sets are the same as semilinear
sets. As an application of this result, we show that the graph of multiplication is not Presburger
definable.

## Main Results

- `presburger.definable_iff_isSemilinearSet`: a set is Presburger definable in `ℕ` if and only if it
  is semilinear.
- `presburger.definable₁_iff_ultimately_periodic`: in the 1-dimensional case, a set is Presburger
  arithmetic definable in `ℕ` if and only if it is ultimately periodic, i.e. periodic after some
  number `k`.
- `presburger.mul_not_definable`: the graph of multiplication is not Presburger definable in `ℕ`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger Formulas, and Languages*][
  ginsburg1966]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

public section

variable {α : Type*} {s : Set (α → ℕ)} {A : Set ℕ}

open Set FirstOrder Language

theorem IsLinearSet.definable [Finite α] (hs : IsLinearSet s) : A.Definable presburger s := by
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨v, t, rfl⟩
  refine ⟨Formula.iExs t (Formula.iInf fun i : α =>
    (Term.var (Sum.inl i)).equal
      (Term.varsToConstants
        ((v i : presburger.Term _) + presburger.sum Finset.univ fun x : t =>
          x.1 i • Term.var (Sum.inr (Sum.inr x))))), ?_⟩
  ext x
  simp only [mem_vadd_set, SetLike.mem_coe, AddSubmonoid.mem_closure_finset', Finset.univ_eq_attach,
    nsmul_eq_mul, vadd_eq_add, ↓existsAndEq, true_and, mem_setOf_eq, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var, Sum.elim_inl,
    Term.realize_varsToConstants, coe_con, presburger.realize_add, presburger.realize_natCast,
    Nat.cast_id, presburger.realize_sum, presburger.realize_nsmul, Sum.elim_inr, smul_eq_mul]
  congr! with a
  simp_rw [Eq.comm (b := x), fun x : t => mul_comm (a x : α → ℕ) x, funext_iff]
  congr! 1 with i
  simp

theorem IsSemilinearSet.definable [Finite α] (hs : IsSemilinearSet s) :
    A.Definable presburger s := by
  rw [isSemilinearSet_iff] at hs
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_setOf_eq] at this
  simp [this]

namespace FirstOrder.Language.presburger

set_option backward.isDefEq.respectTransparency false in
lemma term_realize_eq_add_dotProduct [Fintype α] (t : presburger[[A]].Term α) :
    ∃ (k : ℕ) (u : α → ℕ), ∀ (v : α → ℕ), t.realize v = k + u ⬝ᵥ v := by
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp [ih]
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl, add_dotProduct, add_left_comm, add_assoc, add_left_comm,
          ← add_assoc]
        simp [ih]
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInr, zero_dotProduct, add_zero]
        rfl
      | succ => nomatch f

variable [Finite α]

lemma isSemilinearSet_boundedFormula_realize {n} (φ : presburger[[A]].BoundedFormula α n) :
    IsSemilinearSet {v : α ⊕ Fin n → ℕ | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
  haveI := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct t₂ with ⟨k₂, u₂, ht₂⟩
    convert Nat.isSemilinearSet_setOf_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel f => nomatch f
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert (ih₂.compl.inter ih₁).compl using 1
    simp [setOf_inter_eq_sep, imp_iff_not_or, compl_setOf]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft ℕ ℕ e)] at ih
    convert ih.compl.proj.compl using 1
    simp_rw [compl_setOf, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_setOf, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]

lemma isSemilinearSet_formula_realize_semilinear (φ : presburger[[A]].Formula α) :
    IsSemilinearSet (setOf φ.Realize : Set (α → ℕ)) := by
  let e := Equiv.sumEmpty α (Fin 0)
  convert (isSemilinearSet_boundedFormula_realize φ).image (LinearMap.funLeft ℕ ℕ e.symm)
  ext x
  simp only [mem_setOf_eq, mem_image]
  rw [(e.arrowCongr (.refl ℕ)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

/-- A set is Presburger definable in `ℕ` if and only if it is semilinear. -/
theorem definable_iff_isSemilinearSet {s : Set (α → ℕ)} :
    A.Definable presburger s ↔ IsSemilinearSet s :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ isSemilinearSet_formula_realize_semilinear φ, IsSemilinearSet.definable⟩

/-- In the 1-dimensional case, a set is Presburger arithmetic definable in `ℕ` if and only if it
  is ultimately periodic, i.e. periodic after some number `k`. -/
theorem definable₁_iff_ultimately_periodic {s : Set ℕ} :
    A.Definable₁ presburger s ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ s ↔ x + p ∈ s := by
  rw [Definable₁, definable_iff_isSemilinearSet,
    ← isSemilinearSet_image_iff (LinearEquiv.funUnique (Fin 1) ℕ ℕ), ← preimage_setOf_eq]
  simp only [LinearEquiv.funUnique_apply, Function.eval, Fin.default_eq_zero, setOf_mem_eq]
  rw [image_preimage_eq s fun x => ⟨![x], rfl⟩, Nat.isSemilinearSet_iff_ultimately_periodic]

/-- The graph of multiplication is not Presburger definable in `ℕ`. -/
theorem mul_not_definable : ¬ A.Definable presburger {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : ℕ} := by
    rw [Definable₁]
    convert (hmul.preimage_comp (β := Fin 2) ![0, 1, 1]).image_comp ![0]
    ext
    simpa [funext_iff, Fin.exists_fin_succ_pi] using exists_congr fun _ => Eq.comm
  rw [definable₁_iff_ultimately_periodic] at hsqr
  rcases hsqr with ⟨k, p, hp, h⟩
  specialize h ((max k p) * (max k p)) ((Nat.le_mul_self _).trans' (le_max_left _ _))
  simp only [mem_setOf_eq, exists_apply_eq_apply, true_iff] at h
  rcases h with ⟨x, h₁⟩
  by_cases h₂ : x ≤ max k p
  · apply Nat.mul_self_le_mul_self at h₂
    grind
  · simp only [not_le, Nat.lt_iff_add_one_le] at h₂
    apply Nat.mul_self_le_mul_self at h₂
    grind

end FirstOrder.Language.presburger
