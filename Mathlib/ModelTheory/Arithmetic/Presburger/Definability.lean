/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic
public import Mathlib.ModelTheory.Definability

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Presburger definability and semilinear sets

This file formalizes the equivalence between Presburger definable sets and semilinear sets. As an
application of this result, we show that the graph of multiplication is not Presburger definable.

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

@[expose] public section

variable {α : Type*} [Fintype α] {s : Set (α → ℕ)} {A : Set ℕ}

open Set Submodule FirstOrder Language

theorem IsLinearSet.definable (hs : IsLinearSet s) : A.Definable presburger s := by
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

theorem IsSemilinearSet.definable (hs : IsSemilinearSet s) : A.Definable presburger s := by
  rw [isSemilinearSet_iff] at hs
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_setOf_eq] at this
  simp [this]

namespace FirstOrder.Language.presburger

lemma term_realize_eq_add_dotProduct (t : presburger[[A]].Term α) :
    ∃ (k : ℕ) (u : α → ℕ), ∀ (v : α → ℕ), t.realize v = k + u ⬝ᵥ v := by
  classical
  induction t with simp only [Term.realize]
  | var i =>
    refine ⟨0, Pi.single i 1, ?_⟩
    simp
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
        rw [withConstants_funMap_sumInr]
        simp only [constantsOn_Functions, constantsOnFunc.eq_1, coe_con, zero_dotProduct, add_zero]
        rfl
      | succ => nomatch f

lemma isSemilinearSet_boundedFormula_realize {n} (φ : presburger[[A]].BoundedFormula α n) :
    IsSemilinearSet {v : α ⊕ Fin n → ℕ | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
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
  rw [image_preimage_eq s fun x => ⟨![x], rfl⟩]
  constructor
  · intro hs
    apply IsSemilinearSet.isProperSemilinearSet at hs
    rw [isProperSemilinearSet_iff] at hs
    rcases hs with ⟨S, hS, rfl⟩
    replace hS : ∀ t ∈ S, ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ t ↔ x + p ∈ t := by
      intro t ht
      apply hS at ht
      rw [isProperLinearSet_iff] at ht
      rcases ht with ⟨a, t, ht, rfl⟩
      have hcard : t.card ≤ 1 := by
        by_contra hcard
        simp only [not_le, Finset.one_lt_card_iff] at hcard
        rcases hcard with ⟨a, b, ha, hb, hab⟩
        have hb' : b ≠ 0 := by
          intro hb'
          apply ht.zero_notMem_image
          simp [← hb', hb]
        revert ht
        simp only [imp_false, not_linearIndepOn_finset_iffₛ, id_eq]
        refine ⟨Pi.single a b, Pi.single b a, ?_, a, ha, ?_⟩
        · simpa [Pi.single_apply, ha, hb] using mul_comm b a
        · simp [hab, hb']
      simp_rw [Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff] at hcard
      rcases hcard with ⟨b, (rfl | rfl)⟩
      · refine ⟨a + 1, 1, zero_lt_one, fun x hx => ?_⟩
        simp [(Nat.lt_of_succ_le hx).ne', (Nat.lt_of_succ_le (Nat.le_succ_of_le hx)).ne']
      · have hb : b ≠ 0 := by
          intro hb
          apply ht.zero_notMem_image
          simp [hb]
        rw [Nat.ne_zero_iff_zero_lt] at hb
        refine ⟨a, b, hb, fun x hx => ?_⟩
        simp only [Finset.coe_singleton, mem_vadd_set, SetLike.mem_coe,
          AddSubmonoid.mem_closure_singleton, smul_eq_mul, vadd_eq_add, exists_exists_eq_and]
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨x + 1, ?_⟩
          simp [add_one_mul, add_assoc]
        · rintro ⟨y, heq⟩
          cases y with
          | zero =>
            rw [zero_mul, add_zero] at heq
            simp only [heq, ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at hx
            simp [hx] at hb
          | succ y =>
            rw [add_one_mul, ← add_assoc, add_right_cancel_iff] at heq
            exact ⟨y, heq⟩
    choose! k p hS hS' using hS
    refine ⟨S.sup k, S.lcm p, ?_, fun x hx => ?_⟩
    · rw [gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq]
      simpa [Finset.lcm_eq_zero_iff, ← Nat.pos_iff_ne_zero]
    · simp only [ge_iff_le, Finset.sup_le_iff] at hx
      refine exists_congr fun t => and_congr_right fun ht => ?_
      have hpt : p t ∣ S.lcm p := Finset.dvd_lcm ht
      rw [dvd_iff_exists_eq_mul_left] at hpt
      rcases hpt with ⟨m, hpt⟩
      rw [hpt]
      clear hpt
      induction m with
      | zero => simp
      | succ m ih =>
        simp [← ih, Nat.succ_mul, ← add_assoc,
          ← hS' t ht (x + m * p t) (le_add_of_le_left (hx t ht))]
  · intro ⟨k, p, hp, hs⟩
    have h₁ : {x ∈ s | x < k}.Finite := (Set.finite_lt_nat k).subset (sep_subset_setOf _ _)
    have h₂ : {x ∈ s | k ≤ x ∧ x < k + p}.Finite :=
      (Set.finite_Ico k (k + p)).subset (sep_subset_setOf _ _)
    convert (IsSemilinearSet.of_finite h₁).union (.add (.of_finite h₂) (.closure_finset {p}))
    ext x
    simp only [sep_and, Finset.coe_singleton, mem_union, mem_setOf_eq, mem_add, mem_inter_iff,
      SetLike.mem_coe, AddSubmonoid.mem_closure_singleton, smul_eq_mul, exists_exists_eq_and]
    constructor
    · intro hx
      by_cases hx' : x < k
      · exact Or.inl ⟨hx, hx'⟩
      · rw [not_lt] at hx'
        refine Or.inr ⟨k + (x - k) % p, ⟨⟨?_1, ?_2⟩, ?_1, ?_3⟩, (x - k) / p, ?_4⟩
        · rw [← add_tsub_cancel_of_le hx', ← Nat.mod_add_div' (x - k) p, ← add_assoc] at hx
          generalize (x - k) / p = m at hx
          induction m with
          | zero => simpa using hx
          | succ m ih =>
            refine ih ?_
            rwa [hs _ (Nat.le_add_right_of_le (Nat.le_add_right _ _)), add_assoc, ← Nat.add_one_mul]
        · apply Nat.le_add_right
        · apply Nat.add_lt_add_left (Nat.mod_lt _ hp)
        · rw [add_assoc, Nat.mod_add_div', add_tsub_cancel_of_le hx']
    · rintro (⟨hx, hx'⟩ | ⟨x, ⟨⟨hx, hx'⟩, _⟩, m, rfl⟩)
      · exact hx
      · induction m with
        | zero => simpa
        | succ m ih =>
          rw [hs _ (le_add_right hx')] at ih
          rwa [Nat.add_one_mul, ← add_assoc]

/-- The graph of multiplication is not Presburger definable in `ℕ`. -/
theorem mul_not_definable :
    ¬ A.Definable presburger {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : ℕ} := by
    rcases hmul with ⟨φ, hφ⟩
    exists Formula.iExs (Fin 1) (φ.subst ![Term.var (.inl 0), Term.var (.inr 0), Term.var (.inr 0)])
    simp only [setOf] at hφ
    ext x
    simp only [Fin.isValue, mem_setOf_eq, Formula.Realize, BoundedFormula.realize_iExs,
      BoundedFormula.realize_subst]
    constructor
    · intro ⟨y, h⟩
      refine ⟨![y], ?_⟩
      rw [← Formula.Realize, ← hφ]
      simp [h]
    · intro ⟨v, h⟩
      rw [← Formula.Realize, ← hφ] at h
      simp only [Fin.isValue, Matrix.cons_val_zero, Term.realize_var, Sum.elim_inl,
        Matrix.cons_val_one, Sum.elim_inr, Matrix.cons_val] at h
      exact ⟨v 0, h.symm⟩
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
