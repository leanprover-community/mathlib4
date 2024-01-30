/-
Copyright (c) 2024 Antoine Chambert-Loir (and others). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir (add others)
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.FiniteDimensional

variable (R : Type*) [LinearOrderedField R]

variable (V : Type*) [AddCommGroup V] [Module R V]
variable (W : Type*) [AddCommGroup W] [Module R W]

section Span

variable {V}
def ConvexCone.span (s : Set V) : ConvexCone R V :=
  sInf {c : ConvexCone R V | s ⊆ ↑c}

def PointedCone.span (s : Set V) : PointedCone R V :=
  sInf {c : PointedCone R V | s ⊆ ↑c}

lemma PointedCone.sum_mem  (𝕜 : Type u_1) (E : Type u_2) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] (C : PointedCone 𝕜 E)
  (ι : Type*) [DecidableEq ι] (s : Finset ι) (f : ι → E) (hfs : ∀ i ∈ s, f i ∈ C) :
  s.sum f ∈ C := by
  /- induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine zero_mem C
  | insert has hs =>
    rw [Finset.sum_insert has]
    apply add_mem
    exact hfs _ (Finset.mem_insert_self _ _)
    apply hs
    exact fun i hi => hfs _ (Finset.mem_insert_of_mem hi) -/
    exact Submodule.sum_mem C hfs

end Span

section lpAux

open  FiniteDimensional

namespace lpAux

variable (A : Set V) [Finite A] [LinearOrder A] (v : V)
    (hA : ∀ (f : Module.Dual R V) (_ : ∀ x ∈ A, 0 ≤ f x),
      (0 ≤ f v) ∨
      (finrank R (Submodule.span R (A ∪ {v}))
        > finrank R (Submodule.span R (LinearMap.ker f ∩ (A : Set V))) + 1))
    (hv : ∀ (t : V →₀ R)
      (_ : (t.support : Set V) ⊆ A)
      (_ : LinearIndependent R (fun (x : t.support) ↦ (x : V)))
      (_ : v = t.sum (fun x s ↦ s • x)), ∃ x, t x < 0)

lemma memspan : v ∈ Submodule.span R A := by
  by_contra hv'
  suffices : ∃ f : Module.Dual R V, ((∀ a ∈ A, f a = 0) ∧ ¬ (0 ≤ f v))
  obtain ⟨f, hfA, hfv⟩ := this
  have hAv1 : finrank R (Submodule.span R  (A ∪ {v})) = finrank R (Submodule.span R A) + 1
  · rw [Submodule.span_union]
    apply Nat.add_right_cancel
    have : FiniteDimensional R (Submodule.span R A) :=
      FiniteDimensional.span_of_finite R A.toFinite
    have : FiniteDimensional R (Submodule.span R {v}) :=
      FiniteDimensional.span_of_finite R (Set.finite_singleton v)
    rw [Submodule.finrank_sup_add_finrank_inf_eq]
    rw [add_assoc, Nat.add_left_cancel_iff]
    rw [finrank_span_singleton _]
    simp only [self_eq_add_right, Submodule.finrank_eq_zero]
    rw [eq_bot_iff]
    intro x
    simp only [Submodule.mem_inf, Submodule.mem_bot, and_imp]
    intro hxA hxv
    rw [Submodule.mem_span_singleton] at hxv
    obtain ⟨r, rfl⟩ := hxv
    by_cases hr : r = 0
    · rw [hr, zero_smul]
    · exfalso
      apply hv'
      rw [← one_smul R v, ← inv_mul_cancel hr, mul_smul]
      exact Submodule.smul_mem _ r⁻¹ hxA
    · intro h
      apply hv'
      rw [h]
      apply zero_mem
  have hAv2 : finrank R (Submodule.span R (LinearMap.ker f ∩ A)) = finrank R (Submodule.span R A)
  · suffices : ↑(LinearMap.ker f) ∩ A = A
    rw [this]
    ext a
    simp only [Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_ker, and_iff_right_iff_imp]
    exact hfA a
  specialize hA f _
  · intro a ha
    simp only [hfA a ha, le_refl]
  have hA := Or.resolve_left hA hfv
  rw [hAv1, hAv2] at hA
  exact LT.lt.false hA
  -- construct f
  suffices : Submodule.dualAnnihilator (Submodule.span R (A ∪ {v})) <
    Submodule.dualAnnihilator (Submodule.span R A)
  obtain ⟨f, hmem, hnotmem⟩ := SetLike.exists_of_lt this
  have hfA : ∀ a ∈ A, f a = 0
  · simp only [Submodule.mem_dualAnnihilator] at hmem
    exact fun a ha => hmem a (Submodule.subset_span ha)
  have hfv : f v ≠ 0
  · simp only [Submodule.mem_dualAnnihilator] at hnotmem
    intro hfv'
    apply hnotmem
    suffices : Submodule.span R (A ∪ {v}) ≤ LinearMap.ker f
    intro w hw
    rw [← LinearMap.mem_ker]
    exact this hw
    simp only [Submodule.span_le]
    intro x hx
    simp only [Set.union_singleton, Set.mem_insert_iff, SetLike.mem_coe] at hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    cases hx with
    | inl hx => rw [hx, hfv']
    | inr hx => exact hfA x hx
  by_cases hfv' : 0 < f v
  · use -f
    constructor
    · intro a ha
      simp only [LinearMap.neg_apply, hfA a ha, neg_zero]
    · simp only [LinearMap.neg_apply, Left.nonneg_neg_iff, not_le]
      exact hfv'
  · use f
    constructor
    · intro a ha
      simp only [LinearMap.neg_apply, hfA a ha, neg_zero]
    · exact fun h => hfv' (lt_of_le_of_ne h hfv.symm)
  simp only [lt_iff_le_not_le, Subspace.dualAnnihilator_le_dualAnnihilator_iff]
  constructor
  exact Submodule.span_mono (A.subset_union_left {v})
  intro h
  apply hv'
  apply h
  apply Submodule.subset_span
  exact Set.mem_union_right A rfl

example (W W' : Submodule R V) (h : W < W') : ∃ f ∈ W', f ∉ W := by
  exact SetLike.exists_of_lt h

variable {V}
structure D (A : Set V) (v : V) where
  basis : Set V
  subset : basis ⊆ A
  indep : LinearIndependent R (fun (x : basis) => (x : V))
  mem : v ∈ Submodule.span R basis

/-
example (R : Type*) [Semiring R] (V : Type*) [AddCommGroup V] [Module R V] (A : Set V) (v : V) :
  v ∈ Submodule.span R A ↔ ∃ (r : V →₀ R), ↑(r.support) ⊆ A ∧ v = r.sum (fun x a => a • x) := by
  rw [Finsupp.mem_span_iff_total]
  constructor
  · intro hv

    refine' Submodule.span_induction hv  _ _ _ _
    · -- Hs
      intro a ha
      use Finsupp.single a 1
      constructor
      intro x
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
      intro hx
      by_cases hx' : x = a
      · rw [hx']
        exact ha
      · rw [Finsupp.single_eq_of_ne (ne_comm.mpr hx')] at hx
        contradiction
      simp only [zero_smul, Finsupp.sum_single_index, one_smul]
    · -- H0
      sorry
    · -- H1
      sorry
    · -- H2
      sorry

  · rintro ⟨r, hr, rfl⟩
    rw [Finsupp.sum]
    apply Submodule.sum_mem
    intro x hx
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact hr hx
-/

def iterate (B : D R A v) : D R A v := by
  classical
  have hr := (Finsupp.mem_span_iff_total _ _ _).mp B.mem
  set r := Finsupp.extendDomain hr.choose with r_eq
  have hrsupp : (r.support : Set V) ⊆ B.basis
  · intro x hx
    simp only [Finsupp.extendDomain_support, Finset.coe_map,
      Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨⟨x, hx'⟩, hx, rfl⟩ := hx
    exact hx'
  have hr' : v = Finsupp.sum r fun x s ↦ s • x
  · suffices : v = Finsupp.sum hr.choose (fun x s ↦ s • (x : V))
    rw [this, r_eq]
    simp only [Finsupp.sum]
    simp only [Finsupp.extendDomain_support, Finsupp.extendDomain_toFun, dite_smul, zero_smul,
      Finset.sum_map, Function.Embedding.coe_subtype, Subtype.coe_prop, Subtype.coe_eta,
      dite_eq_ite, ite_true]
    exact hr.choose_spec.symm
  have : ∃ a ∈ B.basis, r a < 0
  · by_contra this
    push_neg at this
    obtain ⟨x, hx⟩ := hv r (subset_trans hrsupp B.subset)
      (LinearIndependent.mono hrsupp (R := R) B.indep) hr'
    suffices hx' : x ∈ B.basis
    exact LT.lt.false (lt_of_le_of_lt (this x hx') hx)
    · apply hrsupp
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      exact ne_of_lt hx






  sorry

lemma lpAux' (A : Set V) [Finite A] [LinearOrder A]
    (v : V) (hvA : v ∈ Submodule.span R A)
    (hv : ∀ (t : V →₀ R)
      (hsupp : (t.support : Set V) ⊆ A)
      (hindep : LinearIndependent R (fun (x : t.support) ↦ (x : V)))
      (hv : v = t.sum (fun x s ↦ s • x)), ∃ x, t x < 0)
    (hA : ∀ (f : Module.Dual R V) (hf : ∀ x ∈ A, f x ≥ 0),
      (f v ≥ 0) ∨
      (Module.rank R (Submodule.span R (A ∪ {v}))
        > Module.rank R (Submodule.span R (LinearMap.ker f ∩ (A : Set V))) + 1)) : False :=  by sorry

lemma lpAux (A : Set V) [Finite A] (v : V)
    (hA : ∀ (f : Module.Dual R V) (_ : ∀ x ∈ A, f x ≥ 0),
      (f v ≥ 0) ∨
      (Module.rank R (Submodule.span R (A ∪ {v}))
        > Module.rank R (Submodule.span R (LinearMap.ker f ∩ (A : Set V))) + 1)) :
    ∃ (t : V →₀ R)
      (_ : (t.support : Set V) ⊆ A)
      (_ : LinearIndependent R (fun (x : t.support) ↦ (x : V)))
      (_ : ∀ x, 0 ≤ t x),
      v = t.sum (fun x s ↦ s • x) := by sorry

end lpAux

/-- Theorem 1.2.1 -/
theorem lp (A : Set V) [Finite A] (v : V) : List.TFAE [
    ∃ (t : V →₀ R)
      (_ : (t.support : Set V) ⊆ A)
      (_ : LinearIndependent R (fun (x : t.support) ↦ (x : V)))
      (_ : ∀ x, 0 ≤ t x),
      v = t.sum (fun x s ↦ s • x),
    v ∈ PointedCone.span R (A : Set V),
    ∀ (f : Module.Dual R V) (_ : ∀ x ∈ A, f x ≥ 0), f v ≥ 0,
    ∀ (f : Module.Dual R V) (_ : ∀ x ∈ A, f x ≥ 0),
      (f v ≥ 0) ∨
      (Module.rank R (Submodule.span R (A ∪ {v}))
        > Module.rank R (Submodule.span R (LinearMap.ker f ∩ (A : Set V))) + 1)] := by
  apply List.tfae_of_cycle _
  · apply lpAux
  rw [List.chain_cons]
  constructor
  · rintro ⟨t, hsupp, _, hpos, ht⟩
    unfold PointedCone.span
    simp only [Submodule.mem_sInf, Set.mem_setOf_eq]
    intro C hC
    rw [ht, Finsupp.sum]
    apply Submodule.sum_mem
    intro c hc
    exact Submodule.smul_mem C { val := t c, property := hpos c } (hC (hsupp hc))
  rw [List.chain_cons]
  constructor
  · intro hv f hf
    set C : PointedCone R V  := PointedCone.comap f (PointedCone.positive R R)
    simp [PointedCone.span, Submodule.mem_span] at hv
    specialize hv C _
    simp [C]
    intro x hx
    simp only [Set.mem_preimage, SetLike.mem_coe, PointedCone.mem_positive]
    exact hf x hx
    exact hv
  rw [List.chain_cons]
  constructor
  · exact fun hv f hf => Or.inl (hv f hf)
  exact List.Chain.nil




theorem caratheodory (A : Set V) (x : V) (hx : x ∈ ConvexCone.span R A) :
  ∃ (A' : Set V)
    (fA' : Finite A')
    (hindep : LinearIndependent R (fun (x : A') ↦ (x : V))),
    x ∈ ConvexCone.span R A' := sorry

variable {V}
def isPolyhedralCone (C : Set V) : Prop :=
    ∃ (A : Finset V), C = ConvexCone.span R (A : Set V)

def isPolyhedralCone' (C : Set V) : Prop :=
    ∃ (A : Finset (Module.Dual R V)),
    C = { v : V | ∀ f ∈ A, 0 ≤ f v }

theorem farkas3 (C : Set V) :
  isPolyhedralCone R C ↔ isPolyhedralCone' R C := by
  constructor
  · unfold isPolyhedralCone
    rintro ⟨A, hA⟩
    sorry
  · sorry

theorem farkas1' (φ : V →ₗ[R] W) (C : ConvexCone R V) (w : W) :
    (∃ (v : V), φ v = w ∧ v ∈ C)
    ↔ (∀ (f : Module.Dual R W), (hf: ∀ x ∈ C, 0 ≤ f (φ x))
      → 0 ≤ f w) := by
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact fun f hf => hf v hv
  · intro hφ
    sorry

section

variable (V : Type*) [OrderedAddCommGroup V] [Module ℝ V]
variable (W : Type*) [OrderedAddCommGroup W] [Module ℝ W]
example (φ : V →ₗ[ℝ] W) (w : W) :
    (∃ (v : V), φ v = w ∧ 0 ≤ v)
    ↔ (∀ (f : Module.Dual ℝ W), (hf : ∀ x, 0 ≤ x → 0 ≤ f (φ x))
      → 0 ≤ f w ) := by
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact fun f hf => hf v hv
  · intro hφ
    sorry

#exit
import Mathlib.Analysis.Convex.Cone.Pointed

variable (𝕜 E : Type*)

variable {E}
/-- Give a set `s` in `E`, `toPointedCone 𝕜 s` is the cone consisting of
  linear combinations of elements in `s` with non-negative coefficients. -/
abbrev Set.toPointedCone (𝕜)
    [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] (s : Set E) :
    PointedCone 𝕜 E :=
  Submodule.span {c : 𝕜 // 0 ≤ c} s

variable {𝕜}
variable  [LinearOrderedField 𝕜] [AddCommMonoid E] [Module 𝕜 E]

def Convex.toPointedCone (s : Set E) (hns : Set.Nonempty s) (hs : Convex 𝕜 s) : PointedCone 𝕜 E where
  carrier := { y | ∃ x ∈ s, ∃ c : 𝕜, 0 ≤ c ∧ y = c • x }
  add_mem' := fun {x} {y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    obtain ⟨x, hx, a, ⟨ha, rfl⟩⟩ := hx
    obtain ⟨y, hy, b, ⟨hb, rfl⟩⟩ := hy
    by_cases hab : 0 < a + b
    · use (a / (a + b)) • x + (b / (a + b)) • y
      constructor
      apply convex_iff_segment_subset.mp hs hx hy
      use a / (a + b), b / (a + b)
      constructor
      · simp only [le_div_iff hab, zero_mul]; exact ha
      constructor
      · simp only [le_div_iff hab, zero_mul]; exact hb
      constructor
      · rw [← add_div]
        exact div_self (ne_of_gt hab)
      rfl
      use (a + b)
      apply And.intro (le_of_lt hab)
      rw [smul_add, ← smul_assoc, ← smul_assoc]
      rw [smul_eq_mul, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt hab), mul_one]
      rw [smul_eq_mul, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt hab), mul_one]
    · use x, hx, 0, Eq.le rfl
      simp only [not_lt] at hab
      rw [eq_zero_of_add_nonpos_left ha hb hab, eq_zero_of_add_nonpos_left hb ha ?_, zero_smul, zero_smul, zero_add]
      rw [add_comm]; exact hab
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    use hns.some, hns.some_mem, 0
    simp only [zero_smul, le_refl, and_self]
  smul_mem' := fun c {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    obtain ⟨x, hx, a, ha, rfl⟩ := hx
    use x, hx, c * a
    constructor
    · exact mul_nonneg c.prop ha
    · rw [← smul_assoc]; rfl

lemma Set.toPointedCone_eq_smul_convexHull (s : Set E) (hns : Set.Nonempty s) :
    s.toPointedCone 𝕜 = convexHull 𝕜 {y | ∃ x ∈ s, ∃ (t : 𝕜), 0 ≤ t ∧ t • x = y} := by
  ext y
  simp only [SetLike.mem_coe, le_eq_subset]
  constructor
  · rw [toPointedCone]
    intro hy
    refine Submodule.span_induction hy ?_ ?_ ?_ ?_
    · intro x hx
      apply subset_convexHull
      simp only [mem_setOf_eq]
      use x, hx, 1, zero_le_one
      rw [one_smul]
    · apply subset_convexHull
      simp only [mem_setOf_eq]
      use hns.some, hns.some_mem, 0, le_rfl
      rw [zero_smul]
    · intro x y hx hy
      sorry

    · rintro ⟨c, hc⟩ x hx
      simp only [Nonneg.mk_smul]
      sorry

  · rw [Set.toPointedCone, Submodule.mem_span, mem_convexHull_iff]
    intro h p hp
    apply h
    · intro y hy
      simp only [mem_setOf_eq] at hy
      obtain ⟨x, hx, ⟨t, ht, rfl⟩⟩ := hy
      change (⟨t, ht⟩ : { c : 𝕜 // 0 ≤ c }) • x ∈ p
      apply Submodule.smul_mem
      exact hp hx
    · rw [convex_iff_segment_subset]
      intro x hx y hy
      rw [segment_subset_iff]
      intro a b ha hb hab
      simp only [SetLike.mem_coe]
      apply Submodule.add_mem
      change (⟨a, ha⟩ : { c : 𝕜 // 0 ≤ c}) • x ∈ p
      exact Submodule.smul_mem p _ hx
      change (⟨b, hb⟩ : { c : 𝕜 // 0 ≤ c}) • y ∈ p
      exact Submodule.smul_mem p _ hy
