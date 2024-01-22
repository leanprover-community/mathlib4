/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.RingTheory.FiniteType

/-!
# The properties of a graded Noetherian ring.

This file proves some properties of a graded Noetherian ring:
1. The 0-th grade of a Noetherian ring is also a Noetherian ring.
2. For a Noetherian ring `A` which is internally graded by `𝒜`,
   `⨁_{i>0} 𝒜ᵢ` is finitely generated as an ideal of `A`.
-/


namespace GradedRing

section Ring

variable {ι A σ : Type*}
variable [Ring A] [IsNoetherianRing A]
variable [DecidableEq ι] [CanonicallyOrderedAddCommMonoid ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]


/--
If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring.
-/
instance GradeZero.subring_isNoetherianRing_of_isNoetherianRing : IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜)
  (GradedRing.projZeroRingHom'_surjective 𝒜)

end Ring

section CommRing

variable {A : Type*}
variable [CommRing A] [IsNoetherianRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]

instance : Algebra (𝒜 0) A := Algebra.ofSubring (SetLike.GradeZero.subring 𝒜)

open BigOperators Pointwise

instance : Algebra.FiniteType (𝒜 0) A := by
  classical
  obtain ⟨S, hS1, (hS2 : _ = Ideal.span (α := A) S)⟩ := Ideal.fg_iff_homogeneously_fg _  |>.mp <|
    isNoetherianRing_iff_ideal_fg A |>.mp inferInstance (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  choose deg h_deg1 using hS1
  have h_deg0 (a : A) (h1 : a ∈ S) (h2 : a ≠ 0) : 0 < deg a h1
  · by_contra! rid
    simp only [nonpos_iff_eq_zero] at rid
    have m : a ∈ Ideal.span S := Ideal.subset_span h1
    specialize h_deg1 a h1
    rw [rid] at h_deg1
    erw [← hS2, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (hx := h_deg1)] at m
    exact h2 m

  suffices subset (m : ℕ) : (𝒜 m : Set A) ⊆ (Algebra.adjoin (𝒜 0) (S : Set A))
  · use S
    refine le_antisymm le_top fun a _ ↦ ?_
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    exact Subalgebra.sum_mem _ fun j hj ↦ subset j <| Subtype.mem _

  suffices (n : ℕ) :
    𝒜 n.succ = ⨆ (s : {s : S | deg s.1 s.2 ≤ n + 1 }), (s : A) • 𝒜 (n.succ - deg _ s.1.2)
  ·
    cases m with | zero => ?_ | succ m => ?_
    · simp only [Nat.zero_eq]
      intro x hx
      show _ ∈ Subsemiring.closure (_ ∪ _)
      rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S]
      exact @le_sup_left (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
        Subsemiring.subset_closure ⟨⟨_, hx⟩, rfl⟩
    induction' m using Nat.strong_induction_on with m ih
    rw [this]
    intro x hx
    simp only [SetLike.mem_coe] at hx ⊢
    refine AddSubgroup.iSup_induction (C := fun y ↦ y ∈ Algebra.adjoin (𝒜 0) (S : Set A))
      (fun (s : {s : S | deg s.1 s.2 ≤ m + 1 }) ↦ (s : A) • 𝒜 (m.succ - deg _ s.1.2)) hx ?_ ?_ ?_
    · rintro ⟨⟨x, hx1⟩, (hx2 : deg _ _ ≤ _)⟩ y hy1
      simp only at hy1
      rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hy1
      obtain ⟨y, hy1, rfl⟩ := hy1
      by_cases ineq1 : x = 0
      · rw [ineq1, zero_smul]; exact Subalgebra.zero_mem _

      by_cases ineq0 : m < deg x hx1
      · have eq0 : m.succ - deg x hx1 = 0
        · simp only [tsub_eq_zero_iff_le]
          exact ineq0
        rw [eq0] at hy1
        refine Subalgebra.mul_mem _ (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_)
          (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_) <;>
        rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S]
        · exact @le_sup_right (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
            Subsemiring.subset_closure hx1
        · exact @le_sup_left (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
            Subsemiring.subset_closure ⟨⟨_, hy1⟩, rfl⟩
      simp only [not_lt] at ineq0
      specialize ih (m - deg _ hx1) (Nat.sub_lt_self (h_deg0 _ hx1 ineq1) ineq0) <|
        show y ∈ _ by
          simp only [SetLike.mem_coe]
          convert hy1 using 2
          rw [Nat.succ_sub]
          exact ineq0
      refine Subalgebra.mul_mem _ (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_) ih
      rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S]
      exact @le_sup_right (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
        Subsemiring.subset_closure hx1

    · exact Subalgebra.zero_mem _
    · intros _ _ h1 h2
      exact Subalgebra.add_mem _ h1 h2

  ext x; constructor
  · intro hx
    have m : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal
    · erw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (hx := hx)]
      norm_num
    erw [hS2, mem_span_set] at m
    obtain ⟨f, hf, (eq0 : ∑ i in f.support, f i * i = x)⟩ := m
    replace eq0 :=
      calc x
        = (DirectSum.decompose 𝒜 x (n + 1) : A)
        := by simp only [DirectSum.of_eq_same, DirectSum.decompose_of_mem 𝒜 hx]
      _ = DirectSum.decompose 𝒜 (∑ a in f.support, f a * a) (n + 1) := by rw [eq0]
      _ = ∑ a in f.support, (DirectSum.decompose 𝒜 (f a * a) (n + 1) : A)
        := by change GradedRing.proj 𝒜 (n + 1) (∑ a in f.support, f a * a : A) = _
              rw [map_sum]
              rfl
      _ = ∑ a in f.support.attach, (DirectSum.decompose 𝒜 (f a * a) (n + 1) : A)
        := Finset.sum_attach _ _ |>.symm
      _ = ∑ a in f.support.attach,
            if deg a (hf a.2) ≤ n + 1
            then (DirectSum.decompose 𝒜 (f a) ((n + 1) - deg a (hf a.2)) * a : A)
            else 0
        := Finset.sum_congr rfl fun a _ ↦
          DirectSum.coe_decompose_mul_of_right_mem 𝒜 (n + 1) (h_deg1 a (hf a.2)) (a := f a)

    rw [eq0]
    refine AddSubgroup.sum_mem _ fun a _ ↦ ?_

    split_ifs with h
    · refine AddSubgroup.mem_iSup_of_mem ⟨⟨a, hf a.2⟩, h⟩ ?_
      rw [AddSubgroup.mem_smul_pointwise_iff_exists]
      exact ⟨DirectSum.decompose 𝒜 (f a) ((n + 1) - deg a (hf a.2)), SetLike.coe_mem _,
        by rw [mul_comm]; rfl⟩
    · exact AddSubgroup.zero_mem _
  · intro hx
    refine AddSubgroup.iSup_induction (C := fun y ↦ y ∈ 𝒜 n.succ)
      (fun (s : {s : S | deg s.1 s.2 ≤ n + 1 }) ↦ (s : A) • 𝒜 (n.succ - deg _ s.1.2)) hx ?_ ?_ ?_
    · rintro ⟨⟨x, hx1⟩, (hx2 : deg _ _ ≤ _)⟩ z hz1
      simp only at hz1
      rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hz1
      obtain ⟨z, hz1, rfl⟩ := hz1
      specialize h_deg1 _ hx1
      convert SetLike.mul_mem_graded h_deg1 hz1 using 2
      rw [← Nat.add_sub_assoc, add_comm, Nat.add_sub_cancel]
      exact hx2
    · exact AddSubgroup.zero_mem _
    · intros _ _ h1 h2
      exact AddSubgroup.add_mem _ h1 h2

end CommRing

end GradedRing
