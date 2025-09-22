/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

* `Ideal.IsHomogeneous.isPrime_iff`: for any `I : Ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
  homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `Ideal.IsPrime.homogeneousCore`: for any `I : Ideal A`, if `I` is prime, then
  `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `Ideal.IsHomogeneous.radical`: for any `I : Ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `HomogeneousIdeal.radical`: for any `I : HomogeneousIdeal 𝒜`, `I.radical` is the
  radical of `I` as a `HomogeneousIdeal 𝒜`.

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
`LinearOrderedCancelAddCommMonoid`. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `Ideal.IsHomogeneous.isPrime_iff`
fails for a non-cancellative set see `Counterexamples/HomogeneousPrimeNotPrime.lean`.

## Tags

homogeneous, radical
-/


open GradedRing DirectSum SetLike Finset

variable {ι σ A : Type*}
variable [CommRing A]
variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

theorem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (I_ne_top : I ≠ ⊤)
    (homogeneous_mem_or_mem :
      ∀ {x y : A}, IsHomogeneousElem 𝒜 x → IsHomogeneousElem 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I) :
    Ideal.IsPrime I :=
  ⟨I_ne_top, by
    intro x y hxy
    by_contra! rid
    obtain ⟨rid₁, rid₂⟩ := rid
    classical
      /-
        The idea of the proof is the following :
        since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
        Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support | yⱼ ∉ J}`;
        let `max₁, max₂` be the maximum of the two sets, then `proj (max₁ + max₂) (x * y) ∈ I`.
        Then, `proj max₁ x ∉ I` and `proj max₂ j ∉ I`
        but `proj i x ∈ I` for all `max₁ < i` and `proj j y ∈ I` for all `max₂ < j`.
        `  proj (max₁ + max₂) (x * y)`
        `= ∑ {(i, j) ∈ supports | i + j = max₁ + max₂}, xᵢ * yⱼ`
        `= proj max₁ x * proj max₂ y`
        `  + ∑ {(i, j) ∈ supports \ {(max₁, max₂)} | i + j = max₁ + max₂}, xᵢ * yⱼ`.
        This is a contradiction, because both `proj (max₁ + max₂) (x * y) ∈ I` and the sum on the
        right-hand side is in `I` however `proj max₁ x * proj max₂ y` is not in `I`.
        -/
      set set₁ := {i ∈ (decompose 𝒜 x).support | proj 𝒜 i x ∉ I} with set₁_eq
      set set₂ := {i ∈ (decompose 𝒜 y).support | proj 𝒜 i y ∉ I} with set₂_eq
      have nonempty :
        ∀ x : A, x ∉ I → {i ∈ (decompose 𝒜 x).support | proj 𝒜 i x ∉ I}.Nonempty := by
        intro x hx
        rw [filter_nonempty_iff]
        contrapose! hx
        simp_rw [proj_apply] at hx
        rw [← sum_support_decompose 𝒜 x]
        exact Ideal.sum_mem _ hx
      set max₁ := set₁.max' (nonempty x rid₁)
      set max₂ := set₂.max' (nonempty y rid₂)
      have mem_max₁ : max₁ ∈ set₁ := max'_mem set₁ (nonempty x rid₁)
      have mem_max₂ : max₂ ∈ set₂ := max'_mem set₂ (nonempty y rid₂)
      replace hxy : proj 𝒜 (max₁ + max₂) (x * y) ∈ I := hI _ hxy
      have mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∈ I := by
        set antidiag :=
          {z ∈ (decompose 𝒜 x).support ×ˢ (decompose 𝒜 y).support | z.1 + z.2 = max₁ + max₂}
           with ha
        have mem_antidiag : (max₁, max₂) ∈ antidiag := by
          simp only [antidiag, mem_filter, mem_product]
          exact ⟨⟨mem_of_mem_filter _ mem_max₁, mem_of_mem_filter _ mem_max₂⟩, trivial⟩
        have eq_add_sum :=
          calc
            proj 𝒜 (max₁ + max₂) (x * y) = ∑ ij ∈ antidiag, proj 𝒜 ij.1 x * proj 𝒜 ij.2 y := by
              simp_rw [ha, proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply 𝒜]
            _ =
                proj 𝒜 max₁ x * proj 𝒜 max₂ y +
                  ∑ ij ∈ antidiag.erase (max₁, max₂), proj 𝒜 ij.1 x * proj 𝒜 ij.2 y :=
              (add_sum_erase _ _ mem_antidiag).symm
        rw [eq_sub_of_add_eq eq_add_sum.symm]
        refine Ideal.sub_mem _ hxy (Ideal.sum_mem _ fun z H => ?_)
        rcases z with ⟨i, j⟩
        simp only [antidiag, mem_erase, Prod.mk_inj, Ne, mem_filter, mem_product] at H
        rcases H with ⟨H₁, ⟨H₂, H₃⟩, H₄⟩
        have max_lt : max₁ < i ∨ max₂ < j := by
          rcases lt_trichotomy max₁ i with (h | rfl | h)
          · exact Or.inl h
          · refine False.elim (H₁ ⟨rfl, add_left_cancel H₄⟩)
          · apply Or.inr
            have := add_lt_add_right h j
            rw [H₄] at this
            exact lt_of_add_lt_add_left this
        rcases max_lt with max_lt | max_lt
        · -- in this case `max₁ < i`, then `xᵢ ∈ I`; for otherwise `i ∈ set₁` then `i ≤ max₁`.
          have notMem : i ∉ set₁ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₁ (nonempty x rid₁)).mp max_lt i h)
          rw [set₁_eq] at notMem
          simp only [not_and, Classical.not_not, mem_filter] at notMem
          exact Ideal.mul_mem_right _ I (notMem H₂)
        · -- in this case `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
          have notMem : j ∉ set₂ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₂ (nonempty y rid₂)).mp max_lt j h)
          rw [set₂_eq] at notMem
          simp only [not_and, Classical.not_not, mem_filter] at notMem
          exact Ideal.mul_mem_left I _ (notMem H₃)
      have notMem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∉ I := by
        have neither_mem : proj 𝒜 max₁ x ∉ I ∧ proj 𝒜 max₂ y ∉ I := by
          rw [mem_filter] at mem_max₁ mem_max₂
          exact ⟨mem_max₁.2, mem_max₂.2⟩
        intro _rid
        rcases homogeneous_mem_or_mem ⟨max₁, SetLike.coe_mem _⟩ ⟨max₂, SetLike.coe_mem _⟩ mem_I
          with h | h
        · apply neither_mem.1 h
        · apply neither_mem.2 h
      exact notMem_I mem_I⟩

theorem Ideal.IsHomogeneous.isPrime_iff {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.IsPrime ↔
      I ≠ ⊤ ∧
        ∀ {x y : A},
          IsHomogeneousElem 𝒜 x → IsHomogeneousElem 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun HI => ⟨HI.ne_top, fun _ _ hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩

theorem Ideal.IsPrime.homogeneousCore {I : Ideal A} (h : I.IsPrime) :
    (I.homogeneousCore 𝒜).toIdeal.IsPrime := by
  apply (Ideal.homogeneousCore 𝒜 I).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine H.imp ?_ ?_
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hx
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hy

theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    I.radical = InfSet.sInf { J | Ideal.IsHomogeneous 𝒜 J ∧ I ≤ J ∧ J.IsPrime } := by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    rintro J ⟨HJ₁, HJ₂⟩
    refine ⟨(J.homogeneousCore 𝒜).toIdeal, ?_, J.toIdeal_homogeneousCore_le _⟩
    refine ⟨HomogeneousIdeal.isHomogeneous _, ?_, HJ₂.homogeneousCore⟩
    exact hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ HJ₁)

theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.radical.IsHomogeneous 𝒜 := by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left

/-- The radical of a homogeneous ideal, as another homogeneous ideal. -/
def HomogeneousIdeal.radical (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  ⟨I.toIdeal.radical, I.isHomogeneous.radical⟩

@[simp]
theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) :
    I.radical.toIdeal = I.toIdeal.radical := rfl
