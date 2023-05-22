/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

! This file was ported from Lean 3 source module ring_theory.graded_algebra.radical
! leanprover-community/mathlib commit f1944b30c97c5eb626e498307dec8b022a05bd0a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

* `ideal.is_homogeneous.is_prime_iff`: for any `I : ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
  homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `ideal.is_prime.homogeneous_core`: for any `I : ideal A`, if `I` is prime, then
  `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `ideal.is_homogeneous.radical`: for any `I : ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `homogeneous_ideal.radical`: for any `I : homogeneous_ideal 𝒜`, `I.radical` is the the
  radical of `I` as a `homogeneous_ideal 𝒜`

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
`linear_ordered_cancel_add_comm_monoid`. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `ideal.is_homogeneous.is_prime_iff`
fails for a non-cancellative set see `counterexample/homogeneous_prime_not_prime.lean`.

## Tags

homogeneous, radical
-/


open GradedRing DirectSum SetLike Finset

open BigOperators

variable {ι σ A : Type _}

variable [CommRing A]

variable [LinearOrderedCancelAddCommMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

include A

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.Homogeneous 𝒜)
    (I_ne_top : I ≠ ⊤)
    (homogeneous_mem_or_mem :
      ∀ {x y : A}, Homogeneous 𝒜 x → Homogeneous 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I) :
    Ideal.IsPrime I :=
  ⟨I_ne_top, by
    intro x y hxy
    by_contra rid
    obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid
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
        right hand side is in `I` however `proj max₁ x * proj max₂ y` is not in `I`.
        -/
      set set₁ := (decompose 𝒜 x).support.filterₓ fun i => proj 𝒜 i x ∉ I with set₁_eq
      set set₂ := (decompose 𝒜 y).support.filterₓ fun i => proj 𝒜 i y ∉ I with set₂_eq
      have nonempty :
        ∀ x : A, x ∉ I → ((decompose 𝒜 x).support.filterₓ fun i => proj 𝒜 i x ∉ I).Nonempty :=
        by
        intro x hx
        rw [filter_nonempty_iff]
        contrapose! hx
        simp_rw [proj_apply] at hx
        rw [← sum_support_decompose 𝒜 x]
        exact Ideal.sum_mem _ hx
      set max₁ := set₁.max' (Nonempty x rid₁) with max₁_eq
      set max₂ := set₂.max' (Nonempty y rid₂) with max₂_eq
      have mem_max₁ : max₁ ∈ set₁ := max'_mem set₁ (Nonempty x rid₁)
      have mem_max₂ : max₂ ∈ set₂ := max'_mem set₂ (Nonempty y rid₂)
      replace hxy : proj 𝒜 (max₁ + max₂) (x * y) ∈ I := hI _ hxy
      have mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∈ I :=
        by
        set antidiag :=
          ((decompose 𝒜 x).support ×ˢ (decompose 𝒜 y).support).filterₓ fun z : ι × ι =>
            z.1 + z.2 = max₁ + max₂ with
          ha
        have mem_antidiag : (max₁, max₂) ∈ antidiag :=
          by
          simp only [add_sum_erase, mem_filter, mem_product]
          exact ⟨⟨mem_of_mem_filter _ mem_max₁, mem_of_mem_filter _ mem_max₂⟩, rfl⟩
        have eq_add_sum :=
          calc
            proj 𝒜 (max₁ + max₂) (x * y) = ∑ ij in antidiag, proj 𝒜 ij.1 x * proj 𝒜 ij.2 y := by
              simp_rw [ha, proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply 𝒜]
            _ =
                proj 𝒜 max₁ x * proj 𝒜 max₂ y +
                  ∑ ij in antidiag.erase (max₁, max₂), proj 𝒜 ij.1 x * proj 𝒜 ij.2 y :=
              (add_sum_erase _ _ mem_antidiag).symm
            
        rw [eq_sub_of_add_eq eq_add_sum.symm]
        refine' Ideal.sub_mem _ hxy (Ideal.sum_mem _ fun z H => _)
        rcases z with ⟨i, j⟩
        simp only [mem_erase, Prod.mk.inj_iff, Ne.def, mem_filter, mem_product] at H
        rcases H with ⟨H₁, ⟨H₂, H₃⟩, H₄⟩
        have max_lt : max₁ < i ∨ max₂ < j :=
          by
          rcases lt_trichotomy max₁ i with (h | rfl | h)
          · exact Or.inl h
          · refine' False.elim (H₁ ⟨rfl, add_left_cancel H₄⟩)
          · apply Or.inr
            have := add_lt_add_right h j
            rw [H₄] at this
            exact lt_of_add_lt_add_left this
        cases max_lt
        · -- in this case `max₁ < i`, then `xᵢ ∈ I`; for otherwise `i ∈ set₁` then `i ≤ max₁`.
          have not_mem : i ∉ set₁ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₁ (Nonempty x rid₁)).mp max_lt i h)
          rw [set₁_eq] at not_mem
          simp only [not_and, Classical.not_not, Ne.def, mem_filter] at not_mem
          exact Ideal.mul_mem_right _ I (not_mem H₂)
        · -- in this case  `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
          have not_mem : j ∉ set₂ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₂ (Nonempty y rid₂)).mp max_lt j h)
          rw [set₂_eq] at not_mem
          simp only [not_and, Classical.not_not, Ne.def, mem_filter] at not_mem
          exact Ideal.mul_mem_left I _ (not_mem H₃)
      have not_mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∉ I :=
        by
        have neither_mem : proj 𝒜 max₁ x ∉ I ∧ proj 𝒜 max₂ y ∉ I :=
          by
          rw [mem_filter] at mem_max₁ mem_max₂
          exact ⟨mem_max₁.2, mem_max₂.2⟩
        intro rid
        cases homogeneous_mem_or_mem ⟨max₁, SetLike.coe_mem _⟩ ⟨max₂, SetLike.coe_mem _⟩ mem_I
        · apply neither_mem.1 h
        · apply neither_mem.2 h
      exact not_mem_I mem_I⟩
#align ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem

theorem Ideal.IsHomogeneous.isPrime_iff {I : Ideal A} (h : I.Homogeneous 𝒜) :
    I.IsPrime ↔
      I ≠ ⊤ ∧
        ∀ {x y : A},
          SetLike.Homogeneous 𝒜 x → SetLike.Homogeneous 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun HI => ⟨ne_of_apply_ne _ HI.ne_top, fun x y hx hy hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩
#align ideal.is_homogeneous.is_prime_iff Ideal.IsHomogeneous.isPrime_iff

theorem Ideal.IsPrime.homogeneousCore {I : Ideal A} (h : I.IsPrime) :
    (I.homogeneousCore 𝒜).toIdeal.IsPrime :=
  by
  apply (Ideal.homogeneousCore 𝒜 I).Homogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine' H.imp _ _
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hx
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hy
#align ideal.is_prime.homogeneous_core Ideal.IsPrime.homogeneousCore

theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.Homogeneous 𝒜) :
    I.radical = sInf { J | J.Homogeneous 𝒜 ∧ I ≤ J ∧ J.IsPrime } :=
  by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine' sInf_le_sInf_of_forall_exists_le _
    rintro J ⟨HJ₁, HJ₂⟩
    refine' ⟨(J.homogeneous_core 𝒜).toIdeal, _, J.to_ideal_homogeneous_core_le _⟩
    refine' ⟨HomogeneousIdeal.isHomogeneous _, _, HJ₂.homogeneous_core⟩
    refine' hI.to_ideal_homogeneous_core_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ HJ₁)
#align ideal.is_homogeneous.radical_eq Ideal.IsHomogeneous.radical_eq

theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.Homogeneous 𝒜) : I.radical.Homogeneous 𝒜 :=
  by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left
#align ideal.is_homogeneous.radical Ideal.IsHomogeneous.radical

/-- The radical of a homogenous ideal, as another homogenous ideal. -/
def HomogeneousIdeal.radical (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  ⟨I.toIdeal.radical, I.Homogeneous.radical⟩
#align homogeneous_ideal.radical HomogeneousIdeal.radical

@[simp]
theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) :
    I.radical.toIdeal = I.toIdeal.radical :=
  rfl
#align homogeneous_ideal.coe_radical HomogeneousIdeal.coe_radical

