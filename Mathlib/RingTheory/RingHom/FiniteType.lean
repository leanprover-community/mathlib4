/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ring_hom.finite_type
! leanprover-community/mathlib commit 64fc7238fb41b1a4f12ff05e3d5edfa360dd768c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.LocalProperties
import Mathlib.RingTheory.Localization.InvSubmonoid

/-!

# The meta properties of finite-type ring homomorphisms.

The main result is `RingHom.finiteType_is_local`.

-/


namespace RingHom

open scoped Pointwise

theorem finiteType_stableUnderComposition : StableUnderComposition @FiniteType := by
  introv R hf hg
  exact hg.comp hf
#align ring_hom.finite_type_stable_under_composition RingHom.finiteType_stableUnderComposition

theorem finiteType_holdsForLocalizationAway : HoldsForLocalizationAway @FiniteType := by
  introv R _
  suffices Algebra.FiniteType R S by
    rw [RingHom.FiniteType]
    convert this; ext;
    rw [Algebra.smul_def]; rfl
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S
#align ring_hom.finite_type_holds_for_localization_away RingHom.finiteType_holdsForLocalizationAway

theorem finiteType_ofLocalizationSpanTarget : OfLocalizationSpanTarget @FiniteType := by
  -- Setup algebra intances.
  rw [ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  classical
  letI := f.toAlgebra
  replace H : ∀ r : s, Algebra.FiniteType R (Localization.Away (r : S))
  · intro r; simp_rw [RingHom.FiniteType] at H; convert H r; ext; simp_rw [Algebra.smul_def]; rfl
  replace H := fun r => (H r).1
  constructor
  -- Suppose `s : Finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : Finset Sᵣ` generates `Sᵣ`. By assumption, we may find `lᵢ` such that
  -- `∑ lᵢ * sᵢ = 1`. I claim that all `s` and `l` and the numerators of `t` and generates `S`.
  choose t ht using H
  obtain ⟨l, hl⟩ :=
    (Finsupp.mem_span_iff_total S (s : Set S) 1).mp
      (show (1 : S) ∈ Ideal.span (s : Set S) by rw [hs]; trivial)
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (x : S)) (t x)
  use s.attach.biUnion sf ∪ s ∪ l.support.image l
  rw [eq_top_iff]
  -- We need to show that every `x` falls in the subalgebra generated by those elements.
  -- Since all `s` and `l` are in the subalgebra, it suffices to check that `sᵢ ^ nᵢ • x` falls in
  -- the algebra for each `sᵢ` and some `nᵢ`.
  rintro x -
  apply Subalgebra.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set S) l hl _ _ x _
  · intro x hx
    apply Algebra.subset_adjoin
    rw [Finset.coe_union, Finset.coe_union]
    exact Or.inl (Or.inr hx)
  · intro i
    by_cases h : l i = 0; · rw [h]; exact zero_mem _
    apply Algebra.subset_adjoin
    rw [Finset.coe_union, Finset.coe_image]
    exact Or.inr (Set.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr h))
  · intro r
    rw [Finset.coe_union, Finset.coe_union, Finset.coe_biUnion]
    -- Since all `sᵢ` and numerators of `t r` are in the algebra, it suffices to show that the
    -- image of `x` in `Sᵣ` falls in the `R`-adjoin of `t r`, which is of course true.
    -- Porting note: The following `obtain` fails because Lean wants to know right away what the
    -- placeholders are, so we need to provide a little more guidance
    -- obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalization.exists_smul_mem_of_mem_adjoin
    --   (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) _ _ _
    rw [show ∀ A : Set S, (∃ n, (r : S) ^ n • x ∈ Algebra.adjoin R A) ↔
      (∃ m : (Submonoid.powers (r : S)), (m : S) • x ∈ Algebra.adjoin R A) by
      { exact fun _ => by simp [Submonoid.mem_powers_iff] }]
    refine IsLocalization.exists_smul_mem_of_mem_adjoin
      (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) ?_ ?_ ?_
    · intro x hx
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inl ⟨_, ⟨r, rfl⟩, _, ⟨s.mem_attach r, rfl⟩, hx⟩)
    · rw [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff]
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inr r.2)
    · rw [ht]; trivial
#align ring_hom.finite_type_of_localization_span_target RingHom.finiteType_ofLocalizationSpanTarget

theorem finiteType_is_local : PropertyIsLocal @FiniteType :=
  ⟨localization_finiteType, finiteType_ofLocalizationSpanTarget, finiteType_stableUnderComposition,
    finiteType_holdsForLocalizationAway⟩
#align ring_hom.finite_type_is_local RingHom.finiteType_is_local

theorem finiteType_respectsIso : RingHom.RespectsIso @RingHom.FiniteType :=
  RingHom.finiteType_is_local.respectsIso
#align ring_hom.finite_type_respects_iso RingHom.finiteType_respectsIso

end RingHom
