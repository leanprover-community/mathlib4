/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Transcendental separable extensions
-/

universe u v

@[expose] public section

open TensorProduct

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

class Algebra.IsSeparablyGenerated : Prop where
  isSeparable' : ∃ (ι : Type v) (f : ι → K),
    IsTranscendenceBasis k f ∧
    Algebra.IsSeparable (Algebra.adjoin k (Set.range f)) K

class Algebra.IsTranscendentalSeparable : Prop where
  forall_isSeparablyGenerated : ∀ (A' : IntermediateField k K),
    Algebra.EssFiniteType k A' → Algebra.IsSeparablyGenerated k A'

end

set_option backward.isDefEq.respectTransparency false in
/-- If `R ⊗[k] S` is nonreduced, then this already occurs on finitely generated `k`-subalgebras
of `R` and `S`. -/
lemma exists_subalgebra_fg_of_not_isReduced_tensorProduct
    (k R S : Type*) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ R' : Subalgebra k R, ∃ S' : Subalgebra k S, R'.FG ∧ S'.FG ∧ ¬ IsReduced (R' ⊗[k] S') := by
  obtain ⟨z, hz_ne, ⟨n, hn⟩⟩ := exists_isNilpotent_of_not_isReduced h
  rcases TensorProduct.Algebra.exists_of_fg z with ⟨R', fgR, ⟨y, hy⟩⟩
  rcases TensorProduct.Algebra.exists_of_fg ((TensorProduct.comm k _ _) y) with ⟨S', fgS, ⟨x, hx⟩⟩
  use R', S', fgR, fgS
  rw [isReduced_iff, not_forall₂]
  use (TensorProduct.comm k _ _) x
  refine exists_prop.mpr ⟨?_, ?_⟩
  · use n
    have hx' : (Algebra.TensorProduct.rTensor _ S'.val) x =
      (Algebra.TensorProduct.comm k _ _) y := hx
    have : x ^ n = 0 := by
      rw [← map_eq_zero_iff (Algebra.TensorProduct.rTensor R' S'.val)
        (Module.Flat.rTensor_preserves_injective_linearMap S'.val.toLinearMap
        Subtype.val_injective), map_pow, hx', ← map_pow,
        map_eq_zero_iff _ (AlgEquiv.injective _), ← map_eq_zero_iff
        (Algebra.TensorProduct.rTensor S R'.val) (Module.Flat.rTensor_preserves_injective_linearMap
        R'.val.toLinearMap Subtype.val_injective), map_pow, ← hn, ← hy]
      rfl
    rwa [← map_eq_zero_iff (Algebra.TensorProduct.comm k _ _) (AlgEquiv.injective _), map_pow]
      at this
  · rw [LinearEquiv.map_eq_zero_iff]
    by_contra eq0
    rw [eq0, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at hx
    simp [hx, map_zero, eq_comm, hz_ne] at hy

lemma tensorProduct_of_isSeparablyGenerated {k : Type*} [Field k]
    {S : Type*} [CommRing S] [IsReduced S] [Algebra k S] {K : Type*} [Field K] [Algebra k K] :
    IsReduced (TensorProduct k K S) := by
  sorry

lemma Algebra.isTranscendentalSeparable_of_perfectField {k : Type*} [Field k] [PerfectField k]
    {K : Type*} [Field K] [Algebra k K] : Algebra.IsTranscendentalSeparable k K := by
  sorry
