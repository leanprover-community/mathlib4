/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso
import Mathlib.Data.Finset.Lattice.Fold

/-!
# `Finset.sup` in a group with zero
-/

namespace Finset
variable {ι M₀ G₀ : Type*}

section MonoidWithZero
variable [MonoidWithZero M₀] {s : Finset ι} {a b : ι → M₀}

lemma sup_mul_le_mul_sup_of_nonneg [SemilatticeSup M₀] [OrderBot M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) : s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun _i hi ↦
    mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)

lemma mul_inf_le_inf_mul_of_nonneg [SemilatticeInf M₀] [OrderTop M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) : s.inf a * s.inf b ≤ s.inf (a * b) :=
  Finset.le_inf fun i hi ↦ mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)

lemma sup'_mul_le_mul_sup'_of_nonneg [SemilatticeSup M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hs) :
    s.sup' hs (a * b) ≤ s.sup' hs a * s.sup' hs b :=
  sup'_le _ _ fun _i hi ↦
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)

lemma inf'_mul_le_mul_inf'_of_nonneg [SemilatticeInf M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hs) :
    s.inf' hs a * s.inf' hs b ≤ s.inf' hs (a * b) :=
  le_inf' _ _ fun _i hi ↦ mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀] [SemilatticeSup G₀] {s : Finset ι} {a : G₀}

lemma sup'_mul₀ [MulPosReflectLT G₀] (ha : 0 < a) (f : ι → G₀) (s : Finset ι) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := map_finset_sup' (OrderIso.mulRight₀ _ ha) hs f

set_option linter.docPrime false in
lemma mul₀_sup' [PosMulReflectLT G₀] (ha : 0 < a) (f : ι → G₀) (s : Finset ι) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := map_finset_sup' (OrderIso.mulLeft₀ _ ha) hs f

lemma sup'_div₀ [MulPosReflectLT G₀] (ha : 0 < a) (f : ι → G₀) (s : Finset ι) (hs) :
    s.sup' hs f / a = s.sup' hs fun i ↦ f i / a :=
  map_finset_sup' (OrderIso.divRight₀ _ ha) hs f

end GroupWithZero

lemma sup_div₀ [LinearOrderedCommGroupWithZero G₀] [OrderBot G₀] {a : G₀} (ha : 0 < a)
    (s : Finset ι) (f : ι → G₀) : s.sup f / a = s.sup fun i ↦ f i / a := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [← show (0 : G₀) = ⊥ from bot_unique zero_le']
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, sup'_div₀ (ha := ha)]

end Finset
