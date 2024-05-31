/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Finset.Lattice

/-!
# Algebraic properties of finitary supremum
-/

namespace Finset
variable {ι R : Type*} [LinearOrderedSemiring R] {a b : ι → R}

theorem sup_mul_le_mul_sup_of_nonneg [OrderBot R] (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) : s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun _i hi ↦
    mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)
#align finset.sup_mul_le_mul_sup_of_nonneg Finset.sup_mul_le_mul_sup_of_nonneg

theorem mul_inf_le_inf_mul_of_nonneg [OrderTop R] (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) : s.inf a * s.inf b ≤ s.inf (a * b) :=
  Finset.le_inf fun i hi ↦ mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)
#align finset.mul_inf_le_inf_mul_of_nonneg Finset.mul_inf_le_inf_mul_of_nonneg

theorem sup'_mul_le_mul_sup'_of_nonneg (s : Finset ι) (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) : s.sup' H (a * b) ≤ s.sup' H a * s.sup' H b :=
  (sup'_le _ _) fun _i hi ↦
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)
#align finset.sup'_mul_le_mul_sup'_of_nonneg Finset.sup'_mul_le_mul_sup'_of_nonneg

theorem inf'_mul_le_mul_inf'_of_nonneg (s : Finset ι) (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) : s.inf' H a * s.inf' H b ≤ s.inf' H (a * b) :=
  (le_inf' _ _) fun _i hi ↦ mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)
#align finset.inf'_mul_le_mul_inf'_of_nonneg Finset.inf'_mul_le_mul_inf'_of_nonneg

end Finset
