/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Order properties of star algebras

This file collects results about order properties of star algebras

## Main results

+ `NonUnitalStarAlgHom.strictMono_of_injective`: If a non-unital star algebra homomorphism is
  injective, then it is strictly monotone.
-/

variable {R A B : Type*} [CommSemiring R] [StarRing R] [NonUnitalRing A] [NonUnitalRing B]
  [Module R A] [StarRing A] [Module R B] [StarRing B] [PartialOrder A]
  [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [StarModule R B]

lemma NonUnitalStarAlgHom.strictMono_of_injective {f : A →⋆ₙₐ[R] B}
    (hf : Function.Injective f) : StrictMono f := by
  rw [strictMono_iff_map_pos]
  intro a ha
  have h₁ : 0 ≤ f a := map_nonneg f (le_of_lt ha)
  refine lt_of_le_not_le h₁ ?_
  intro h
  have h₂ : f a = f 0 := by simp [eq_of_le_of_le h h₁]
  exact (ne_of_lt ha) (hf h₂).symm

lemma NonUnitalStarAlgHom.le_iff_le_of_injective {f : A →⋆ₙₐ[R] B}
    (hf : Function.Injective f) {a b : A} : f a ≤ f b ↔ a ≤ b := by
  let φ := StarAlgEquiv.ofInjective' f hf
  let fa' : NonUnitalStarAlgHom.range f := ⟨f a, by sorry⟩
  let fb' : NonUnitalStarAlgHom.range f := ⟨f b, by sorry⟩
  --let _ : StarOrderedRing (NonUnitalStarAlgHom.range f) := inferInstance
  constructor
  case mp =>
    intro h
    have ha : a = φ.symm fa' := by sorry
    have hb : b = φ.symm fb' := by sorry
    rw [ha, hb]
    --apply OrderHomClass.mono
    sorry
  case mpr =>
    sorry
