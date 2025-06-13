/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Ring.Equiv

/-!
# Propositional typeclasses on several ring homs

This file contains three typeclasses used in the definition of (semi)linear maps:
* `RingHomId σ`, which expresses the fact that `σ₂₃ = id`
* `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`
* `RingHomInvPair σ₁₂ σ₂₁`, which states that `σ₁₂` and `σ₂₁` are inverses of each other
* `RingHomSurjective σ`, which states that `σ` is surjective

These typeclasses ensure that objects such as `σ₂₃.comp σ₁₂` never end up in the type of a
semilinear map; instead, the typeclass system directly finds the appropriate `RingHom` to use.
A typical use-case is conjugate-linear maps, i.e. when `σ = Complex.conj`; this system ensures that
composing two conjugate-linear maps is a linear map, and not a `conj.comp conj`-linear map.

Instances of these typeclasses mostly involving `RingHom.id` are also provided:
* `RingHomInvPair (RingHom.id R) (RingHom.id R)`
* `[RingHomInvPair σ₁₂ σ₂₁] : RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁)`
* `RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂`
* `RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂`
* `RingHomSurjective (RingHom.id R)`
* `[RingHomInvPair σ₁ σ₂] : RingHomSurjective σ₁`

## Implementation notes

* For the typeclass `RingHomInvPair σ₁₂ σ₂₁`, `σ₂₁` is marked as an `outParam`,
  as it must typically be found via the typeclass inference system.

* Likewise, for `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, `σ₁₃` is marked as an `outParam`,
  for the same reason.

## Tags

`RingHomCompTriple`, `RingHomInvPair`, `RingHomSurjective`
-/


variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

/-- Class that expresses that a ring homomorphism is in fact the identity. -/
-- This at first seems not very useful. However we need this when considering
-- modules over some diagram in the category of rings,
-- e.g. when defining presheaves over a presheaf of rings.
-- See `Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`.
class RingHomId {R : Type*} [Semiring R] (σ : R →+* R) : Prop where
  eq_id : σ = RingHom.id R

instance {R : Type*} [Semiring R] : RingHomId (RingHom.id R) where
  eq_id := rfl

/-- Class that expresses the fact that three ring homomorphisms form a composition triple. This is
used to handle composition of semilinear maps. -/
class RingHomCompTriple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) (σ₁₃ : outParam (R₁ →+* R₃)) :
  Prop where
  /-- The morphisms form a commutative triangle -/
  comp_eq : σ₂₃.comp σ₁₂ = σ₁₃

attribute [simp] RingHomCompTriple.comp_eq

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

namespace RingHomCompTriple

@[simp]
theorem comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x :=
  RingHom.congr_fun comp_eq x

end RingHomCompTriple

/-- Class that expresses the fact that two ring homomorphisms are inverses of each other. This is
used to handle `symm` for semilinear equivalences. -/
class RingHomInvPair (σ : R₁ →+* R₂) (σ' : outParam (R₂ →+* R₁)) : Prop where
  /-- `σ'` is a left inverse of `σ` -/
  comp_eq : σ'.comp σ = RingHom.id R₁
  /-- `σ'` is a left inverse of `σ'` -/
  comp_eq₂ : σ.comp σ' = RingHom.id R₂

variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

namespace RingHomInvPair

variable [RingHomInvPair σ σ']

theorem comp_apply_eq {x : R₁} : σ' (σ x) = x := by
  rw [← RingHom.comp_apply, comp_eq]
  simp

theorem comp_apply_eq₂ {x : R₂} : σ (σ' x) = x := by
  rw [← RingHom.comp_apply, comp_eq₂]
  simp

instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=
  ⟨rfl, rfl⟩

instance triples {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁) :=
  ⟨by simp only [comp_eq]⟩

instance triples₂ {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₂₁ σ₁₂ (RingHom.id R₂) :=
  ⟨by simp only [comp_eq₂]⟩

/-- Construct a `RingHomInvPair` from both directions of a ring equiv.

This is not an instance, as for equivalences that are involutions, a better instance
would be `RingHomInvPair e e`. Indeed, this declaration is not currently used in mathlib.
-/
theorem of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ →+* R₂) ↑e.symm :=
  ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

/--
Swap the direction of a `RingHomInvPair`. This is not an instance as it would loop, and better
instances are often available and may often be preferable to using this one. Indeed, this
declaration is not currently used in mathlib.
-/
theorem symm (σ₁₂ : R₁ →+* R₂) (σ₂₁ : R₂ →+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomInvPair σ₂₁ σ₁₂ :=
  ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩

end RingHomInvPair

namespace RingHomCompTriple

instance ids : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂ :=
  ⟨by
    ext
    simp⟩

instance right_ids : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂ :=
  ⟨by
    ext
    simp⟩

end RingHomCompTriple

/-- Class expressing the fact that a `RingHom` is surjective. This is needed in the context
of semilinear maps, where some lemmas require this. -/
class RingHomSurjective (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is surjective -/
  is_surjective : Function.Surjective σ

theorem RingHom.surjective (σ : R₁ →+* R₂) [t : RingHomSurjective σ] : Function.Surjective σ :=
  t.is_surjective

namespace RingHomSurjective

instance (priority := 100) invPair {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁} [RingHomInvPair σ₁ σ₂] :
    RingHomSurjective σ₁ :=
  ⟨fun x => ⟨σ₂ x, RingHomInvPair.comp_apply_eq₂⟩⟩

instance ids : RingHomSurjective (RingHom.id R₁) :=
  ⟨is_surjective⟩

/-- This cannot be an instance as there is no way to infer `σ₁₂` and `σ₂₃`. -/
theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
    RingHomSurjective σ₁₃ :=
  { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }

instance (σ : R₁ ≃+* R₂) : RingHomSurjective (σ : R₁ →+* R₂) := ⟨σ.surjective⟩

end RingHomSurjective
