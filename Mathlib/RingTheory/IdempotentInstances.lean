/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Idempotents

/-! # Instances on corners -/

@[expose] public section

variable {R A : Type*} [CommSemiring R]
  [CommSemiring A] [Algebra R A] {e : A} (he : IsIdempotentElem e)

instance [Module.Projective R A] : Module.Projective R he.Corner :=
  .of_split ⟨⟨Subtype.val, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    (IsScalarTower.toAlgHom _ A _).toLinearMap
    (LinearMap.ext fun a ↦ Subtype.ext ((Subsemigroup.mem_corner_iff he).mp a.2).2)

instance [Module.Flat R A] : Module.Flat R he.Corner :=
  .trans R A _

instance [Module.Finite R A] : Module.Finite R he.Corner :=
  .of_surjective (IsScalarTower.toAlgHom _ _ _).toLinearMap he.algebraMap_corner_surjective
#min_imports
