/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!

# Open immersions

A morphism is an open immersion if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `AlgebraicGeometry/OpenImmersion`, and we provide the
remaining theorems analogous to other lemmas in `AlgebraicGeometry/Morphisms/*`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

theorem isOpenImmersion_iff_stalk {f : X ⟶ Y} : IsOpenImmersion f ↔
    IsOpenEmbedding f.base ∧ ∀ x, IsIso (f.stalkMap x) := by
  constructor
  · intro h; exact ⟨h.1, inferInstance⟩
  · rintro ⟨h₁, h₂⟩; exact IsOpenImmersion.of_stalk_iso f h₁

theorem isOpenImmersion_eq_inf :
    @IsOpenImmersion = (topologically IsOpenEmbedding) ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  ext
  exact isOpenImmersion_iff_stalk.trans
    (and_congr Iff.rfl (forall_congr' fun x ↦ ConcreteCategory.isIso_iff_bijective _))

instance : IsLocalAtTarget (stalkwise (fun f ↦ Function.Bijective f)) := by
  apply stalkwiseIsLocalAtTarget_of_respectsIso
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  convert (inferInstanceAs (MorphismProperty.isomorphisms CommRingCat).RespectsIso)
  ext
  -- Regression in https://github.com/leanprover-community/mathlib4/pull/17583: have to specify C explicitly below.
  exact (ConcreteCategory.isIso_iff_bijective (C := CommRingCat) _).symm

instance isOpenImmersion_isLocalAtTarget : IsLocalAtTarget @IsOpenImmersion :=
  isOpenImmersion_eq_inf ▸ inferInstance

end AlgebraicGeometry
