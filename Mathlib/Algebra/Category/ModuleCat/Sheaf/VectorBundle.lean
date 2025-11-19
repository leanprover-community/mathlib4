/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoversTop

/-! # Vector Bundles

A sheaf of modules is a vector bundle if it is locally isomorphic to a free sheaf.

-/

universe u v

namespace SheafOfModules

open CategoryTheory Limits

variable {C : Type u} [Category.{v, u} C]
variable {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat} (M : SheafOfModules R)
variable [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrp)]
variable [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrp]
variable [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrp]

/-- A vector bundle is a sheaf of modules that is locally isomorphic to
a free sheaf. -/
structure VectorBundleData (M : SheafOfModules.{v} R) where
  /-- The index type for the open cover on which the vector bundle is free. -/
  OpensIndex : Type u
  /-- The indexed family of opens on which the vector bundle is free. -/
  opens : OpensIndex → C
  /-- The indexed family of types that index local bases for the vector bundle. -/
  BasisIndex : OpensIndex → Type v
  /-- The indexed family of opens covers the base. -/
  coversTop : J.CoversTop opens
  /-- The restriction of the vector bundle to one of the opens is free. -/
  locallyFree : ∀ i, (M.over <| opens i) ≅ SheafOfModules.free (BasisIndex i)

--TODO: construct a `QuasiCoherentData` from a `VectorBundle` data.

/-- A class for vector bundles of constant finite rank. -/
class IsVectorBundle (M : SheafOfModules R) where
  /-- The predicate that a sheaf of modules is locally free. -/
  exists_vector_bundle_data : Nonempty  M.VectorBundleData

-- TODO: prove that vector bundles are quasicoherent

end SheafOfModules
