/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.CoversTop

/-!
# Quasicoherent sheaves

A sheaf of modules admits a global presentation if it is the cokernel of
a morphism between free modules (i.e. coproducts of `SheafOfModules.unit`).

A sheaf of modules is said to be quasi-coherent if, locally, it admits a global presentation.

-/

universe u v' u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

-- to be moved...
/-- The sheaf on `J.over X` induced by a sheaf on `J`. -/
abbrev CategoryTheory.Sheaf.over {A : Type*} [Category A] (F : Sheaf J A) (X : C) :
    Sheaf (J.over X) A :=
  ((Over.forget X).sheafPushforwardContinuous A (J.over X) J).obj F

variable {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

variable (M : SheafOfModules.{u} R)

section

variable [HasWeakSheafify J AddCommGroupCat.{u}] [J.WEqualsLocallyBijective AddCommGroupCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGroupCat.{u})]
  -- note: such `HasSheafCompose` assumptions should always hold because this
  -- `forget₂` functor preserves all limits, regardless of universes,
  -- similarly as it was done in the lemma `forget₂GroupPreservesLimitsOfShape` in
  -- `Algebra.Category.GroupCat.Limits`

/-- Given a family `s : I → M.sections` of sections of a sheaf of modules, this is the
corresponding morphism from a coproduct of copies of `unit` to `M`. -/
noncomputable abbrev homOfSections {I : Type u} (s : I → M.sections) :
    ∐ (fun (_ : I) ↦ unit R) ⟶ M :=
  Sigma.desc (fun i ↦ M.unitHomEquiv.symm (s i))

/-- The type of sections which generate a sheaf of modules. -/
structure GeneratingSections where
  /-- the index type for the sections -/
  I : Type u
  /-- a family of sections which generate the sheaf of modules -/
  s : I → M.sections
  isLocallySurjective : Sheaf.IsLocallySurjective ((toSheaf _).map (M.homOfSections s))

/-- A global presentation of a sheaf of modules `M` consists of a family
of sections `s` which generate `M`, and a family of sections which generate
the kernel of the morphism `M.homOfSections s`. -/
structure GlobalPresentation where
  /-- generators -/
  generators : M.GeneratingSections
  /-- relations -/
  relations : (kernel (M.homOfSections generators.s)).GeneratingSections

/-- A sheaf of modules `M` has a global presentation if it identifies to the cokernel
of a morphism between coproducts of copies of `unit`. -/
class HasGlobalPresentation : Prop where
  nonempty_globalPresentation : Nonempty M.GlobalPresentation

end

-- should be moved to `PushforwardContinuous.lean`
/-- Given `M : SheafOfModules R` and `X : C`, this is the restriction of `M`
over the sheaf of rings `R.over X` on the category `Over X`. -/
noncomputable abbrev over (X : C) : SheafOfModules.{u} (R.over X) :=
  (pushforward.{u} (𝟙 _)).obj M

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGroupCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGroupCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGroupCat.{u}]

/-- This structure contains the data of a family of objects `X i` which cover
the terminal object, and such that for any `i`, the restriction `M.over (X i)`
has a global presentation. -/
structure QuasicoherentData where
  /-- the index type of the covering -/
  I : Type u
  /-- a covering family of objects over which the sheaf has a global presentation. -/
  X : I → C
  coversTop : J.CoversTop X
  hasGlobalPresentation (i : I) : (M.over (X i)).HasGlobalPresentation

/-- Type-class expressing that a sheaf of modules is quasi-coherent. -/
class IsQuasicoherent : Prop where
  nonempty_quasicoherentData : Nonempty M.QuasicoherentData

end SheafOfModules
