/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Localization

/-!
# The category of sheaves of modules as a localization of presheaves of modules

Similarly as the category of sheaves with values in a category identify to
a localization of the category of presheaves with respect to those morphisms
which become isomorphisms after sheafification
(see the file `Mathlib/CategoryTheory/Sites/Localization.lean`), we show that
the sheafification functor from presheaves of modules to sheaves of modules
is a localization functor.

-/

@[expose] public section

universe v u v' u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace PresheafOfModules

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.val)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J AddCommGrpCat.{v}]

open MorphismProperty in
lemma inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms :
    J.W.inverseImage (toPresheaf R₀) = (isomorphisms _).inverseImage (sheafification α) := by
  rw [J.W_eq_inverseImage_isomorphisms]
  ext P Q f
  simp only [inverseImage_iff, isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  exact (isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (sheafificationCompToSheaf.{v} α)).app (Arrow.mk f))

instance : (sheafification.{v} α).IsLocalization (J.W.inverseImage (toPresheaf R₀)) := by
  rw [inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α]
  exact (sheafificationAdjunction.{v} α).isLocalization

end PresheafOfModules
