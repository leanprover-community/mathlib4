/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Preradicals

A **preradical** on an abelian category `C` is a monomorphism in the functor category `C ⥤ C`
with codomain `𝟭 C`, i.e. an element of `MonoOver (𝟭 C)`.

## Main definitions

* `Preradical C`: The type of preradicals on `C`.
* `Preradical.r`: The underlying endofunctor of a `Preradical`.
* `Preradical.ι`: The structure morphism of a `Preradical`.
* `Preradical.IsIdempotent`: The predicate expressing idempotence.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

@[expose] public section

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (C) in
/-- A preradical on an abelian category `C` is a monomorphism in `C ⥤ C` with codomain `𝟭 C`. -/
abbrev Preradical := MonoOver (𝟭 C)

namespace Preradical

variable (Φ : Preradical C)

/-- The underlying endofunctor `r : C ⥤ C` of a preradical `Φ`. -/
abbrev r : C ⥤ C := Φ.obj.left

/-- The structure morphism `Φ.r ⟶ 𝟭 C` of a preradical `Φ`. -/
abbrev ι : Φ.r ⟶ 𝟭 C := Φ.obj.hom

@[simp]
lemma r_map_ι_app (X : C) : Φ.r.map (Φ.ι.app X) = Φ.ι.app (Φ.r.obj X) := by
  rw [← cancel_mono (Φ.ι.app X)]
  exact Φ.ι.naturality (Φ.ι.app X)

/-- A preradical `Φ` is idempotent if `Φ.r ⋙ Φ.r ≅ Φ.r`. -/
class IsIdempotent : Prop where
  isIso_whiskerLeft_r_ι : IsIso (Functor.whiskerLeft Φ.r Φ.ι)

attribute [instance] IsIdempotent.isIso_whiskerLeft_r_ι

instance [Φ.IsIdempotent] (X : C) :
    IsIso (Φ.ι.app (Φ.r.obj X)) :=
  inferInstanceAs (IsIso ((Functor.whiskerLeft Φ.r Φ.ι).app X))

instance [Φ.IsIdempotent] (X : C) :
    IsIso (Φ.r.map (Φ.ι.app X)) := by
  rw [r_map_ι_app]
  infer_instance

end Preradical

end CategoryTheory.Abelian
