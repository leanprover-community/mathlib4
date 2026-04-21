/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Transport
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Left resolutions which preserve the zero object

The structure `LeftResolution` allows to define a functorial
resolution of an object (see `LeftResolution.chainComplexFunctor`
in the file `Mathlib/Algebra/Homology/LeftResolution/Basic.lean`). In
order to extend this resolution to complexes, we not only
need the functoriality but also that zero morphisms
are sent to zero. In this file, given `ι : C ⥤ A`,
we extend `Λ : LeftResolution ι` to idempotent completions as
`Λ.karoubi : LeftResolution ((functorExtension₂ C A).obj ι)`, and
when both `C` and `A` are idempotent complete, we define
`Λ.reduced : LeftResolution ι` in such a way that the
functor `Λ.reduced.F : A ⥤ C` preserves zero morphisms.

For example, if `A := ModuleCat R` and `C` is the full subcategory
of flat `R`-modules, we may first define `Λ` by using the
functor which sends an `R`-module `M` to the free `R`-module
on the elements of `M`. Then, `Λ.reduced.F.obj M` will be obtained
from the free `R`-module on `M` by factoring out the direct factor
corresponding to the submodule spanned by the generator corresponding
to `0 : M` (TODO).

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Abelian

variable {A C : Type*} [Category* C] [Category* A] {ι : C ⥤ A}
  (Λ : LeftResolution ι)

open Idempotents Limits MorphismProperty

namespace LeftResolution

variable [Preadditive C] [Preadditive A] [ι.Additive]

/-- Auxiliary definition for `LeftResolution.karoubi`. -/
@[simps]
def karoubi.F' : A ⥤ Karoubi C where
  obj X := ⟨Λ.F.obj X, 𝟙 _ - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map {X Y} f := ⟨Λ.F.map f - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map_comp _ _ := by simp [← Functor.map_comp]

/-- Auxiliary definition for `LeftResolution.karoubi`. -/
@[simps!]
def karoubi.F : Karoubi A ⥤ Karoubi C := (functorExtension₁ A C).obj (karoubi.F' Λ)

instance : (karoubi.F Λ).PreservesZeroMorphisms where

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `LeftResolution.karoubi`. -/
@[simps]
def karoubi.π' : toKaroubi A ⋙ F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ toKaroubi A where
  app X := ⟨Λ.π.app X, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `(karoubi.π' Λ).app X` is a retract of `(toKaroubi _).map (Λ.π.app X)`. -/
def karoubi.retractArrow (X : A) :
    RetractArrow ((karoubi.π' Λ).app X) ((toKaroubi _).map (Λ.π.app X)) where
  i := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  r := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩ (𝟙 _)
  retract := by
    ext
    · simp [← Functor.map_comp]
    · simp

instance (X : A) : Epi ((karoubi.π' Λ).app X) :=
  of_retract (P := epimorphisms _) (karoubi.retractArrow Λ X)
    (epimorphisms.infer_property _)

/-- Auxiliary definition for `LeftResolution.karoubi`. -/
def karoubi.π : karoubi.F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ 𝟭 (Karoubi A) :=
  whiskeringLeftObjToKaroubiFullyFaithful.preimage (karoubi.π' Λ)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma karoubi.π_app_toKaroubi_obj (X : A) :
    (karoubi.π Λ).app ((toKaroubi _).obj X) = (karoubi.π' Λ).app X := by
  simp [π, whiskeringLeftObjToKaroubiFullyFaithful]

set_option backward.isDefEq.respectTransparency false in
instance (X : A) : Epi ((karoubi.π Λ).app ((toKaroubi _).obj X)) := by
  rw [karoubi.π_app_toKaroubi_obj]
  infer_instance

instance (X : Karoubi A) : Epi ((karoubi.π Λ).app X) :=
  of_retract (P := epimorphisms _) (NatTrans.retractArrowApp (karoubi.π Λ) X.retract)
    (epimorphisms.infer_property _)

/-- Given `ι : C ⥤ A`, this is the extension of `Λ : LeftResolution ι` to
`LeftResolution ((functorExtension₂ C A).obj ι)`, where
`(functorExtension₂ C A).obj ι : Karoubi C ⥤ Karoubi A` is the extension of `ι`. -/
@[simps]
noncomputable def karoubi : LeftResolution ((functorExtension₂ C A).obj ι) where
  F := karoubi.F Λ
  π := karoubi.π Λ

instance : Λ.karoubi.F.PreservesZeroMorphisms where

section

variable [IsIdempotentComplete A] [IsIdempotentComplete C]

/-- Given an additive functor `ι : C ⥤ A` between idempotent complete categories,
any `Λ : LeftResolution ι` induces a term `Λ.reduced : LeftResolution ι`
such that `Λ.reduced.F` preserves zero morphisms. -/
noncomputable def reduced : LeftResolution ι :=
  Λ.karoubi.transport (toKaroubiEquivalence A) (toKaroubiEquivalence C)
     ((karoubiUniversal₁ C A).unitIso.app _)

instance : Λ.reduced.F.PreservesZeroMorphisms := by
  dsimp [reduced, transport]
  infer_instance

end

end LeftResolution

end CategoryTheory.Abelian
