/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.LeftResolutions.Transport
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Left resolutions which preserve the zero object

The structure `LeftResolutions` allows to define a functorial
resolution of an object (see `LeftResolutions.chainComplexFunctor`
in the file `Algebra.Homology.LeftResolutions.Basic`). In
order to extend this resolution to complexes, we not only
need the functoriality but also that zero morphisms
are sent to zero. In this file, given `ι : C ⥤ A`,
we extend `Λ : LeftResolutions ι` to idempotent completions as
`Λ.karoubi : LeftResolutions ((functorExtension₂ C A).obj ι)`, and
when both `C` and `A` are idempotent complete, we define
`Λ.reduced : LeftResolutions ι` in such a way that the
functor `Λ.reduced.F : A ⥤ C` preserves zero morphisms.

For example, if `A := ModuleCat R` and `C` is the full subcategory
of flat `R`-modules, we may first define `Λ` by using the
functor which sends a `R`-module `M` to the free `R`-module
on the elements of `M`. Then, `Λ.reduced.F.obj M` will be obtained
from the free `R`-module on `M` by factoring out the direct factor
corresponding to the submodule spanned by the generator corresponding
to `0 : M` (TODO).

-/

namespace CategoryTheory

namespace NatTrans

variable {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
  (τ : F ⟶ G) {X Y : C} (h : Retract X Y)

-- to be moved
/-- If `X` is a retract of `Y`, then for any natural transformation `τ`,
the natural transformation `τ.app X` is a retract of `τ.app Y`. -/
@[simps]
def retractArrowApp : RetractArrow (τ.app X) (τ.app Y) where
  i := Arrow.homMk (F.map h.i) (G.map h.i) (by simp)
  r := Arrow.homMk (F.map h.r) (G.map h.r) (by simp)
  retract := by ext <;> simp [← Functor.map_comp]

end NatTrans

-- to be moved
namespace Idempotents

variable {C D : Type*} [Category C] [Category D]

/-- If `X : Karoubi C`, then `X` is a retract of `((toKaroubi C).obj X.X)`. -/
@[simps]
def Karoubi.retract (X : Karoubi C) : Retract X ((toKaroubi C).obj X.X) where
  i := ⟨X.p, by simp⟩
  r := ⟨X.p, by simp⟩

/-- The precomposition of functors with `toKaroubi C` is fully faithful. -/
def whiskeringLeftObjToKaroubiFullyFaithful :
    ((Functor.whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)).FullyFaithful where
  preimage {F G} τ :=
    { app P := F.map P.decompId_i ≫ τ.app P.X ≫ G.map P.decompId_p
      naturality X Y f := by
        dsimp at τ ⊢
        have h₁ : f ≫ Y.decompId_i = X.decompId_i ≫ (toKaroubi C).map f.f := by aesop
        have h₂ := τ.naturality f.f
        have h₃ : X.decompId_p ≫ f = (toKaroubi C).map f.f ≫ Y.decompId_p := by aesop
        dsimp at h₂
        rw [Category.assoc, Category.assoc, ← F.map_comp_assoc,
          h₁, F.map_comp_assoc, reassoc_of% h₂, ← G.map_comp, ← h₃, G.map_comp] }
  preimage_map {F G} τ := by ext X; exact (natTrans_eq _ _).symm
  map_preimage {F G} τ := by
    ext X
    dsimp
    rw [Karoubi.decompId_i_toKaroubi, Karoubi.decompId_p_toKaroubi,
      Functor.map_id, Category.id_comp]
    change _ ≫ G.map (𝟙 _) = _
    simp

instance : (toKaroubi C).PreservesEpimorphisms where
  preserves {X Y} f _ := ⟨fun {Z} g h eq ↦ by
    ext
    rw [← cancel_epi f]
    simpa using eq⟩

instance : (toKaroubi C).PreservesMonomorphisms where
  preserves {X Y} f _ := ⟨fun {Z} g h eq ↦ by
    ext
    rw [← cancel_mono f]
    simpa using eq⟩

end Idempotents

end CategoryTheory

namespace CategoryTheory.Abelian

variable {A C : Type*} [Category C] [Category A] {ι : C ⥤ A}
  (Λ : LeftResolutions ι)

open Idempotents Limits MorphismProperty

namespace LeftResolutions

variable [Preadditive C] [Preadditive A] [ι.Additive]

/-- Auxiliary definition for `LeftResolutions.karoubi`. -/
@[simps]
def karoubi.F' : A ⥤ Karoubi C where
  obj X := ⟨Λ.F.obj X, 𝟙 _ - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map {X Y} f := ⟨Λ.F.map f - Λ.F.map 0, by simp [← Functor.map_comp]⟩
  map_comp _ _ := by simp [← Functor.map_comp]

/-- Auxiliary definition for `LeftResolutions.karoubi`. -/
@[simps!]
def karoubi.F : Karoubi A ⥤ Karoubi C := (functorExtension₁ A C).obj (karoubi.F' Λ)

instance : (karoubi.F Λ).PreservesZeroMorphisms where

/-- Auxiliary definition for `LeftResolutions.karoubi`. -/
@[simps]
def karoubi.π' : toKaroubi A ⋙ F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ toKaroubi A where
  app X := ⟨Λ.π.app X, by simp⟩

instance (X : A) : Epi ((karoubi.π' Λ).app X) := by
  have h : RetractArrow ((karoubi.π' Λ).app X) ((toKaroubi _).map (Λ.π.app X)) :=
    { i := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩
            (𝟙 _) (by simp)
      r := Arrow.homMk ⟨ι.map ((karoubi.F' Λ).obj X).p, by simp [← Functor.map_comp]⟩
            (𝟙 _) (by simp)
      retract := by
        ext
        · simp [← Functor.map_comp]
        · simp }
  exact of_retract (P := epimorphisms _) h (epimorphisms.infer_property _)

/-- Auxiliary definition for `LeftResolutions.karoubi`. -/
def karoubi.π : karoubi.F Λ ⋙ (functorExtension₂ C A).obj ι ⟶ 𝟭 (Karoubi A) :=
  whiskeringLeftObjToKaroubiFullyFaithful.preimage (karoubi.π' Λ)

@[simp]
lemma karoubi.π_app_toKaroubi_obj (X : A) :
    (karoubi.π Λ).app ((toKaroubi _).obj X) = (karoubi.π' Λ).app X :=
  NatTrans.congr_app (whiskeringLeftObjToKaroubiFullyFaithful.map_preimage
    (Y := 𝟭 _) (karoubi.π' Λ)) X

instance (X : A) : Epi ((karoubi.π Λ).app ((toKaroubi _).obj X)) := by
  rw [karoubi.π_app_toKaroubi_obj]
  infer_instance

instance (X : Karoubi A) : Epi ((karoubi.π Λ).app X) :=
  of_retract (P := epimorphisms _) (NatTrans.retractArrowApp (karoubi.π Λ) X.retract)
    (epimorphisms.infer_property _)

/-- Given `ι : C ⥤ A`, this is the extension of `Λ : LeftResolutions ι` to
`LeftResolutions ((functorExtension₂ C A).obj ι)`, where
`(functorExtension₂ C A).obj ι : Karoubi C ⥤ Karoubi A` is the extension of `ι`. -/
@[simps]
noncomputable def karoubi : LeftResolutions ((functorExtension₂ C A).obj ι) where
  F := karoubi.F Λ
  π := karoubi.π Λ

instance : Λ.karoubi.F.PreservesZeroMorphisms where

section

variable [IsIdempotentComplete A] [IsIdempotentComplete C]

/-- Given an additive functor `ι : C ⥤ A` between idempotent complete categories,
any `Λ : LeftResolutions ι` induces a term `Λ.reduced : LeftResolutions ι`
such that `Λ.reduced.F` preserves zero morphisms. -/
noncomputable def reduced : LeftResolutions ι :=
  Λ.karoubi.transport (toKaroubiEquivalence A) (toKaroubiEquivalence C)
     ((karoubiUniversal₁ C A).unitIso.app _)

instance : Λ.reduced.F.PreservesZeroMorphisms := by
  dsimp [reduced, transport]
  infer_instance

end

end LeftResolutions

end CategoryTheory.Abelian
