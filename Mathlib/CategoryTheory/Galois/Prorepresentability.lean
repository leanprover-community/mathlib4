/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Limits.FunctorCategory

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to the colimit of `X ⋙ coyoneda`.

## Main definitions

- `PointedGaloisObject`: the category of pointed Galois objects
- `PointedGaloisObject.cocone`: a cocone on `(PointedGaloisObject.incl F).op ≫ coyoneda` with
  point `F ⋙ FintypeCat.incl`.
- `autGaloisSystem`: the system of automorphism groups indexed by the pointed Galois objects.

## Main results

- `PointedGaloisObject.isColimit`: the cocone `PointedGaloisObject.cocone` is a colimit cocone.

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]

/-- A pointed Galois object is a Galois object with a fixed point of its fiber. -/
structure PointedGaloisObject : Type (max u₁ u₂) where
  /-- The underlying object of `C`. -/
  obj : C
  /-- An element of the fiber of `obj`. -/
  pt : F.obj obj
  /-- `obj` is Galois. -/
  isGalois : IsGalois obj := by infer_instance

namespace PointedGaloisObject

attribute [instance] isGalois

instance (X : PointedGaloisObject F) : CoeDep (PointedGaloisObject F) X C where
  coe := X.obj

variable {F} in
/-- The type of homomorphisms between two pointed Galois objects. This is a homomorphism
of the underlying objects of `C` that maps the distinguished points to each other. -/
@[ext]
structure Hom (A B : PointedGaloisObject F) where
  /-- The underlying homomorphism of `C`. -/
  val : A.obj ⟶ B.obj
  /-- The distinguished point of `A` is mapped to the distinguished point of `B`. -/
  comp : F.map val A.pt = B.pt := by simp

attribute [simp] Hom.comp

/-- The category of pointed Galois objects. -/
instance : Category.{u₂} (PointedGaloisObject F) where
  Hom A B := Hom A B
  id A := { val := 𝟙 (A : C) }
  comp {A B C} f g := { val := f.val ≫ g.val }

instance {A B : PointedGaloisObject F} : Coe (Hom A B) (A.obj ⟶ B.obj) where
  coe f := f.val

variable {F}

@[ext]
lemma hom_ext {A B : PointedGaloisObject F} {f g : A ⟶ B} (h : f.val = g.val) : f = g :=
  Hom.ext f g h

@[simp]
lemma id_val (A : PointedGaloisObject F) : 𝟙 A = 𝟙 A.obj :=
  rfl

@[simp, reassoc]
lemma comp_val {A B C : PointedGaloisObject F} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

variable (F)

/-- The category of pointed Galois objects is cofiltered. -/
instance : IsCofilteredOrEmpty (PointedGaloisObject F) where
  cone_objs := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ↦ by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F (A ⨯ B)
      <| (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨Z, z, hgal⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    · simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, hf⟩ ⟨g, hg⟩ ↦ by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_hom_from_galois_of_fiber F A a
    refine ⟨⟨Z, z, hgal⟩, ⟨h, hhz⟩, hom_ext ?_⟩
    apply evaluation_injective_of_isConnected F Z B z
    simp [hhz, hf, hg]

/-- The canonical functor from pointed Galois objects to `C`. -/
def incl : PointedGaloisObject F ⥤ C where
  obj := fun A ↦ A
  map := fun ⟨f, _⟩ ↦ f

@[simp]
lemma incl_obj (A : PointedGaloisObject F) : (incl F).obj A = A :=
  rfl

@[simp]
lemma incl_map {A B : PointedGaloisObject F} (f : A ⟶ B) : (incl F).map f = f.val :=
  rfl

/-- `F ⋙ FintypeCat.incl` as a cocone over `(can F).op ⋙ coyoneda`.
This is a colimit cocone (see `PreGaloisCategory.isColimìt`) -/
def cocone : Cocone ((incl F).op ⋙ coyoneda) where
  pt := F ⋙ FintypeCat.incl
  ι := {
    app := fun ⟨A, a, _⟩ ↦ { app := fun X (f : (A : C) ⟶ X) ↦ F.map f a }
    naturality := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, (hf : F.map f b = a)⟩ ↦ by
      ext Y (g : (A : C) ⟶ Y)
      suffices h : F.map g (F.map f b) = F.map g a by simpa
      rw [hf]
  }

@[simp]
lemma cocone_app (A : PointedGaloisObject F) (B : C) (f : (A : C) ⟶ B) :
    ((cocone F).ι.app ⟨A⟩).app B f = F.map f A.pt :=
  rfl

/-- `cocone F` is a colimit cocone, i.e. `F` is pro-represented by `incl F`. -/
noncomputable def isColimit : IsColimit (cocone F) := by
  refine evaluationJointlyReflectsColimits _ (fun X ↦ ?_)
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : F.obj X)
    obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
    refine ⟨⟨Z, z, hgal⟩, f ≫ i, ?_⟩
    simp only [mapCocone_ι_app, evaluation_obj_map, cocone_app, map_comp,
      ← h1, FintypeCat.comp_apply, hfz]
  · intro ⟨A, a, _⟩ ⟨B, b, _⟩ (u : (A : C) ⟶ X) (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
    obtain ⟨⟨Z, z, _⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
      IsFilteredOrEmpty.cocone_objs (C := (PointedGaloisObject F)ᵒᵖ)
        ⟨{ obj := A, pt := a}⟩ ⟨{obj := B, pt := b}⟩
    refine ⟨⟨{ obj := Z, pt := z }⟩, ⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
    apply evaluation_injective_of_isConnected F Z X z
    change F.map (f ≫ u) z = F.map (g ≫ v) z
    rw [map_comp, FintypeCat.comp_apply, hf, map_comp, FintypeCat.comp_apply, hg, h]

instance : HasColimit ((incl F).op ⋙ coyoneda) where
  exists_colimit := ⟨cocone F, isColimit F⟩

end PointedGaloisObject

open PointedGaloisObject

/-- The diagram sending each pointed Galois object to its automorphism group
as an object of `C`. -/
noncomputable def autGaloisSystem : PointedGaloisObject F ⥤ GroupCat.{u₂} where
  obj := fun A ↦ GroupCat.of <| Aut (A : C)
  map := fun {A B} f ↦ (autMapHom f : Aut (A : C) →* Aut (B : C))
  map_id := fun A ↦ by
    ext (σ : Aut A.obj)
    simp
  map_comp {A B C} f g := by
    ext (σ : Aut A.obj)
    simp

end PreGaloisCategory

end CategoryTheory
