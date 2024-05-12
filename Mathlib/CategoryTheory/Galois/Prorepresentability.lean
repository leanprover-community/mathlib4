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
`X : I ⥤ C` such that `F` is naturally isomorphic to `X ⋙ coyoneda`.

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
structure Hom (A B : PointedGaloisObject F) where
  /-- The underlying homomorphism of `C`. -/
  val : A.obj ⟶ B.obj
  /-- The distinguished point of `A` is mapped to the distinguished point of `B`. -/
  comp : F.map val A.pt = B.pt

/-- The category of pointed Galois objects. -/
instance : Category.{u₂} (PointedGaloisObject F) where
  Hom A B := Hom A B
  id A := ⟨𝟙 (A : C), by simp⟩
  comp {A B C} f g := by
    refine ⟨f.val ≫ g.val, ?_⟩
    simp only [F.map_comp, FintypeCat.comp_apply, f.comp, g.comp]

instance {A B : PointedGaloisObject F} : Coe (Hom A B) (A.obj ⟶ B.obj) where
  coe f := f.val

variable {F}

@[ext]
lemma Hom.ext {A B : PointedGaloisObject F} {f g : A ⟶ B} (_ : f.val = g.val) : f = g :=
  match f, g with | ⟨_, _⟩, ⟨_, _⟩ => by congr

@[simp]
lemma Hom.map_point {A B : PointedGaloisObject F} (f : A ⟶ B) :
    F.map f A.pt = B.pt :=
  f.comp

@[simp]
lemma id_val (A : PointedGaloisObject F) : 𝟙 A = 𝟙 A.obj :=
  rfl

@[simp]
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
    refine ⟨⟨Z, z, hgal⟩, ⟨h, hhz⟩, Hom.ext ?_⟩
    apply evaluationInjective_of_isConnected F Z B z
    show F.map (h ≫ f) z = F.map (h ≫ g) z
    simp only [map_comp, FintypeCat.comp_apply, hhz, hf, hg]

/-- The canonical functor from pointed Galois objects to `C`. -/
def incl : PointedGaloisObject F ⥤ C where
  obj := fun A ↦ A
  map := fun ⟨f, _⟩ ↦ f

@[simp]
lemma incl_obj (A : PointedGaloisObject F) : (incl F).obj A = A :=
  rfl

@[simp]
lemma incl_map {A B : PointedGaloisObject F} (f : A ⟶ B) : ((incl F).map f) = f.val :=
  rfl

/-- `F ⋙ FintypeCat.incl` as a cocone over `(can F).op ⋙ coyoneda`.
This is a colimit cocone (see `PreGaloisCategory.isColimìt`) -/
def cocone : Cocone ((incl F).op ⋙ coyoneda) where
  pt := F ⋙ FintypeCat.incl
  ι := {
    app := fun ⟨A, a, _⟩ ↦ { app := fun X (f : (A : C) ⟶ X) ↦ F.map f a }
    naturality := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, (hf : F.map f b = a)⟩ ↦ by
      ext Y (g : (A : C) ⟶ Y)
      suffices h : F.map g (F.map f b) = F.map g a by
        simpa
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
      @IsFilteredOrEmpty.cocone_objs (PointedGaloisObject F)ᵒᵖ _ _
      ⟨{ obj := A, pt := a}⟩ ⟨{obj := B, pt := b}⟩
    refine ⟨⟨{ obj := Z, pt := z }⟩, ⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
    apply evaluationInjective_of_isConnected F Z X z
    change F.map (f ≫ u) z = F.map (g ≫ v) z
    rw [map_comp, FintypeCat.comp_apply, hf, map_comp, FintypeCat.comp_apply, hg, h]

instance : HasColimit ((incl F).op ⋙ coyoneda) where
  exists_colimit := ⟨cocone F, isColimit F⟩

variable {F}

/-- A morphism of pointed Galois objects induces a map on automorphism groups
of the underlying objects in `C`. This is a group homomorphism (see `autMapMul`). -/
noncomputable def autMap {A B : PointedGaloisObject F} (f : A ⟶ B) (σ : Aut A.obj) : Aut B.obj :=
  (evaluationEquivOfIsGalois F B B.pt).symm (F.map (σ.hom ≫ f) A.pt)

@[simp]
lemma autMap_eval {A B : PointedGaloisObject F} (f : A ⟶ B) (σ : Aut A.obj) :
    F.map (autMap f σ).hom B.pt = F.map f (F.map σ.hom A.pt) := by
  simp [autMap]

lemma autMap_surjective {A B : PointedGaloisObject F} (f : A ⟶ B) :
    Function.Surjective (autMap f) := by
  intro σ
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f.val (F.map σ.hom B.pt)
  obtain ⟨τ, (hτ : F.map τ.hom A.pt = a')⟩ := MulAction.exists_smul_eq (Aut A.obj) A.pt a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B B.pt
  simp [hτ, ha']

@[simp]
lemma comp_autMap {A B : PointedGaloisObject F} (f : A ⟶ B) (σ : Aut A.obj) :
    f.val ≫ (autMap f σ).hom = σ.hom ≫ f := by
  apply evaluationInjective_of_isConnected F A B A.pt
  simp

@[simp]
lemma comp_autMap_apply {A B : PointedGaloisObject F} (f : A ⟶ B) (σ : Aut A.obj) (a : F.obj A) :
    F.map (autMap f σ).hom (F.map f.val a) = F.map f.val (F.map σ.hom a) := by
  simpa [-comp_autMap] using congrFun (congrArg F.map (comp_autMap f σ)) a

@[simp]
lemma autMap_apply_mul {A B : PointedGaloisObject F} (f : A ⟶ B) (σ τ : Aut A.obj) :
    autMap f (σ * τ) = autMap f σ * autMap f τ := by
  apply evaluation_aut_injective_of_isConnected F (B : C) B.pt
  simp [Aut.Aut_mul_def]

/-- `MonoidHom` version of `autMap`. -/
noncomputable def autMapMul {A B : PointedGaloisObject F} (f : A ⟶ B) :
     Aut (A : C) →* Aut (B : C) :=
  MonoidHom.mk' (autMap f) (autMap_apply_mul f)

end PointedGaloisObject

open PointedGaloisObject

/-- The diagram sending each pointed Galois object to its automorphism group
as an object of `C`. -/
noncomputable def autGaloisSystem : PointedGaloisObject F ⥤ GroupCat.{u₂} where
  obj := fun A ↦ GroupCat.of <| Aut (A : C)
  map := fun {A B} f ↦ (autMapMul f : Aut (A : C) →* Aut (B : C))
  map_id := fun A ↦ by
    ext (σ : Aut (A : C))
    show autMap (𝟙 A) σ = σ
    apply evaluation_aut_injective_of_isConnected F A A.pt
    simp
  map_comp {A B C} f g := by
    ext (σ : Aut A.obj)
    show autMap (f ≫ g) σ = autMap g (autMap f σ)
    apply evaluation_aut_injective_of_isConnected F C C.pt
    simp

  end PreGaloisCategory

  end CategoryTheory
