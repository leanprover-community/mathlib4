/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to the colimit of `X ⋙ coyoneda`.

From this we deduce the canonical isomorphism of `Aut F` with the limit over the automorphism
groups of all Galois objects.

## Main definitions

- `PointedGaloisObject`: the category of pointed Galois objects
- `PointedGaloisObject.cocone`: a cocone on `(PointedGaloisObject.incl F).op ≫ coyoneda` with
  point `F ⋙ FintypeCat.incl`.
- `autGaloisSystem`: the system of automorphism groups indexed by the pointed Galois objects.

## Main results

- `PointedGaloisObject.isColimit`: the cocone `PointedGaloisObject.cocone` is a colimit cocone.
- `autMulEquivAutGalois`: `Aut F` is canonically isomorphic to the limit over the automorphism
  groups of all Galois objects.
- `FiberFunctor.isPretransitive_of_isConnected`: The `Aut F` action on the fiber of a connected
  object is transitive.

## Implementation details

The pro-representability statement and the isomorphism of `Aut F` with the limit over the
automorphism groups of all Galois objects naturally forces `F` to take values in `FintypeCat.{u₂}`
where `u₂` is the `Hom`-universe of `C`. Since this is used to show that `Aut F` acts
transitively on `F.obj X` for connected `X`, we a priori only obtain this result for
the mentioned specialized universe setup. To obtain the result for `F` taking values in an arbitrary
`FintypeCat.{w}`, we postcompose with an equivalence `FintypeCat.{w} ≌ FintypeCat.{u₂}` and apply
the specialized result.

In the following the section `Specialized` is reserved for the setup where `F` takes values in
`FintypeCat.{u₂}` and the section `General` contains results holding for `F` taking values in
an arbitrary `FintypeCat.{w}`.

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]

/-- A pointed Galois object is a Galois object with a fixed point of its fiber. -/
structure PointedGaloisObject (F : C ⥤ FintypeCat.{w}) : Type (max u₁ u₂ w) where
  /-- The underlying object of `C`. -/
  obj : C
  /-- An element of the fiber of `obj`. -/
  pt : F.obj obj
  /-- `obj` is Galois. -/
  isGalois : IsGalois obj := by infer_instance

namespace PointedGaloisObject

section General

variable (F : C ⥤ FintypeCat.{w})

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
  Hom.ext h

@[simp]
lemma id_val (A : PointedGaloisObject F) : 𝟙 A = 𝟙 A.obj :=
  rfl

@[simp, reassoc]
lemma comp_val {A B C : PointedGaloisObject F} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

variable (F)

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

end General

section Specialized

variable (F : C ⥤ FintypeCat.{u₂})

/-- `F ⋙ FintypeCat.incl` as a cocone over `(can F).op ⋙ coyoneda`.
This is a colimit cocone (see `PreGaloisCategory.isColimit`) -/
def cocone : Cocone ((incl F).op ⋙ coyoneda) where
  pt := F ⋙ FintypeCat.incl
  ι := {
    app := fun ⟨A, a, _⟩ ↦ { app X := TypeCat.ofHom (fun (f : (A : C) ⟶ X) ↦ F.map f a) }
    naturality := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, (hf : F.map f b = a)⟩ ↦ by
      ext Y (g : (A : C) ⟶ Y)
      suffices h : F.map g (F.map f b) = F.map g a by simpa
      rw [hf]
  }

@[simp]
lemma cocone_app (A : PointedGaloisObject F) (B : C) :
    ((cocone F).ι.app ⟨A⟩).app B = TypeCat.ofHom (fun (f : (A : C) ⟶ B) ↦ F.map f A.pt) :=
  rfl

variable [FiberFunctor F]

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

set_option backward.isDefEq.respectTransparency false in
/-- `cocone F` is a colimit cocone, i.e. `F` is pro-represented by `incl F`. -/
noncomputable def isColimit : IsColimit (cocone F) := by
  refine evaluationJointlyReflectsColimits _ (fun X ↦ ?_)
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : F.obj X)
    obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
    refine ⟨⟨Z, z, hgal⟩, f ≫ i, ?_⟩
    simp [← hfz, ← h1]
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

end Specialized

end PointedGaloisObject

open PointedGaloisObject

section Specialized

variable (F : C ⥤ FintypeCat.{u₂})

/-- The diagram sending each pointed Galois object to its automorphism group
as an object of `C`. -/
@[simps]
noncomputable def autGaloisSystem : PointedGaloisObject F ⥤ GrpCat.{u₂} where
  obj := fun A ↦ GrpCat.of <| Aut (A : C)
  map := fun {A B} f ↦ GrpCat.ofHom (autMapHom f)

/-- The limit of `autGaloisSystem`. -/
noncomputable def AutGalois : Type (max u₁ u₂) :=
  (autGaloisSystem F ⋙ forget _).sections

noncomputable instance : Group (AutGalois F) :=
  inferInstanceAs <| Group (autGaloisSystem F ⋙ forget _).sections

/-- The canonical projection from `AutGalois F` to the `C`-automorphism group of each
pointed Galois object. -/
noncomputable def AutGalois.π (A : PointedGaloisObject F) : AutGalois F →* Aut (A : C) :=
  GrpCat.sectionsπMonoidHom (autGaloisSystem F) A

/- Not a `simp` lemma, because we usually don't want to expose the internals here. -/
lemma AutGalois.π_apply (A : PointedGaloisObject F) (x : AutGalois F) :
    AutGalois.π F A x = x.val A :=
  rfl

lemma autGaloisSystem_map_surjective ⦃A B : PointedGaloisObject F⦄ (f : A ⟶ B) :
    Function.Surjective ((autGaloisSystem F).map f) := by
  intro (φ : Aut B.obj)
  obtain ⟨ψ, hψ⟩ := autMap_surjective_of_isGalois f.val φ
  use ψ
  simp only [autGaloisSystem_map]
  exact hψ

/-- Equality of elements of `AutGalois F` can be checked on the projections on each pointed
Galois object. -/
lemma AutGalois.ext {f g : AutGalois F}
    (h : ∀ (A : PointedGaloisObject F), AutGalois.π F A f = AutGalois.π F A g) : f = g := by
  dsimp only [AutGalois]
  ext A
  exact h A

variable [FiberFunctor F]

/-- `autGalois.π` is surjective for every pointed Galois object. -/
theorem AutGalois.π_surjective (A : PointedGaloisObject F) :
    Function.Surjective (AutGalois.π F A) := fun (σ : Aut A.obj) ↦ by
  have (i : PointedGaloisObject F) : Finite ((autGaloisSystem F ⋙ forget _).obj i) :=
    inferInstanceAs <| Finite (Aut (i.obj))
  exact eval_section_surjective_of_surjective
    (autGaloisSystem F ⋙ forget _) (autGaloisSystem_map_surjective F) A σ

section EndAutGaloisIsomorphism

/-!

### Isomorphism between `Aut F` and `AutGalois F`

In this section we establish the isomorphism between the automorphism group of `F` and
the limit over the automorphism groups of all Galois objects.

We first establish the isomorphism between `End F` and `AutGalois F`, from which we deduce that
`End F` is a group, hence `End F = Aut F`. The isomorphism is built in multiple steps:

- `endEquivSectionsFibers : End F ≅ (incl F ⋙ F').sections`: the endomorphisms of
  `F` are isomorphic to the limit over `F.obj A` for all Galois objects `A`.
  This is obtained as the composition (slightly simplified):

  `End F ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F) ≅ (incl F ⋙ F).sections`

  Where the first isomorphism is induced from the pro-representability of `F` and the second one
  from the pro-coyoneda lemma.

- `endEquivAutGalois : End F ≅ AutGalois F`: this is the composition of `endEquivSectionsFibers`
  with:

  `(incl F ⋙ F).sections ≅ (autGaloisSystem F ⋙ forget GrpCat).sections`

  which is induced from the level-wise equivalence `Aut A ≃ F.obj A` for a Galois object `A`.

-/

-- Local notation for `F` considered as a functor to types instead of finite types.
local notation "F'" => F ⋙ FintypeCat.incl

/-- The endomorphisms of `F` are isomorphic to the limit over the fibers of `F` on all
Galois objects. -/
noncomputable def endEquivSectionsFibers : End F ≃ (incl F ⋙ F').sections :=
  let i1 : End F ≃ End F' :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : End F' ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F') :=
    (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F') ≅
      limit ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (incl F) F'
  let i4 : limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) ≃
      ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections :=
    Types.limitEquivSections (incl F ⋙ (F ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁, u₂})
  let i5 : ((incl F ⋙ F') ⋙ uliftFunctor.{u₁}).sections ≃ (incl F ⋙ F').sections :=
    (Types.sectionsEquiv (incl F ⋙ F')).symm
  i1.trans <| i2.toEquiv.trans <| i3.toEquiv.trans <| i4.trans i5

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma endEquivSectionsFibers_π (f : End F) (A : PointedGaloisObject F) :
    (endEquivSectionsFibers F f).val A = f.app A A.pt := by
  dsimp [endEquivSectionsFibers, Types.sectionsEquiv]
  erw [Types.limitEquivSections_apply, colimitCoyonedaHomIsoLimit'_π_apply]
  change (((FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful
      FintypeCat.incl) C).homEquiv) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Functorial isomorphism `Aut A ≅ F.obj A` for Galois objects `A`. -/
noncomputable def autIsoFibers :
    autGaloisSystem F ⋙ forget GrpCat ≅ incl F ⋙ F' :=
  NatIso.ofComponents (fun A ↦ ((evaluationEquivOfIsGalois F A A.pt).toIso))
    (fun f ↦ by
      ext
      simp [evaluationEquivOfIsGalois, -Hom.comp, ← f.comp])

lemma autIsoFibers_inv_app (A : PointedGaloisObject F) (b : F.obj A) :
    (autIsoFibers F).inv.app A b = (evaluationEquivOfIsGalois F A A.pt).symm b :=
  rfl

/-- The equivalence between endomorphisms of `F` and the limit over the automorphism groups
of all Galois objects. -/
noncomputable def endEquivAutGalois : End F ≃ AutGalois F :=
  let e1 := endEquivSectionsFibers F
  let e2 := ((Functor.sectionsFunctor _).mapIso (autIsoFibers F).symm).toEquiv
  e1.trans e2

set_option backward.isDefEq.respectTransparency false in
lemma endEquivAutGalois_π (f : End F) (A : PointedGaloisObject F) :
    F.map (AutGalois.π F A (endEquivAutGalois F f)).hom A.pt = f.app A A.pt := by
  dsimp [endEquivAutGalois, AutGalois.π_apply]
  change F.map ((((sectionsFunctor _).map (autIsoFibers F).inv) _).val A).hom A.pt = _
  dsimp [autIsoFibers]
  simp only [endEquivSectionsFibers_π]
  erw [evaluationEquivOfIsGalois_symm_fiber]

@[simp]
theorem endEquivAutGalois_mul (f g : End F) :
    (endEquivAutGalois F) (g ≫ f) = (endEquivAutGalois F g) * (endEquivAutGalois F f) := by
  refine AutGalois.ext F (fun A ↦ evaluation_aut_injective_of_isConnected F A A.pt ?_)
  simp only [map_mul, endEquivAutGalois_π, Aut.Aut_mul_def, NatTrans.comp_app, Iso.trans_hom]
  simp only [map_comp, FintypeCat.comp_apply, endEquivAutGalois_π]
  change f.app A (g.app A A.pt) =
    (f.app A ≫ F.map ((AutGalois.π F A) ((endEquivAutGalois F) g)).hom) A.pt
  rw [← f.naturality, FintypeCat.comp_apply, endEquivAutGalois_π]

/-- The monoid isomorphism between endomorphisms of `F` and the (multiplicative opposite of the)
limit of automorphism groups of all Galois objects. -/
noncomputable def endMulEquivAutGalois : End F ≃* (AutGalois F)ᵐᵒᵖ :=
  MulEquiv.mk (Equiv.trans (endEquivAutGalois F) MulOpposite.opEquiv) (by simp)

lemma endMulEquivAutGalois_pi (f : End F) (A : PointedGaloisObject F) :
    F.map (AutGalois.π F A (endMulEquivAutGalois F f).unop).hom A.2 = f.app A A.pt :=
  endEquivAutGalois_π F f A

/-- Any endomorphism of a fiber functor is a unit. -/
theorem FibreFunctor.end_isUnit (f : End F) : IsUnit f :=
  (isUnit_map_iff (endMulEquivAutGalois F) _).mp
    (Group.isUnit ((endMulEquivAutGalois F) f))

/-- Any endomorphism of a fiber functor is an isomorphism. -/
instance FibreFunctor.end_isIso (f : End F) : IsIso f := by
  rw [← isUnit_iff_isIso]
  exact FibreFunctor.end_isUnit F f

/-- The automorphism group of `F` is multiplicatively isomorphic to
(the multiplicative opposite of) the limit over the automorphism groups of
the Galois objects. -/
noncomputable def autMulEquivAutGalois : Aut F ≃* (AutGalois F)ᵐᵒᵖ where
  toFun := MonoidHom.comp (endMulEquivAutGalois F) (Aut.toEnd F)
  invFun t := asIso ((endMulEquivAutGalois F).symm t)
  left_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    exact Aut.ext rfl
  right_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, Aut.toEnd_apply]
    exact (MulEquiv.eq_symm_apply (endMulEquivAutGalois F)).mp rfl
  map_mul' := by simp [map_mul]

lemma autMulEquivAutGalois_π (f : Aut F) (A : C) [IsGalois A] (a : F.obj A) :
    F.map (AutGalois.π F { obj := A, pt := a } (autMulEquivAutGalois F f).unop).hom a =
      f.hom.app A a := by
  dsimp [autMulEquivAutGalois, endMulEquivAutGalois]
  rw [endEquivAutGalois_π]
  rfl

@[simp]
lemma autMulEquivAutGalois_symm_app (x : AutGalois F) (A : C) [IsGalois A] (a : F.obj A) :
    ((autMulEquivAutGalois F).symm ⟨x⟩).hom.app A a =
      F.map (AutGalois.π F ⟨A, a, inferInstance⟩ x).hom a := by
  rw [← autMulEquivAutGalois_π, MulEquiv.apply_symm_apply]
  rfl

end EndAutGaloisIsomorphism

/-- The `Aut F` action on the fiber of a Galois object is transitive. See
`pretransitive_of_isConnected` for the same result for connected objects. -/
theorem FiberFunctor.isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := AutGalois.π_surjective F ⟨X, x, inferInstance⟩ φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

/-- The `Aut F` action on the fiber of a connected object is transitive. For a version
with less restrictive universe assumptions, see `FiberFunctor.isPretransitive_of_isConnected`. -/
private instance FiberFunctor.isPretransitive_of_isConnected' (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := isPretransitive_of_isGalois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [← ha, ← hb]
  change (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality, FintypeCat.comp_apply, hσ]

end Specialized

section General

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- The `Aut F` action on the fiber of a connected object is transitive. -/
instance FiberFunctor.isPretransitive_of_isConnected (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) where
  exists_smul_eq x y := by
    let F' : C ⥤ FintypeCat.{u₂} := F ⋙ FintypeCat.uSwitch.{w, u₂}
    letI : FiberFunctor F' := FiberFunctor.comp_right _
    let e (Y : C) : F'.obj Y ≃ F.obj Y := (F.obj Y).uSwitchEquiv
    set x' : F'.obj X := (e X).symm x with hx'
    set y' : F'.obj X := (e X).symm y with hy'
    obtain ⟨g', (hg' : g'.hom.app X x' = y')⟩ := MulAction.exists_smul_eq (Aut F') x' y'
    let gapp (Y : C) : F.obj Y ≅ F.obj Y := FintypeCat.equivEquivIso <|
      (e Y).symm.trans <| (FintypeCat.equivEquivIso.symm (g'.app Y)).trans (e Y)
    let g : F ≅ F := NatIso.ofComponents gapp <| fun {X Y} f ↦ by
      ext x
      dsimp [gapp, e]
      erw [FintypeCat.uSwitchEquiv_naturality (F.map f)]
      rw [← Functor.comp_map]
      erw [← NatTrans.naturality_apply, FintypeCat.uSwitchEquiv_symm_naturality (F.map f)]
      rfl
    refine ⟨g, show (gapp X).hom x = y from ?_⟩
    simp [gapp, ← hx', hg', hy', Equiv.apply_symm_apply]

end General

end PreGaloisCategory

end CategoryTheory
