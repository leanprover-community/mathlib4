/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.IndYoneda

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to `X ⋙ coyoneda`.

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

/-- `autGaloisSystem` but lifted to a bigger universe. This is needed to compute its limit. -/
noncomputable def autGaloisSystem' : PointedGaloisObject F ⥤ GroupCat.{max u₁ u₂} :=
  autGaloisSystem F ⋙ GroupCat.uliftFunctor.{u₂, u₁}

@[simp]
lemma autGaloisSystem'_map {A B : PointedGaloisObject F} (f : A ⟶ B) (φ : Aut (A : C)) :
    ((autGaloisSystem' F).map f) ⟨φ⟩ = ⟨autMapMul f φ⟩ :=
  rfl

/-- The limit of `autGaloisSystem` computed in `GroupCat.{max u₁ u₂}`. -/
noncomputable def autGalois : GroupCat.{max u₁ u₂} := limit (autGaloisSystem' F)

/-- The canonical projection from `autGalois F` to the `C`-automorphism group of each
pointed Galois object. -/
noncomputable def autGalois.π (A : PointedGaloisObject F) : autGalois F →* Aut (A : C) :=
  MonoidHom.comp MulEquiv.ulift.toMonoidHom (limit.π (autGaloisSystem' F) A)

/- Not a `simp` lemma, because we usually don't want to expose the internals here. -/
lemma autGalois.π_apply (A : PointedGaloisObject F) (x : autGalois F) :
    autGalois.π F A x = Equiv.ulift (limit.π (autGaloisSystem' F) A x) :=
  rfl

lemma autGaloisSystem'_map_surjective ⦃A B : PointedGaloisObject F⦄ (f : A ⟶ B) :
    Function.Surjective ((autGaloisSystem' F).map f) := by
  intro ⟨(φ : Aut B.obj)⟩
  obtain ⟨ψ, hψ⟩ := autMap_surjective f φ
  use ⟨ψ⟩
  simp only [autGaloisSystem'_map]
  apply ULift.ext
  exact hψ

/-- `autGalois.π` is surjective for every pointed Galois object. -/
theorem autGalois.π_surjective (A : PointedGaloisObject F) :
    Function.Surjective (autGalois.π F A) := fun (σ : Aut A.obj) ↦ by
  have (i : PointedGaloisObject F) : Finite ((autGaloisSystem' F ⋙ forget _).obj i) :=
    inferInstanceAs <| Finite (ULift (Aut (i.obj)))
  obtain ⟨s', hs⟩ := eval_section_surjective_of_surjective
    (autGaloisSystem' F ⋙ forget _) (autGaloisSystem'_map_surjective F) A ⟨σ⟩
  simp only [comp_obj] at hs
  use (preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv
    ((Types.limitEquivSections (autGaloisSystem' F ⋙ forget _)).symm s')
  dsimp [autGalois.π]
  change MulEquiv.ulift (((preservesLimitIso _ _).inv
    ≫ (forget _).map (limit.π (autGaloisSystem' F) A)) _) = σ
  simp only [preservesLimitsIso_inv_π, comp_obj, Types.limitEquivSections_symm_apply, hs]
  rfl

/-- Equality of elements of `autGalois F` can be checked on the projections on each pointed
Galois object. -/
lemma autGalois_ext {f g : autGalois F}
    (h : ∀ (A : PointedGaloisObject F), autGalois.π F A f = autGalois.π F A g) : f = g :=
  Concrete.limit_ext (autGaloisSystem' F) f g (fun A ↦ EquivLike.injective MulEquiv.ulift (h A))

section EndAutGaloisIsomorphism

/-!

### Isomorphism between `Aut F` and `autGalois F`

In this section we establish the isomorphism between the automorphism group of `F` and
the limit over the automorphism groups of all Galois objects.

We first establish the isomorphism between `End F` and `autGalois F`, from which we deduce that
`End F` is a group, hence `End F = Aut F`. The isomorphism is built in multiple steps:

- `endIsoLimitFibers : End F ≅ limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁})`: the endomorphisms of
  `F` are isomorphic to the limit over `F.obj A` for all Galois objects `A`.
  This is obtained as the composition (slighty simplified):

  `End F ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F) ≅ limit (incl F ⋙ F)`

  Where the first isomorphism is induced from the pro-representability of `F` and the second one
  from the pro-coyoneda lemma.

- `endIsoAutGalois : End F ≅ autGalois F`: this is the composition of `endIsoLimitFibers` with:

  `limit (incl F ⋙ F) ≅ limit (autGaloisSystem' F ⋙ forget GroupCat)`

  which is induced from the level-wise equivalence `Aut A ≃ F.obj A` for a Galois object `A`.

-/

-- Local notation for `F` considered as a functor to types instead of finite types.
local notation "F'" => F ⋙ FintypeCat.incl

/-- The endomorphisms of `F` are isomorphic to the limit over the fibers of `F` on all
Galois objects. -/
noncomputable def endIsoLimitFibers : End F ≅ limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) :=
  let i1 : End F ≅ End F' :=
    Equiv.toIso (NatTrans.equivOfCompFullyFaithful FintypeCat.incl)
  let i2 : End F' ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F') :=
    (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F') ≅ limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (incl F) F'
  i1 ≪≫ i2 ≪≫ i3

@[simp]
lemma endIsoLimitFibers_π (f : End F) (A : PointedGaloisObject F) :
    limit.π (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) A ((endIsoLimitFibers F).hom f) = ⟨f.app A A.pt⟩ := by
  apply ULift.ext
  simp [endIsoLimitFibers]
  change ((NatTrans.equivOfCompFullyFaithful FintypeCat.incl) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp

/-- Functorial isomorphism `Aut A ≅ F.obj A` for Galois objects `A`. -/
noncomputable def autIsoFibers :
    autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} ≅ incl F ⋙ F' ⋙ uliftFunctor.{u₁} :=
  NatIso.ofComponents (fun A ↦ ((Equiv.ulift.{u₁, u₂}).trans
      ((evaluationEquivOfIsGalois F A A.pt).trans Equiv.ulift.{u₁, u₂}.symm)).toIso)
    (fun {A B} f ↦ by
      ext ⟨φ : Aut A.obj⟩
      apply ULift.ext
      dsimp
      erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down, Equiv.apply_symm_apply]
      simp)

lemma autIsoFibers_inv_app (A : PointedGaloisObject F) (b : F.obj A) :
    (autIsoFibers F).inv.app A ⟨b⟩ = ⟨(evaluationEquivOfIsGalois F A A.pt).symm b⟩ :=
  rfl

/-- The isomorphism between endomorphisms of `F` and the limit over the automorphism groups
of all Galois objects. -/
noncomputable def endIsoAutGalois : End F ≅ autGalois F := by
  let i1 := endIsoLimitFibers F
  let i2 := lim.mapIso (autIsoFibers F).symm
  let i3 := (preservesLimitIso (forget GroupCat.{max u₁ u₂}) (autGaloisSystem' F)).symm
  exact i1 ≪≫ i2 ≪≫ i3

/-- `endIsoAutGalois` as an equiv. -/
noncomputable def endEquivAutGalois : End F ≃ autGalois F := (endIsoAutGalois F).toEquiv

lemma endEquivAutGalois_π (f : End F) (A : PointedGaloisObject F) :
    F.map (autGalois.π F A (endEquivAutGalois F f)).hom A.2 = f.app A A.pt := by
  dsimp [endEquivAutGalois, endIsoAutGalois, autGalois.π_apply]
  change F.map (Equiv.ulift (((preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv
      ≫ (forget GroupCat).map (limit.π (autGaloisSystem' F) A)) _)).hom A.pt = f.app A.obj A.pt
  rw [preservesLimitsIso_inv_π, Types.Limit.map_π_apply', endIsoLimitFibers_π, Equiv.ulift_apply,
    autIsoFibers_inv_app, evaluationEquivOfIsGalois_symm_fiber]

@[simp]
theorem endEquivAutGalois_mul (f g : End F) :
    (endEquivAutGalois F) (g ≫ f) = (endEquivAutGalois F g) * (endEquivAutGalois F f) := by
  refine autGalois_ext F (fun A ↦ evaluation_aut_injective_of_isConnected F A A.pt ?_)
  simp only [map_mul, endEquivAutGalois_π, Aut.Aut_mul_def, NatTrans.comp_app, Iso.trans_hom]
  simp only [map_comp, FintypeCat.comp_apply, endEquivAutGalois_π]
  change f.app A (g.app A A.pt) =
    (f.app A ≫ F.map ((autGalois.π F A) ((endEquivAutGalois F) g)).hom) A.pt
  rw [← f.naturality, FintypeCat.comp_apply, endEquivAutGalois_π]

/-- The monoid isomorphism between endomorphisms of `F` and the (multiplicative oppososite of the)
limit of automorphism groups of all Galois objects. -/
noncomputable def endMulEquivAutGalois : End F ≃* (autGalois F)ᵐᵒᵖ :=
  MulEquiv.mk (Equiv.trans (endEquivAutGalois F) MulOpposite.opEquiv) (by simp)

lemma endMulEquivAutGalois_pi (f : End F) (A : PointedGaloisObject F) :
    F.map (autGalois.π F A (endMulEquivAutGalois F f).unop).hom A.2 = f.app A A.pt :=
  endEquivAutGalois_π F f A

/-- Any endomorphism of a fiber functor is a unit. -/
theorem FibreFunctor.end_isUnit (f : End F) : IsUnit f :=
  (MulEquiv.map_isUnit_iff (endMulEquivAutGalois F)).mp
    (Group.isUnit ((endMulEquivAutGalois F) f))

/-- Any endomorphism of a fiber functor is an isomorphism. -/
instance FibreFunctor.end_isIso (f : End F) : IsIso f := by
  rw [← isUnit_iff_isIso]
  exact FibreFunctor.end_isUnit F f

/-- The automorphism group of `F` is multiplicatively isomorphic to
(the multiplicative opposite of) the limit over the automorphism groups of
the Galois objects. -/
noncomputable def autMulEquivAutGalois : Aut F ≃* (autGalois F)ᵐᵒᵖ where
  toFun := MonoidHom.comp (endMulEquivAutGalois F) (Aut.toEnd F)
  invFun t := asIso ((endMulEquivAutGalois F).symm t)
  left_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    exact Aut.ext rfl
  right_inv t := by
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, Aut.toEnd_apply]
    exact (MulEquiv.eq_symm_apply (endMulEquivAutGalois F)).mp rfl
  map_mul' := by simp

lemma autMulEquivAutGalois_π (f : Aut F) (A : C) [IsGalois A] (a : F.obj A) :
    F.map (autGalois.π F { obj := A, pt := a } (autMulEquivAutGalois F f).unop).hom a
      = f.hom.app A a := by
  dsimp [autMulEquivAutGalois, endMulEquivAutGalois]
  rw [endEquivAutGalois_π]
  rfl

@[simp]
lemma autMulEquivAutGalois_symm_app (x : autGalois F) (A : C) [IsGalois A] (a : F.obj A) :
    ((autMulEquivAutGalois F).symm ⟨x⟩).hom.app A a =
      F.map (autGalois.π F ⟨A, a, inferInstance⟩ x).hom a := by
  rw [← autMulEquivAutGalois_π, MulEquiv.apply_symm_apply]
  rfl

end EndAutGaloisIsomorphism

/-- The `Aut F` action on the fiber of a Galois object is transitive. See
`pretransitive_of_isConnected` for the same result for connected objects. -/
theorem FiberFunctor.isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := autGalois.π_surjective F ⟨X, x, inferInstance⟩ φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

/-- The `Aut F` action on the fiber of a connected object is transitive. -/
instance FiberFunctor.isPretransitive_of_isConnected (X : C) [IsConnected X] :
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
  show (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality, FintypeCat.comp_apply, hσ]

end PreGaloisCategory

end CategoryTheory
