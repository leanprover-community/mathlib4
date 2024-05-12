/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.ProCoyoneda

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to `X ⋙ coyoneda`.

## Main definitions

- `PointedGaloisObject`: the category of pointed Galois objects
- `PointedGaloisObject.cocone`: a cocone on `(PointedGaloisObject.incl F).op ≫ coyoneda` with
  point `F ⋙ FintypeCat.incl`.

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
  obj : C
  pt : F.obj obj
  isGalois : IsGalois obj := by infer_instance

namespace PointedGaloisObject

attribute [instance] isGalois

instance (X : PointedGaloisObject F) : CoeDep (PointedGaloisObject F) X C where
  coe := X.obj

variable {F} in
structure Hom (A B : PointedGaloisObject F) where
  val : A.obj ⟶ B.obj
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

def MonCat.uliftFunctor : MonCat.{u₁} ⥤ MonCat.{max u₁ u₂} where
  obj X := MonCat.of (ULift.{max u₁ u₂, u₁} X)
  map {X Y} f := MonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

def GroupCat.uliftFunctor : GroupCat.{u₁} ⥤ GroupCat.{max u₁ u₂} where
  obj X := GroupCat.of (ULift.{u₂, u₁} X)
  map {X Y} f := GroupCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

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

lemma autGalois.π_apply (A : PointedGaloisObject F) (x : autGalois F) :
    autGalois.π F A x = Equiv.ulift (limit.π (autGaloisSystem' F) A x) :=
  rfl

lemma autGalois_ext (f g : autGalois F)
    (h : ∀ (A : PointedGaloisObject F), autGalois.π F A f = autGalois.π F A g) : f = g := by
  apply Concrete.limit_ext (autGaloisSystem' F) f g
  intro A
  have h1 : MulEquiv.ulift ((limit.π (autGaloisSystem' F) A) f) =
    MulEquiv.ulift ((limit.π (autGaloisSystem' F) A) g) := h A
  exact (EquivLike.injective _) h1

lemma autGalois_ext' (x y : autGalois F)
    (h : ∀ (A : PointedGaloisObject F),
      limit.π (autGaloisSystem' F) A x = limit.π (autGaloisSystem' F) A y) : x = y :=
  Concrete.limit_ext (autGaloisSystem' F) x y h

local notation "F'" => F ⋙ FintypeCat.incl

/-- The endomorphisms of `F` are isomorphic to the limit over the fibers of `F` on all
Galois objects. -/
noncomputable def endIsoLimitFibers : End F ≅ limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) :=
  let i1 : End F ≅ End F' :=
    Equiv.toIso (NatTrans.equivOfCompFullyFaithful FintypeCat.incl)
  let i2 : End F' ≅ (colimit ((incl F).op ⋙ coyoneda) ⟶ F') :=
    (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F') ≅ limit (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) :=
    procoyonedaIso' (incl F) F'
  i1 ≪≫ i2 ≪≫ i3

theorem endIsoLimitFibers_π (f : End F) (A : PointedGaloisObject F) :
    limit.π (incl F ⋙ F' ⋙ uliftFunctor.{u₁}) A ((endIsoLimitFibers F).hom f) = ⟨f.app A A.pt⟩ := by
  apply ULift.ext
  simp [endIsoLimitFibers]
  change ((NatTrans.equivOfCompFullyFaithful FintypeCat.incl) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp

noncomputable def galautiso' :
    autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} ≅ incl F ⋙ F' ⋙ uliftFunctor.{u₁} := by
  fapply NatIso.ofComponents
  · intro ⟨A, a, _⟩
    apply Equiv.toIso
    exact (Equiv.ulift.{u₁, u₂}).trans
      ((evaluationEquivOfIsGalois F A a).trans Equiv.ulift.{u₁, u₂}.symm)
  · intro ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨(f : A ⟶ B), hf⟩
    dsimp
    ext ⟨φ : Aut A⟩
    apply ULift.ext
    erw [Equiv.ulift_apply, Equiv.ulift_apply]
    simp only [types_comp_apply, autGaloisSystem'_map, Function.comp_apply, uliftFunctor_map,
      FintypeCat.incl_map]
    erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down]
    simp only [autMapMul, MonoidHom.mk'_apply, autMap, map_comp, FintypeCat.comp_apply]
    erw [Equiv.apply_symm_apply]
    rfl

/-- functorial isomorphism `F.obj A ≃ Aut A` for Galois object `A`. -/
noncomputable def galautiso :
    incl F ⋙ F' ⋙ uliftFunctor.{u₁} ≅ autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} :=
  (galautiso' F).symm

@[simp]
theorem galautiso_app (A : PointedGaloisObject F) (b : F.obj A) :
    (galautiso F).hom.app A ⟨b⟩ =
      ⟨(evaluationEquivOfIsGalois F A A.pt).symm b⟩ :=
  rfl

noncomputable def iso4 : End F ≅ limit (autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂}) := by
  apply Iso.trans
  exact endIsoLimitFibers F
  exact lim.mapIso (galautiso F)

@[simp]
theorem iso4_pi_apply (A : PointedGaloisObject F) (f : End F) :
    limit.π (autGaloisSystem' F ⋙ forget _) A ((iso4 F).hom f) =
      ⟨(evaluationEquivOfIsGalois F A A.pt).symm (f.app A A.pt)⟩ := by
  simp [iso4]
  erw [endIsoLimitFibers_π]
  rw [galautiso_app]

noncomputable def iso5' : End F ≅ autGalois F := by
  show End F ≅ (forget GroupCat.{max u₁ u₂}).obj (limit (autGaloisSystem' F))
  apply Iso.trans
  exact iso4 F
  exact (preservesLimitIso (forget GroupCat.{max u₁ u₂}) (autGaloisSystem' F)).symm

noncomputable def iso5 : End F ≃ autGalois F := (iso5' F).toEquiv

lemma iso5_pi_foo (f : End F) (A : PointedGaloisObject F) :
    F.map (autGalois.π F A (iso5 F f)).hom A.2 = f.app A A.pt := by
  simp [iso5, iso5']
  rw [autGalois.π_apply]
  change F.map
    (((iso4 F).hom
        ≫ (preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv
        ≫ (forget GroupCat).map (limit.π (autGaloisSystem' F) A)) f).down.hom
    A.2 = _
  rw [preservesLimitsIso_inv_π]
  simp

@[simp]
theorem iso5_mul (f g : End F) : (iso5 F) (g ≫ f) = (iso5 F g) * (iso5 F f) := by
  apply autGalois_ext F
  intro ⟨A, a, _⟩
  simp
  apply evaluation_aut_injective_of_isConnected F A a
  simp
  rw [iso5_pi_foo]
  simp
  rw [Aut.Aut_mul_def]
  simp [-FintypeCat.comp_apply]
  simp
  rw [iso5_pi_foo]
  change f.app A (g.app A a) =
    (f.app A ≫ F.map ((autGalois.π F ⟨A, a, _⟩) ((iso5 F) g)).hom) a
  rw [← f.naturality]
  simp
  rw [iso5_pi_foo]

noncomputable def iso5Monoid : End F ≃* (autGalois F)ᵐᵒᵖ :=
  MulEquiv.mk (Equiv.trans (iso5 F) MulOpposite.opEquiv) (by simp)

lemma iso5Monoid_pi (f : End F) (A : PointedGaloisObject F) :
    F.map (autGalois.π F A (iso5Monoid F f).unop).hom A.2 = f.app A A.pt :=
  iso5_pi_foo F f A

theorem FibreFunctor.end_isUnit (f : End F) : IsUnit f :=
  isUnit_of_equiv _ _ (iso5Monoid F).symm f

theorem FibreFunctor.end_isIso (f : End F) : IsIso f := by
  rw [← isUnit_iff_isIso]
  exact FibreFunctor.end_isUnit F f

noncomputable def autMulEquivAutGalois : Aut F ≃* (autGalois F)ᵐᵒᵖ where
  toFun := MonoidHom.comp (iso5Monoid F) (Aut.toEnd F)
  invFun t := by
    let s : End F := (iso5Monoid F).symm t
    have : IsIso s := FibreFunctor.end_isIso F s
    apply asIso s
  left_inv t := by
    simp
    exact Aut.ext rfl
  right_inv t := by
    simp
    exact (MulEquiv.eq_symm_apply (iso5Monoid F)).mp rfl
  map_mul' := by simp

theorem autMulEquivAutGalois_π (f : Aut F) (A : C) [IsGalois A] (a : F.obj A) :
    F.map (autGalois.π F { obj := A, pt := a } (autMulEquivAutGalois F f).unop).hom a = f.hom.app A a := by
  simp [autMulEquivAutGalois, iso5Monoid]
  rw [iso5_pi_foo]
  rfl

@[simp]
theorem autMulEquivAutGalois_symm_app (x : autGalois F) (A : C) [IsGalois A] (a : F.obj A) :
    ((autMulEquivAutGalois F).symm ⟨x⟩).hom.app A a =
      F.map (autGalois.π F ⟨A, a, inferInstance⟩ x).hom a := by
  rw [← autMulEquivAutGalois_π, MulEquiv.apply_symm_apply]
  rfl

lemma proj_surj (A : C) [IsGalois A] (a : F.obj A) :
    Function.Surjective (autGalois.π F ⟨A, a, inferInstance⟩) := fun (σ : Aut A) ↦ by
  have (i : PointedGaloisObject F) : Finite ((autGaloisSystem' F ⋙ forget _).obj i) :=
    inferInstanceAs <| Finite (ULift (Aut (i.obj)))
  have fsur (i j : PointedGaloisObject F) (f : i ⟶ j) : Function.Surjective ((autGaloisSystem' F).map f) := by
    intro ⟨(φ : Aut j.obj)⟩
    obtain ⟨ψ, hψ⟩ := autMap_surjective f φ
    use ⟨ψ⟩
    simp only [autGaloisSystem'_map]
    apply ULift.ext
    exact hψ
  have := eval_section_surjective_of_surjective (autGaloisSystem' F ⋙ forget _) fsur
  obtain ⟨s', hs⟩ := eval_section_surjective_of_surjective
    (autGaloisSystem' F ⋙ forget _) fsur ⟨A, a, _⟩ ⟨σ⟩
  simp only [comp_obj] at hs
  let s : limit _ := (Types.limitEquivSections (autGaloisSystem' F ⋙ forget _)).symm s'
  let t : autGalois F := (preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv s
  use t
  simp [t, s, autGalois.π]
  change MulEquiv.ulift
      (((preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv
        ≫ (forget _).map (limit.π (autGaloisSystem' F) ⟨A, a, inferInstance⟩))
        ((Types.limitEquivSections ((autGaloisSystem' F).comp (forget GroupCat))).symm s')) =
    σ
  rw [preservesLimitsIso_inv_π]
  simp
  rw [hs]
  rfl

instance (X : C) : MulAction (Aut F) (F.obj X) where
  smul σ x := σ.hom.app X x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem mulAction_def {X : C} (σ : Aut F) (x : F.obj X) :
    σ • x = σ.hom.app X x :=
  rfl

theorem pretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := proj_surj F X x φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

/-- The `Aut F` action on the fiber of a connected object is transitive. -/
instance pretransitive_of_isConnected (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := pretransitive_of_isGalois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [←ha, ←hb]
  show (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality, FintypeCat.comp_apply, hσ]
