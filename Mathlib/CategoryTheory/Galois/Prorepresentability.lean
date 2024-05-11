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

## Main results


## References

* H. W. Lenstra. Galois theory for schemes
  <https://websites.math.leidenuniv.nl/algebra/GSchemes.pdf>

-/

universe u₁ u₂ w

section

variable {G M : Type*} [Group G] [Monoid M] (f : G ≃* M) (g : M ≃* G)

--def equivUnits (h : ∀ (x : M), IsUnit x) : M ≃* Mˣ where
--  toFun m := by
--    admit

end

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable (C : Type u₁) [Category.{u₂} C] [GaloisCategory C]

def GaloisObjects : Set C := { A : C | IsGalois A }

instance (A : GaloisObjects C) : IsGalois A.val :=
  A.2

variable (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]

variable {C}

def Idx : Type (max u₁ u₂) := (A : GaloisObjects C) × F.obj (A : C)

instance : Category.{u₂} (Idx F) where
  Hom := by
    intro ⟨A, a⟩ ⟨B, b⟩
    exact { f : (B : C) ⟶ A // F.map f b = a }
  id := by
    intro ⟨A, a⟩
    exact ⟨𝟙 (A : C), by simp⟩
  comp := by
    intro ⟨A, a⟩ ⟨B, b⟩ ⟨C, c⟩ ⟨f, hf⟩ ⟨g, hg⟩
    have h : F.map (g ≫ f) c = a := by
      simp only [F.map_comp, FintypeCat.comp_apply, hf, hg]
    exact ⟨g ≫ f, h⟩

instance : IsFilteredOrEmpty (Idx F) where
  cocone_objs := fun ⟨A, a⟩ ⟨B, b⟩ ↦ by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F (A ⨯ B)
      <| (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨⟨Z, hgal⟩, z⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cocone_maps := fun ⟨A, a⟩ ⟨B, b⟩ ⟨f, hf⟩ ⟨g, hg⟩ ↦ by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_hom_from_galois_of_fiber F B b
    refine ⟨⟨⟨Z, hgal⟩, z⟩, ⟨h, hhz⟩, ?_⟩
    apply Subtype.ext
    apply evaluationInjective_of_isConnected F Z A z
    show F.map (h ≫ f) z = F.map (h ≫ g) z
    simp only [map_comp, FintypeCat.comp_apply, hhz, hf, hg]

def can : (Idx F)ᵒᵖ ⥤ C where
  obj := fun ⟨⟨A, _⟩⟩ ↦ A
  map := fun ⟨f, _⟩ ↦ f

@[simp]
lemma can_obj (A : (Idx F)ᵒᵖ) : (can F).obj A = A.unop.1 :=
  rfl

@[simp]
lemma can_map_eq {A B : (Idx F)ᵒᵖ} (f : A ⟶ B) : ((can F).map f) = f.unop.val :=
  rfl

def cocone : Cocone ((can F).rightOp ⋙ coyoneda) where
  pt := F ⋙ FintypeCat.incl
  ι := {
    app := by
      intro ⟨A, a⟩
      exact {
        app := by
          intro X (f : (A : C) ⟶ X)
          -- evaluation at a
          exact F.map f a
      }
    naturality := by
      intro ⟨A, a⟩ ⟨B, b⟩ ⟨f, hf⟩
      ext Y (g : (A : C) ⟶ Y)
      simp [hf]
  }

@[simp]
lemma cocone_app (A : Idx F) (B : C) (f : (A.1 : C) ⟶ B) :
    ((cocone F).ι.app A).app B f = F.map f A.2 :=
  rfl

universe v u

noncomputable def iscolimit : IsColimit (cocone F) := by
  apply evaluationJointlyReflectsColimits
  intro X
  let G : Idx F ⥤ Type u₂ := (((can F).rightOp ⋙ coyoneda) ⋙ (evaluation C (Type u₂)).obj X)
  let s : Cocone G := ((evaluation C (Type u₂)).obj X).mapCocone (cocone F)
  show IsColimit s
  refine Types.FilteredColimit.isColimitOf G s ?_ ?_
  intro (x : F.obj X)
  obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
  obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
  use ⟨⟨Z, hgal⟩, z⟩
  use f ≫ i
  show x = F.map (f ≫ i) z
  simp only [←h1, map_comp, FintypeCat.comp_apply, hfz]
  intro ⟨A, a⟩ ⟨B, b⟩ (u : (A : C) ⟶ X) --(v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
  intro (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
  obtain ⟨⟨⟨Z, (hgal : IsGalois Z)⟩, z⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
    @IsFilteredOrEmpty.cocone_objs (Idx F) _ _ (⟨A, a⟩ : Idx F) (⟨B, b⟩ : Idx F)
  use ⟨⟨Z, hgal⟩, z⟩
  use ⟨f, hf⟩
  use ⟨g, hg⟩
  have : IsGalois Z := hgal
  have : IsConnected Z := inferInstance
  apply evaluationInjective_of_isConnected F Z X z
  show F.map (f ≫ u) z = F.map (g ≫ v) z
  rw [map_comp, FintypeCat.comp_apply, hf, map_comp, FintypeCat.comp_apply, hg, h]

--instance (X : C) : SMul (Aut F) (F.obj X) := ⟨fun σ a => (σ.app X).hom a⟩

--private noncomputable def autMap' {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A)
--    (b : F.obj B) (σ : Aut A) : { τ : Aut B | F.map τ.hom b = F.map (σ.hom ≫ f) a } := by
--  choose τ h using MulAction.surjective_smul (Aut B) b (F.map (σ.hom ≫ f) a)
--  exact ⟨τ, h⟩
--
--private noncomputable def autMap {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A)
--    (b : F.obj B) (σ : Aut A) : Aut B := autMap' F f a b σ

noncomputable def autMap {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A)
    (b : F.obj B) (σ : Aut A) : Aut B :=
  (evaluationEquivOfIsGalois F B b).symm (F.map (σ.hom ≫ f) a)

@[simp]
lemma autMap_eval {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A) (b : F.obj B)
    (σ : Aut A) : F.map (autMap F f a b σ : Aut B).hom b = F.map (σ.hom ≫ f) a := by
  simp [autMap]

lemma autMap_surjective {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶ B)
    (a : F.obj A) (b : F.obj B) : Function.Surjective (autMap F f a b) := by
  intro σ
  --have h : Nonempty (F.obj A) := nonempty_fibre_of_connected A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom b)
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B b
  simp only [autMap_eval, map_comp, FintypeCat.comp_apply]
  rw [hτ, ha']

lemma autMap_comp {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (a : F.obj A) (b : F.obj B)
    (h : F.map f a = b)
    (σ : Aut A) : σ.hom ≫ f = f ≫ (autMap F f a b σ).hom := by
  apply evaluationInjective_of_isConnected F A B a
  show F.map (σ.hom ≫ f) a = F.map (f ≫ (autMap F f a b σ).hom) a
  simp only [map_comp, FintypeCat.comp_apply, h, autMap_eval]

lemma autMap_mul {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (a : F.obj A) (b : F.obj B)
    (h : F.map f a = b)
    (σ τ : Aut A) : autMap F f a b (σ * τ) = autMap F f a b σ * autMap F f a b τ := by
  apply evaluation_aut_injective_of_isConnected F (B : C) b
  show F.map (autMap F f a b (σ * τ)).hom b =
    F.map (autMap F f a b σ * autMap F f a b τ).hom b
  simp only [autMap_eval]
  convert_to F.map ((τ.hom ≫ σ.hom) ≫ f) a
    = F.map ((f ≫ (autMap F f a b τ).hom) ≫ (autMap F f a b σ).hom) a
  erw [← h, Functor.map_comp]
  simp only [FintypeCat.comp_apply, autMap_eval, map_comp, Category.assoc]
  erw [← autMap_comp F f a b h τ, Category.assoc, Category.assoc,
    ← autMap_comp F f a b h σ]

noncomputable def autMapMul : {A B : (Idx F)ᵒᵖ} → (A ⟶ B) → Aut (A.1.1 : C) →* Aut (B.1.1 : C) := by
  intro ⟨⟨A, (h1 : IsGalois A)⟩, a⟩ ⟨⟨B, (h2 : IsGalois B)⟩, b⟩ ⟨f, hf⟩
  apply MonoidHom.mk'
  exact autMap_mul F f a b hf

noncomputable def autGaloisSystem : (Idx F)ᵒᵖ ⥤ GroupCat.{u₂} where
  obj := fun ⟨A, _⟩ => GroupCat.of <| Aut (A : C)
  map := by
    intro ⟨A, _⟩ ⟨B, _⟩ f
    exact (autMapMul F f : Aut (A : C) →* Aut (B : C))
  map_id := by
    intro ⟨⟨A, (hAgal : IsGalois A)⟩, a⟩
    ext (σ : Aut A)
    show autMap F (𝟙 A) a a σ = σ
    apply evaluation_aut_injective_of_isConnected F (A : C) a
    simp only [autMap_eval F (𝟙 A) a a σ, Category.comp_id]
  map_comp := by
    intro ⟨⟨A, (hAgal : IsGalois A)⟩, a⟩ ⟨⟨B, (hBgal : IsGalois B)⟩, b⟩
      ⟨⟨C, (hCgal : IsGalois C)⟩, c⟩ ⟨f, hf⟩ ⟨g, hg⟩
    ext (σ : Aut A)
    show autMap F (f ≫ g) a c σ = autMap F g b c (autMap F f a b σ)
    apply evaluation_aut_injective_of_isConnected F C c
    simp only [autMap_eval, map_comp, FintypeCat.comp_apply]

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

noncomputable example [UnivLE.{max u₁ u₂, u₂}] : GroupCat.{u₂} := limit (autGaloisSystem F)

noncomputable def autGaloisSystem' : (Idx F)ᵒᵖ ⥤ GroupCat.{max u₁ u₂} :=
  autGaloisSystem F ⋙ GroupCat.uliftFunctor.{u₂, u₁}

@[simp]
theorem autGaloisSystem'_map {A B : (Idx F)ᵒᵖ} (f : A ⟶ B) (φ : Aut (A.unop.1 : C)) :
    ((autGaloisSystem' F).map f) ⟨φ⟩ = ⟨autMapMul F f φ⟩ :=
  rfl

noncomputable def autGalois : GroupCat.{max u₁ u₂} := limit (autGaloisSystem' F)

noncomputable def autGalois.π (A : Idx F) : autGalois F →* Aut (A.1 : C) :=
  MonoidHom.comp MulEquiv.ulift.toMonoidHom (limit.π (autGaloisSystem' F) (Opposite.op A))

theorem autGalois.π_apply (A : Idx F) (x : autGalois F) :
    autGalois.π F A x = Equiv.ulift (limit.π (autGaloisSystem' F) (Opposite.op A) x) :=
  rfl

lemma autGalois_ext (f g : autGalois F)
    (h : ∀ (A : (Idx F)ᵒᵖ), autGalois.π F A.unop f = autGalois.π F A.unop g) : f = g := by
  apply Concrete.limit_ext (autGaloisSystem' F) f g
  intro ⟨A⟩
  have h1 : MulEquiv.ulift ((limit.π (autGaloisSystem' F) ⟨A⟩) f) =
    MulEquiv.ulift ((limit.π (autGaloisSystem' F) ⟨A⟩) g) := h ⟨A⟩
  exact (EquivLike.injective _) h1

lemma autGalois_ext' (x y : autGalois F)
    (h : ∀ (A : (Idx F)ᵒᵖ), limit.π (autGaloisSystem' F) A x = limit.π (autGaloisSystem' F) A y) : x = y :=
  Concrete.limit_ext (autGaloisSystem' F) x y h

instance : HasColimit ((can F).rightOp ⋙ coyoneda) where
  exists_colimit := ⟨cocone F, iscolimit F⟩

noncomputable def prorep : colimit ((can F).rightOp ⋙ coyoneda) ≅ F ⋙ FintypeCat.incl :=
  colimit.isoColimitCocone ⟨cocone F, iscolimit F⟩

local notation "F'" => F ⋙ FintypeCat.incl

noncomputable def iso0 : End F ≅ End (F ⋙ FintypeCat.incl) :=
  Equiv.toIso (NatTrans.equivOfCompFullyFaithful FintypeCat.incl)

noncomputable def iso1 : End F' ≅ (colimit ((can F).rightOp ⋙ coyoneda) ⟶ F') :=
  (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (prorep F).op

-- coproyoneda lemma
noncomputable def iso2 :
    (colimit ((can F).rightOp ⋙ coyoneda) ⟶ F') ≅ limit (can F ⋙ F' ⋙ uliftFunctor.{u₁}) :=
  procoyonedaIso (can F) F'

noncomputable def iso3 : End F ≅ limit (can F ⋙ F' ⋙ uliftFunctor.{u₁}) := by
  apply Iso.trans
  exact iso0 F
  apply Iso.trans (iso1 F) (iso2 F)

theorem iso3_pi (f : End F) (A : Idx F) :
    limit.π (can F ⋙ F' ⋙ uliftFunctor.{u₁}) ⟨A⟩ ((iso3 F).hom f) = ⟨f.app A.1 (A.2)⟩ := by
  apply ULift.ext
  simp [iso3, iso2, iso1, iso0, iso1, iso0, prorep]
  change ((NatTrans.equivOfCompFullyFaithful FintypeCat.incl) f).app A.1
    (((colimit.ι ((can F).rightOp.comp coyoneda) A) ≫ (colimit.isoColimitCocone ⟨cocone F, iscolimit F⟩).hom).app
      (A.1) _) = f.app A.fst A.snd
  simp

noncomputable def galautiso' :
    autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} ≅ can F ⋙ F' ⋙ uliftFunctor.{u₁} := by
  fapply NatIso.ofComponents
  · intro ⟨⟨⟨A, (hgal : IsGalois A)⟩,a⟩⟩
    apply Equiv.toIso
    exact (Equiv.ulift.{u₁, u₂}).trans
      ((evaluationEquivOfIsGalois F A a).trans Equiv.ulift.{u₁, u₂}.symm)
  · intro ⟨⟨⟨A, (_ : IsGalois A)⟩, a⟩⟩ ⟨⟨⟨B, (_ : IsGalois B)⟩, b⟩⟩ ⟨(f : A ⟶ B), hf⟩
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
    can F ⋙ F' ⋙ uliftFunctor.{u₁} ≅ autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} :=
  (galautiso' F).symm

@[simp]
theorem galautiso_app (A : Idx F) (b : F.obj A.1) :
    (galautiso F).hom.app (Opposite.op A) ⟨b⟩ =
      ⟨(evaluationEquivOfIsGalois F A.1 A.2).symm b⟩ :=
  rfl

noncomputable def iso4 : End F ≅ limit (autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂}) := by
  apply Iso.trans
  exact iso3 F
  exact lim.mapIso (galautiso F)

@[simp]
theorem iso4_pi_apply (A : Idx F) (f : End F) :
    limit.π (autGaloisSystem' F ⋙ forget _) (Opposite.op A) ((iso4 F).hom f) =
      ⟨(evaluationEquivOfIsGalois F A.fst A.snd).symm (f.app A.fst A.snd)⟩ := by
  simp [iso4]
  erw [iso3_pi]
  rw [galautiso_app]

noncomputable def iso5' : End F ≅ autGalois F := by
  show End F ≅ (forget GroupCat.{max u₁ u₂}).obj (limit (autGaloisSystem' F))
  apply Iso.trans
  exact iso4 F
  exact (preservesLimitIso (forget GroupCat.{max u₁ u₂}) (autGaloisSystem' F)).symm

noncomputable def iso5 : End F ≃ autGalois F := (iso5' F).toEquiv

lemma iso5_pi_foo (f : End F) (A : Idx F) :
    F.map (autGalois.π F A (iso5 F f)).hom A.2 = f.app A.1 A.2 := by
  simp [iso5, iso5']
  rw [autGalois.π_apply]
  change F.map
    (((iso4 F).hom
        ≫ (preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv
        ≫ (forget GroupCat).map (limit.π (autGaloisSystem' F) ⟨A⟩)) f).down.hom
    A.2 = _
  rw [preservesLimitsIso_inv_π]
  simp

@[simp]
theorem iso5_mul (f g : End F) : (iso5 F) (g ≫ f) = (iso5 F g) * (iso5 F f) := by
  apply autGalois_ext F
  intro ⟨⟨⟨A, (_ : IsGalois A)⟩, a⟩⟩
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
    (f.app A ≫ F.map ((autGalois.π F ⟨⟨A, _⟩, a⟩) ((iso5 F) g)).hom) a
  rw [← f.naturality]
  simp
  rw [iso5_pi_foo]

noncomputable def iso5Monoid : End F ≃* (autGalois F)ᵐᵒᵖ :=
  MulEquiv.mk (Equiv.trans (iso5 F) MulOpposite.opEquiv) (by simp)

lemma iso5Monoid_pi (f : End F) (A : Idx F) :
    F.map (autGalois.π F A (iso5Monoid F f).unop).hom A.2 = f.app A.1 A.2 :=
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

theorem autMulEquivAutGalois_π (f : Aut F) (A : C) [inst : IsGalois A] (a : F.obj A) :
    F.map (autGalois.π F ⟨⟨A, inst⟩, a⟩ (autMulEquivAutGalois F f).unop).hom a = f.hom.app A a := by
  simp [autMulEquivAutGalois, iso5Monoid]
  rw [iso5_pi_foo]
  rfl

@[simp]
theorem autMulEquivAutGalois_symm_app (x : autGalois F) (A : C) [IsGalois A] (a : F.obj A) :
    ((autMulEquivAutGalois F).symm ⟨x⟩).hom.app A a =
      F.map (autGalois.π F ⟨⟨A, (inferInstance : IsGalois A)⟩, a⟩ x).hom a := by
  rw [← autMulEquivAutGalois_π, MulEquiv.apply_symm_apply]
  rfl

lemma proj_surj (A : C) [inst : IsGalois A] (a : F.obj A) :
    Function.Surjective (autGalois.π F ⟨⟨A, inst⟩, a⟩) := fun (σ : Aut A) ↦ by
  have (i : (Idx F)ᵒᵖ) : Finite ((autGaloisSystem' F ⋙ forget _).obj i) :=
    inferInstanceAs <| Finite (ULift (Aut (i.1.1.1)))
  have fsur (i j : (Idx F)ᵒᵖ) (f : i ⟶ j) : Function.Surjective ((autGaloisSystem' F).map f) := by
    intro ⟨(φ : Aut j.1.1.1)⟩
    obtain ⟨ψ, hψ⟩ := autMap_surjective F f.1.1 i.1.2 j.1.2 φ
    use ⟨ψ⟩
    simp only [autGaloisSystem'_map]
    apply ULift.ext
    exact hψ
  have := eval_section_surjective_of_surjective (autGaloisSystem' F ⋙ forget _) fsur
  obtain ⟨s', hs⟩ := eval_section_surjective_of_surjective
    (autGaloisSystem' F ⋙ forget _) fsur ⟨⟨⟨A, inst⟩, a⟩⟩ ⟨σ⟩
  simp only [comp_obj] at hs
  let s : limit _ := (Types.limitEquivSections (autGaloisSystem' F ⋙ forget _)).symm s'
  let t : autGalois F := (preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv s
  use t
  simp [t, s, autGalois.π]
  change MulEquiv.ulift
      (((preservesLimitIso (forget GroupCat) (autGaloisSystem' F)).inv
        ≫ (forget _).map (limit.π (autGaloisSystem' F) { unop := ⟨⟨A, inst⟩, a⟩ }))
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

theorem pretransitive_of_galois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨(φ : Aut X), h⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X) x y
  obtain ⟨a, ha⟩ := proj_surj F X x φ
  use (autMulEquivAutGalois F).symm ⟨a⟩
  simpa [mulAction_def, ha]

instance pretransitive_of_isConnected (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := pretransitive_of_galois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [←ha, ←hb]
  show (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality, FintypeCat.comp_apply, hσ]
