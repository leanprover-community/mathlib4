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

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]

structure PointedGaloisObject : Type (max u₁ u₂) where
  obj : C
  pt : F.obj obj
  isGalois : IsGalois obj := by infer_instance

namespace PointedGaloisObject

attribute [instance] isGalois

instance (X : PointedGaloisObject F) : CoeDep (PointedGaloisObject F) X C where
  coe := X.obj

instance : Category.{u₂} (PointedGaloisObject F) where
  Hom A B := { f : (A : C) ⟶ B // F.map f A.pt = B.pt }
  id A := ⟨𝟙 (A : C), by simp⟩
  comp {A B C} f g := by
    refine ⟨f.val ≫ g.val, ?_⟩
    simp only [F.map_comp, FintypeCat.comp_apply, f.property, g.property]

instance : IsCofilteredOrEmpty (PointedGaloisObject F) where
  cone_objs := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ↦ by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F (A ⨯ B)
      <| (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨Z, z, hgal⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨f, hf⟩ ⟨g, hg⟩ ↦ by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_hom_from_galois_of_fiber F A a
    refine ⟨⟨Z, z, hgal⟩, ⟨h, hhz⟩, ?_⟩
    apply Subtype.ext
    apply evaluationInjective_of_isConnected F Z B z
    show F.map (h ≫ f) z = F.map (h ≫ g) z
    simp only [map_comp, FintypeCat.comp_apply, hhz, hf, hg]

end PointedGaloisObject

/-- The canonical (contravariant) functor from pointed Galois objects to `C`. -/
def can : PointedGaloisObject F ⥤ C where
  obj := fun A ↦ A
  map := fun ⟨f, _⟩ ↦ f

@[simp]
lemma can_obj (A : PointedGaloisObject F) : (can F).obj A = A :=
  rfl

@[simp]
lemma can_map_eq {A B : PointedGaloisObject F} (f : A ⟶ B) : ((can F).map f) = f.val :=
  rfl

def cocone : Cocone ((can F).op ⋙ coyoneda) where
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
    ((cocone F).ι.app ⟨A⟩).app B f = F.map f A.2 :=
  rfl

noncomputable def isColimit : IsColimit (cocone F) := by
  apply evaluationJointlyReflectsColimits
  intro X
  let G : (PointedGaloisObject F)ᵒᵖ ⥤ Type u₂ :=
    (((can F).op ⋙ coyoneda) ⋙ (evaluation C (Type u₂)).obj X)
  let s : Cocone G := ((evaluation C (Type u₂)).obj X).mapCocone (cocone F)
  show IsColimit s
  refine Types.FilteredColimit.isColimitOf G s ?_ ?_
  intro (x : F.obj X)
  obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
  obtain ⟨Z, f, z, hgal, hfz⟩ := exists_hom_from_galois_of_fiber F Y y
  use ⟨Z, z, hgal⟩
  use f ≫ i
  show x = F.map (f ≫ i) z
  simp only [←h1, map_comp, FintypeCat.comp_apply, hfz]
  intro ⟨A, a, _⟩ ⟨B, b, _⟩ (u : (A : C) ⟶ X) --(v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
  intro (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
  obtain ⟨⟨Z, z, _⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
    @IsFilteredOrEmpty.cocone_objs (PointedGaloisObject F)ᵒᵖ _ _
    ⟨{ obj := A, pt := a}⟩ ⟨{obj := B, pt := b}⟩
  refine ⟨⟨{ obj := Z, pt := z }⟩, ⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
  apply evaluationInjective_of_isConnected F Z X z
  show F.map (f ≫ u) z = F.map (g ≫ v) z
  rw [map_comp, FintypeCat.comp_apply, hf, map_comp, FintypeCat.comp_apply, hg, h]

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

noncomputable def autMapMul {A B : PointedGaloisObject F} (f : A ⟶ B) :
     Aut (A : C) →* Aut (B : C) :=
  MonoidHom.mk' _ (autMap_mul F f.val A.pt B.pt f.property)

noncomputable def autGaloisSystem : PointedGaloisObject F ⥤ GroupCat.{u₂} where
  obj := fun A ↦ GroupCat.of <| Aut (A : C)
  map := fun {A B} f ↦ (autMapMul F f : Aut (A : C) →* Aut (B : C))
  map_id := fun ⟨A, a, _⟩ ↦ by
    ext (σ : Aut (A : C))
    show autMap F (𝟙 A) a a σ = σ
    apply evaluation_aut_injective_of_isConnected F A a
    simp only [autMap_eval F (𝟙 A) a a σ, Category.comp_id]
  map_comp := by
    intro ⟨A, a, _⟩ ⟨B, b, _⟩ ⟨C, c, _⟩ ⟨f, hf⟩ ⟨g, hg⟩
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

noncomputable def autGaloisSystem' : PointedGaloisObject F ⥤ GroupCat.{max u₁ u₂} :=
  autGaloisSystem F ⋙ GroupCat.uliftFunctor.{u₂, u₁}

@[simp]
theorem autGaloisSystem'_map {A B : PointedGaloisObject F} (f : A ⟶ B) (φ : Aut (A : C)) :
    ((autGaloisSystem' F).map f) ⟨φ⟩ = ⟨autMapMul F f φ⟩ :=
  rfl

noncomputable def autGalois : GroupCat.{max u₁ u₂} := limit (autGaloisSystem' F)

noncomputable def autGalois.π (A : PointedGaloisObject F) : autGalois F →* Aut (A : C) :=
  MonoidHom.comp MulEquiv.ulift.toMonoidHom (limit.π (autGaloisSystem' F) A)

theorem autGalois.π_apply (A : PointedGaloisObject F) (x : autGalois F) :
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

instance : HasColimit ((can F).op ⋙ coyoneda) where
  exists_colimit := ⟨cocone F, isColimit F⟩

noncomputable def prorep : colimit ((can F).op ⋙ coyoneda) ≅ F ⋙ FintypeCat.incl :=
  colimit.isoColimitCocone ⟨cocone F, isColimit F⟩

local notation "F'" => F ⋙ FintypeCat.incl

noncomputable def iso0 : End F ≅ End (F ⋙ FintypeCat.incl) :=
  Equiv.toIso (NatTrans.equivOfCompFullyFaithful FintypeCat.incl)

noncomputable def iso1 : End F' ≅ (colimit ((can F).op ⋙ coyoneda) ⟶ F') :=
  (yoneda.obj (F ⋙ FintypeCat.incl)).mapIso (prorep F).op

-- coproyoneda lemma
noncomputable def iso2 :
    (colimit ((can F).op ⋙ coyoneda) ⟶ F') ≅ limit (can F ⋙ F' ⋙ uliftFunctor.{u₁}) :=
  procoyonedaIso' (can F) F'

noncomputable def iso3 : End F ≅ limit (can F ⋙ F' ⋙ uliftFunctor.{u₁}) := by
  apply Iso.trans
  exact iso0 F
  apply Iso.trans (iso1 F) (iso2 F)

theorem iso3_pi (f : End F) (A : PointedGaloisObject F) :
    limit.π (can F ⋙ F' ⋙ uliftFunctor.{u₁}) A ((iso3 F).hom f) = ⟨f.app A A.pt⟩ := by
  apply ULift.ext
  simp [iso3, iso2, iso1, iso0, iso1, iso0, prorep]
  change ((NatTrans.equivOfCompFullyFaithful FintypeCat.incl) f).app A
    (((colimit.ι ((can F).op.comp coyoneda) ⟨A⟩) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp

noncomputable def galautiso' :
    autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} ≅ can F ⋙ F' ⋙ uliftFunctor.{u₁} := by
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
    can F ⋙ F' ⋙ uliftFunctor.{u₁} ≅ autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂} :=
  (galautiso' F).symm

@[simp]
theorem galautiso_app (A : PointedGaloisObject F) (b : F.obj A) :
    (galautiso F).hom.app A ⟨b⟩ =
      ⟨(evaluationEquivOfIsGalois F A A.pt).symm b⟩ :=
  rfl

noncomputable def iso4 : End F ≅ limit (autGaloisSystem' F ⋙ forget GroupCat.{max u₁ u₂}) := by
  apply Iso.trans
  exact iso3 F
  exact lim.mapIso (galautiso F)

@[simp]
theorem iso4_pi_apply (A : PointedGaloisObject F) (f : End F) :
    limit.π (autGaloisSystem' F ⋙ forget _) A ((iso4 F).hom f) =
      ⟨(evaluationEquivOfIsGalois F A A.pt).symm (f.app A A.pt)⟩ := by
  simp [iso4]
  erw [iso3_pi]
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
    obtain ⟨ψ, hψ⟩ := autMap_surjective F f.val i.pt j.pt φ
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
