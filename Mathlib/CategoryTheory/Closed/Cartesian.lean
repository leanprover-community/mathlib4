/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read

! This file was ported from Lean 3 source module category_theory.closed.cartesian
! leanprover-community/mathlib commit 239d882c4fb58361ee8b3b39fb2091320edef10a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# Cartesian closed categories

Given a category with finite products, the cartesian monoidal structure is provided by the local
instance `monoidal_of_has_finite_products`.

We define exponentiable objects to be closed objects with respect to this monoidal structure,
i.e. `(X × -)` is a left adjoint.

We say a category is cartesian closed if every object is exponentiable
(equivalently, that the category equipped with the cartesian monoidal structure is closed monoidal).

Show that exponential forms a difunctor and define the exponential comparison morphisms.

## TODO
Some of the results here are true more generally for closed objects and
for closed monoidal categories, and these could be generalised.
-/


universe v u u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] monoidal_of_has_finite_products

/-- An object `X` is *exponentiable* if `(X × -)` is a left adjoint.
We define this as being `closed` in the cartesian monoidal structure.
-/
abbrev Exponentiable {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C) :=
  Closed X
#align category_theory.exponentiable CategoryTheory.Exponentiable

/-- If `X` and `Y` are exponentiable then `X ⨯ Y` is.
This isn't an instance because it's not usually how we want to construct exponentials, we'll usually
prove all objects are exponential uniformly.
-/
def binaryProductExponentiable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {X Y : C}
    (hX : Exponentiable X) (hY : Exponentiable Y) : Exponentiable (X ⨯ Y) :=
  tensorClosed hX hY
#align category_theory.binary_product_exponentiable CategoryTheory.binaryProductExponentiable

/-- The terminal object is always exponentiable.
This isn't an instance because most of the time we'll prove cartesian closed for all objects
at once, rather than just for this one.
-/
def terminalExponentiable {C : Type u} [Category.{v} C] [HasFiniteProducts C] :
    Exponentiable (⊤_ C) :=
  unitClosed
#align category_theory.terminal_exponentiable CategoryTheory.terminalExponentiable

/-- A category `C` is cartesian closed if it has finite products and every object is exponentiable.
We define this as `monoidal_closed` with respect to the cartesian monoidal structure.
-/
abbrev CartesianClosed (C : Type u) [Category.{v} C] [HasFiniteProducts C] :=
  MonoidalClosed C
#align category_theory.cartesian_closed CategoryTheory.CartesianClosed

variable {C : Type u} [Category.{v} C] (A B : C) {X X' Y Y' Z : C}

variable [HasFiniteProducts C] [Exponentiable A]

/-- This is (-)^A. -/
abbrev exp : C ⥤ C :=
  ihom A
#align category_theory.exp CategoryTheory.exp

namespace exp

/-- The adjunction between A ⨯ - and (-)^A. -/
abbrev adjunction : prod.functor.obj A ⊣ exp A :=
  ihom.adjunction A
#align category_theory.exp.adjunction CategoryTheory.exp.adjunction

/-- The evaluation natural transformation. -/
abbrev ev : exp A ⋙ prod.functor.obj A ⟶ 𝟭 C :=
  ihom.ev A
#align category_theory.exp.ev CategoryTheory.exp.ev

/-- The coevaluation natural transformation. -/
abbrev coev : 𝟭 C ⟶ prod.functor.obj A ⋙ exp A :=
  ihom.coev A
#align category_theory.exp.coev CategoryTheory.exp.coev

-- mathport name: «expr ⟹ »
notation:20 A " ⟹ " B:19 => (exp A).obj B

-- mathport name: «expr ^^ »
notation:30 B " ^^ " A:30 => (exp A).obj B

@[simp, reassoc]
theorem ev_coev : Limits.prod.map (𝟙 A) ((coev A).app B) ≫ (ev A).app (A ⨯ B) = 𝟙 (A ⨯ B) :=
  ihom.ev_coev A B
#align category_theory.exp.ev_coev CategoryTheory.exp.ev_coev

@[simp, reassoc]
theorem coev_ev : (coev A).app (A ⟹ B) ≫ (exp A).map ((ev A).app B) = 𝟙 (A ⟹ B) :=
  ihom.coev_ev A B
#align category_theory.exp.coev_ev CategoryTheory.exp.coev_ev

end exp

instance : PreservesColimits (prod.functor.obj A) :=
  (ihom.adjunction A).leftAdjointPreservesColimits

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace CartesianClosed

/-- Currying in a cartesian closed category. -/
def curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) :=
  (exp.adjunction A).homEquiv _ _
#align category_theory.cartesian_closed.curry CategoryTheory.CartesianClosed.curry

/-- Uncurrying in a cartesian closed category. -/
def uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) :=
  ((exp.adjunction A).homEquiv _ _).symm
#align category_theory.cartesian_closed.uncurry CategoryTheory.CartesianClosed.uncurry

@[simp]
theorem homEquiv_apply_eq (f : A ⨯ Y ⟶ X) : (exp.adjunction A).homEquiv _ _ f = curry f :=
  rfl
#align category_theory.cartesian_closed.hom_equiv_apply_eq CategoryTheory.CartesianClosed.homEquiv_apply_eq

@[simp]
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟹ X) :
    ((exp.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl
#align category_theory.cartesian_closed.hom_equiv_symm_apply_eq CategoryTheory.CartesianClosed.homEquiv_symm_apply_eq

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) :
    curry (Limits.prod.map (𝟙 _) f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _
#align category_theory.cartesian_closed.curry_natural_left CategoryTheory.CartesianClosed.curry_natural_left

@[reassoc]
theorem curry_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (exp _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _
#align category_theory.cartesian_closed.curry_natural_right CategoryTheory.CartesianClosed.curry_natural_right

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A ⟹ Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (exp _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _
#align category_theory.cartesian_closed.uncurry_natural_right CategoryTheory.CartesianClosed.uncurry_natural_right

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟹ Y) :
    uncurry (f ≫ g) = Limits.prod.map (𝟙 _) f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _
#align category_theory.cartesian_closed.uncurry_natural_left CategoryTheory.CartesianClosed.uncurry_natural_left

@[simp]
theorem uncurry_curry (f : A ⨯ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.isAdj.adj.homEquiv _ _).left_inv f
#align category_theory.cartesian_closed.uncurry_curry CategoryTheory.CartesianClosed.uncurry_curry

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟹ Y) : curry (uncurry f) = f :=
  (Closed.isAdj.adj.homEquiv _ _).right_inv f
#align category_theory.cartesian_closed.curry_uncurry CategoryTheory.CartesianClosed.curry_uncurry

theorem curry_eq_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq _ f g
#align category_theory.cartesian_closed.curry_eq_iff CategoryTheory.CartesianClosed.curry_eq_iff

theorem eq_curry_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply _ f g
#align category_theory.cartesian_closed.eq_curry_iff CategoryTheory.CartesianClosed.eq_curry_iff

-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ A ⟹ X) : uncurry g = Limits.prod.map (𝟙 A) g ≫ (exp.ev A).app X :=
  Adjunction.homEquiv_counit _
#align category_theory.cartesian_closed.uncurry_eq CategoryTheory.CartesianClosed.uncurry_eq

theorem curry_eq (g : A ⨯ Y ⟶ X) : curry g = (exp.coev A).app Y ≫ (exp A).map g :=
  Adjunction.homEquiv_unit _
#align category_theory.cartesian_closed.curry_eq CategoryTheory.CartesianClosed.curry_eq

theorem uncurry_id_eq_ev (A X : C) [Exponentiable A] : uncurry (𝟙 (A ⟹ X)) = (exp.ev A).app X := by
  rw [uncurry_eq, prod.map_id_id, id_comp]
#align category_theory.cartesian_closed.uncurry_id_eq_ev CategoryTheory.CartesianClosed.uncurry_id_eq_ev

theorem curry_id_eq_coev (A X : C) [Exponentiable A] : curry (𝟙 _) = (exp.coev A).app X := by
  rw [curry_eq, (exp A).map_id (A ⨯ _)]; apply comp_id
#align category_theory.cartesian_closed.curry_id_eq_coev CategoryTheory.CartesianClosed.curry_id_eq_coev

theorem curry_injective : Function.Injective (curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X)) :=
  (Closed.isAdj.adj.homEquiv _ _).Injective
#align category_theory.cartesian_closed.curry_injective CategoryTheory.CartesianClosed.curry_injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X)) :=
  (Closed.isAdj.adj.homEquiv _ _).symm.Injective
#align category_theory.cartesian_closed.uncurry_injective CategoryTheory.CartesianClosed.uncurry_injective

end CartesianClosed

open CartesianClosed

/-- Show that the exponential of the terminal object is isomorphic to itself, i.e. `X^1 ≅ X`.

The typeclass argument is explicit: any instance can be used.
-/
def expTerminalIsoSelf [Exponentiable (⊤_ C)] : (⊤_ C) ⟹ X ≅ X :=
  Yoneda.ext ((⊤_ C) ⟹ X) X (fun Y f => (prod.leftUnitor Y).inv ≫ CartesianClosed.uncurry f)
    (fun Y f => CartesianClosed.curry ((prod.leftUnitor Y).Hom ≫ f))
    (fun Z g => by rw [curry_eq_iff, iso.hom_inv_id_assoc]) (fun Z g => by simp) fun Z W f g => by
    rw [uncurry_natural_left, prod.left_unitor_inv_naturality_assoc f]
#align category_theory.exp_terminal_iso_self CategoryTheory.expTerminalIsoSelf

/-- The internal element which points at the given morphism. -/
def internalizeHom (f : A ⟶ Y) : ⊤_ C ⟶ A ⟹ Y :=
  CartesianClosed.curry (Limits.prod.fst ≫ f)
#align category_theory.internalize_hom CategoryTheory.internalizeHom

section Pre

variable {B}

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) [Exponentiable B] : exp A ⟶ exp B :=
  transferNatTransSelf (exp.adjunction _) (exp.adjunction _) (prod.functor.map f)
#align category_theory.pre CategoryTheory.pre

theorem prod_map_pre_app_comp_ev (f : B ⟶ A) [Exponentiable B] (X : C) :
    Limits.prod.map (𝟙 B) ((pre f).app X) ≫ (exp.ev B).app X =
      Limits.prod.map f (𝟙 (A ⟹ X)) ≫ (exp.ev A).app X :=
  transferNatTransSelf_counit _ _ (prod.functor.map f) X
#align category_theory.prod_map_pre_app_comp_ev CategoryTheory.prod_map_pre_app_comp_ev

theorem uncurry_pre (f : B ⟶ A) [Exponentiable B] (X : C) :
    CartesianClosed.uncurry ((pre f).app X) = Limits.prod.map f (𝟙 _) ≫ (exp.ev A).app X := by
  rw [uncurry_eq, prod_map_pre_app_comp_ev]
#align category_theory.uncurry_pre CategoryTheory.uncurry_pre

theorem coev_app_comp_pre_app (f : B ⟶ A) [Exponentiable B] :
    (exp.coev A).app X ≫ (pre f).app (A ⨯ X) =
      (exp.coev B).app X ≫ (exp B).map (Limits.prod.map f (𝟙 _)) :=
  unit_transferNatTransSelf _ _ (prod.functor.map f) X
#align category_theory.coev_app_comp_pre_app CategoryTheory.coev_app_comp_pre_app

@[simp]
theorem pre_id (A : C) [Exponentiable A] : pre (𝟙 A) = 𝟙 _ := by simp [pre]
#align category_theory.pre_id CategoryTheory.pre_id

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Exponentiable A₁] [Exponentiable A₂] [Exponentiable A₃]
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) : pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, transfer_nat_trans_self_comp, prod.functor.map_comp]
#align category_theory.pre_map CategoryTheory.pre_map

end Pre

/-- The internal hom functor given by the cartesian closed structure. -/
def internalHom [CartesianClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := exp X.unop
  map X Y f := pre f.unop
#align category_theory.internal_hom CategoryTheory.internalHom

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
def zeroMul {I : C} (t : IsInitial I) : A ⨯ I ≅ I where
  Hom := Limits.prod.snd
  inv := t.to _
  hom_inv_id' := by
    have : (limits.prod.snd : A ⨯ I ⟶ I) = cartesian_closed.uncurry (t.to _)
    rw [← curry_eq_iff]
    apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id' := t.hom_ext _ _
#align category_theory.zero_mul CategoryTheory.zeroMul

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mulZero {I : C} (t : IsInitial I) : I ⨯ A ≅ I :=
  Limits.prod.braiding _ _ ≪≫ zeroMul t
#align category_theory.mul_zero CategoryTheory.mulZero

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def powZero {I : C} (t : IsInitial I) [CartesianClosed C] : I ⟹ B ≅ ⊤_ C where
  Hom := default
  inv := CartesianClosed.curry ((mulZero t).Hom ≫ t.to _)
  hom_inv_id' := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (MulZeroClass.mul_zero t).inv]
    · apply t.hom_ext
    · infer_instance
    · infer_instance
#align category_theory.pow_zero CategoryTheory.powZero

-- TODO: Generalise the below to its commutated variants.
-- TODO: Define a distributive category, so that zero_mul and friends can be derived from this.
/-- In a CCC with binary coproducts, the distribution morphism is an isomorphism. -/
def prodCoprodDistrib [HasBinaryCoproducts C] [CartesianClosed C] (X Y Z : C) :
    (Z ⨯ X) ⨿ Z ⨯ Y ≅ Z ⨯ X ⨿ Y where
  Hom := coprod.desc (Limits.prod.map (𝟙 _) coprod.inl) (Limits.prod.map (𝟙 _) coprod.inr)
  inv :=
    CartesianClosed.uncurry
      (coprod.desc (CartesianClosed.curry coprod.inl) (CartesianClosed.curry coprod.inr))
  hom_inv_id' := by
    apply coprod.hom_ext
    rw [coprod.inl_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inl_desc, uncurry_curry]
    rw [coprod.inr_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inr_desc, uncurry_curry]
  inv_hom_id' := by
    rw [← uncurry_natural_right, ← eq_curry_iff]
    apply coprod.hom_ext
    rw [coprod.inl_desc_assoc, ← curry_natural_right, coprod.inl_desc, ← curry_natural_left,
      comp_id]
    rw [coprod.inr_desc_assoc, ← curry_natural_right, coprod.inr_desc, ← curry_natural_left,
      comp_id]
#align category_theory.prod_coprod_distrib CategoryTheory.prodCoprodDistrib

/-- If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  haveI : mono (limits.prod.lift (𝟙 A) f ≫ (MulZeroClass.zero_mul t).Hom) := mono_comp _ _
  rw [zero_mul_hom, prod.lift_snd] at _inst 
  haveI : is_split_epi f := is_split_epi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply is_iso_of_mono_of_is_split_epi
#align category_theory.strict_initial CategoryTheory.strict_initial

instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _
#align category_theory.to_initial_is_iso CategoryTheory.to_initial_isIso

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [CartesianClosed C] : Mono (t.to B) :=
  ⟨fun B g h _ => by
    haveI := strict_initial t g
    haveI := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩
#align category_theory.initial_mono CategoryTheory.initial_mono

instance Initial.mono_to [HasInitial C] (B : C) [CartesianClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial
#align category_theory.initial.mono_to CategoryTheory.Initial.mono_to

variable {D : Type u₂} [Category.{v} D]

section Functor

variable [HasFiniteProducts D]

/-- Transport the property of being cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prod_comparison` isomorphism.
-/
def cartesianClosedOfEquiv (e : C ≌ D) [h : CartesianClosed C] : CartesianClosed D
    where closed' X :=
    {
      isAdj := by
        haveI q : exponentiable (e.inverse.obj X) := inferInstance
        have : is_left_adjoint (prod.functor.obj (e.inverse.obj X)) := q.is_adj
        have : e.functor ⋙ prod.functor.obj X ⋙ e.inverse ≅ prod.functor.obj (e.inverse.obj X)
        apply nat_iso.of_components _ _
        intro Y
        · apply as_iso (prod_comparison e.inverse X (e.functor.obj Y)) ≪≫ _
          apply prod.map_iso (iso.refl _) (e.unit_iso.app Y).symm
        · intro Y Z g
          dsimp [prod_comparison]
          simp [prod.comp_lift, ← e.inverse.map_comp, ← e.inverse.map_comp_assoc]
          -- I wonder if it would be a good idea to make `map_comp` a simp lemma the other way round
          dsimp;
          simp
        -- See note [dsimp, simp]
        · have : is_left_adjoint (e.functor ⋙ prod.functor.obj X ⋙ e.inverse) :=
            adjunction.left_adjoint_of_nat_iso this.symm
          have : is_left_adjoint (e.inverse ⋙ e.functor ⋙ prod.functor.obj X ⋙ e.inverse) :=
            adjunction.left_adjoint_of_comp e.inverse _
          have :
            (e.inverse ⋙ e.functor ⋙ prod.functor.obj X ⋙ e.inverse) ⋙ e.functor ≅
              prod.functor.obj X := by
            apply iso_whisker_right e.counit_iso (prod.functor.obj X ⋙ e.inverse ⋙ e.functor) ≪≫ _
            change prod.functor.obj X ⋙ e.inverse ⋙ e.functor ≅ prod.functor.obj X
            apply iso_whisker_left (prod.functor.obj X) e.counit_iso
          skip
          apply adjunction.left_adjoint_of_nat_iso this }
#align category_theory.cartesian_closed_of_equiv CategoryTheory.cartesianClosedOfEquiv

end Functor

end CategoryTheory

