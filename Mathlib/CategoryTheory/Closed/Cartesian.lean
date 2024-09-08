/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
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
instance `monoidalOfHasFiniteProducts`.

We define exponentiable objects to be closed objects with respect to this monoidal structure,
i.e. `(X × -)` is a left adjoint.

We say a category is cartesian closed if every object is exponentiable
(equivalently, that the category equipped with the cartesian monoidal structure is closed monoidal).

Show that exponential forms a difunctor and define the exponential comparison morphisms.

## TODO
Some of the results here are true more generally for closed objects and
for closed monoidal categories, and these could be generalised.
-/


universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] monoidalOfHasFiniteProducts

/-- An object `X` is *exponentiable* if `(X × -)` is a left adjoint.
We define this as being `Closed` in the cartesian monoidal structure.
-/
abbrev Exponentiable {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C) :=
  Closed X

/-- Constructor for `Exponentiable X` which takes as an input an adjunction
`MonoidalCategory.tensorLeft X ⊣ exp` for some functor `exp : C ⥤ C`. -/
abbrev Exponentiable.mk {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C)
    (exp : C ⥤ C) (adj : MonoidalCategory.tensorLeft X ⊣ exp) :
    Exponentiable X where
  adj := adj

/-- If `X` and `Y` are exponentiable then `X ⨯ Y` is.
This isn't an instance because it's not usually how we want to construct exponentials, we'll usually
prove all objects are exponential uniformly.
-/
def binaryProductExponentiable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {X Y : C}
    (hX : Exponentiable X) (hY : Exponentiable Y) : Exponentiable (X ⨯ Y) :=
  tensorClosed hX hY

/-- The terminal object is always exponentiable.
This isn't an instance because most of the time we'll prove cartesian closed for all objects
at once, rather than just for this one.
-/
def terminalExponentiable {C : Type u} [Category.{v} C] [HasFiniteProducts C] :
    Exponentiable (⊤_ C) :=
  unitClosed

/-- A category `C` is cartesian closed if it has finite products and every object is exponentiable.
We define this as `monoidal_closed` with respect to the cartesian monoidal structure.
-/
abbrev CartesianClosed (C : Type u) [Category.{v} C] [HasFiniteProducts C] :=
  MonoidalClosed C

-- Porting note: added to ease the port of `CategoryTheory.Closed.Types`
/-- Constructor for `CartesianClosed C`. -/
def CartesianClosed.mk (C : Type u) [Category.{v} C] [HasFiniteProducts C]
    (exp : ∀ (X : C), Exponentiable X) :
    CartesianClosed C where
  closed X := exp X

variable {C : Type u} [Category.{v} C] (A B : C) {X X' Y Y' Z : C}
variable [HasFiniteProducts C] [Exponentiable A]

/-- This is (-)^A. -/
abbrev exp : C ⥤ C :=
  ihom A

namespace exp

/-- The adjunction between A ⨯ - and (-)^A. -/
abbrev adjunction : prod.functor.obj A ⊣ exp A :=
  ihom.adjunction A

/-- The evaluation natural transformation. -/
abbrev ev : exp A ⋙ prod.functor.obj A ⟶ 𝟭 C :=
  ihom.ev A

/-- The coevaluation natural transformation. -/
abbrev coev : 𝟭 C ⟶ prod.functor.obj A ⋙ exp A :=
  ihom.coev A

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms obtained using an exponentiable object. -/
notation:20 A " ⟹ " B:19 => (exp A).obj B

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Prefunctor.obj` -/
@[delab app.Prefunctor.obj]
def delabPrefunctorObjExp : Delab := whenPPOption getPPNotation <| withOverApp 6 <| do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Prefunctor.obj 6
  let A ← withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``Functor.toPrefunctor 5
    withNaryArg 4 do
      let e ← getExpr
      guard <| e.isAppOfArity' ``exp 5
      withNaryArg 2 delab
  let B ← withNaryArg 5 delab
  `($A ⟹ $B)

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms from an exponentiable object. -/
notation:30 B " ^^ " A:30 => (exp A).obj B

@[simp, reassoc]
theorem ev_coev : Limits.prod.map (𝟙 A) ((coev A).app B) ≫ (ev A).app (A ⨯ B) = 𝟙 (A ⨯ B) :=
  ihom.ev_coev A B

@[reassoc]
theorem coev_ev : (coev A).app (A ⟹ B) ≫ (exp A).map ((ev A).app B) = 𝟙 (A ⟹ B) :=
  ihom.coev_ev A B

end exp

instance : PreservesColimits (prod.functor.obj A) :=
  (ihom.adjunction A).leftAdjointPreservesColimits

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace CartesianClosed

/-- Currying in a cartesian closed category. -/
def curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) :=
  (exp.adjunction A).homEquiv _ _

/-- Uncurrying in a cartesian closed category. -/
def uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) :=
  ((exp.adjunction A).homEquiv _ _).symm

-- This lemma has always been bad, but the linter only noticed after lean4#2644.
@[simp, nolint simpNF]
theorem homEquiv_apply_eq (f : A ⨯ Y ⟶ X) : (exp.adjunction A).homEquiv _ _ f = curry f :=
  rfl

-- This lemma has always been bad, but the linter only noticed after lean4#2644.
@[simp, nolint simpNF]
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟹ X) :
    ((exp.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) :
    curry (Limits.prod.map (𝟙 _) f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
theorem curry_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (exp _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A ⟹ Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (exp _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟹ Y) :
    uncurry (f ≫ g) = Limits.prod.map (𝟙 _) f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : A ⨯ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟹ Y) : curry (uncurry f) = f :=
  (Closed.adj.homEquiv _ _).right_inv f

-- Porting note: extra `(exp.adjunction A)` argument was needed for elaboration to succeed.
theorem curry_eq_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (exp.adjunction A) f g

-- Porting note: extra `(exp.adjunction A)` argument was needed for elaboration to succeed.
theorem eq_curry_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (exp.adjunction A) f g

-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ A ⟹ X) : uncurry g = Limits.prod.map (𝟙 A) g ≫ (exp.ev A).app X :=
  Adjunction.homEquiv_counit _

theorem curry_eq (g : A ⨯ Y ⟶ X) : curry g = (exp.coev A).app Y ≫ (exp A).map g :=
  Adjunction.homEquiv_unit _

theorem uncurry_id_eq_ev (A X : C) [Exponentiable A] : uncurry (𝟙 (A ⟹ X)) = (exp.ev A).app X := by
  rw [uncurry_eq, prod.map_id_id, id_comp]

theorem curry_id_eq_coev (A X : C) [Exponentiable A] : curry (𝟙 _) = (exp.coev A).app X := by
  rw [curry_eq, (exp A).map_id (A ⨯ _)]; apply comp_id

theorem curry_injective : Function.Injective (curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X)) :=
  (Closed.adj.homEquiv _ _).injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X)) :=
  (Closed.adj.homEquiv _ _).symm.injective

end CartesianClosed

open CartesianClosed

/-- Show that the exponential of the terminal object is isomorphic to itself, i.e. `X^1 ≅ X`.

The typeclass argument is explicit: any instance can be used.
-/
def expTerminalIsoSelf [Exponentiable (⊤_ C)] : (⊤_ C) ⟹ X ≅ X :=
  Yoneda.ext ((⊤_ C) ⟹ X) X
    (fun {Y} f => (Limits.prod.leftUnitor Y).inv ≫ CartesianClosed.uncurry f)
    (fun {Y} f => CartesianClosed.curry ((Limits.prod.leftUnitor Y).hom ≫ f))
    (fun g => by
      rw [curry_eq_iff, Iso.hom_inv_id_assoc])
    (fun g => by simp)
    (fun f g => by
      -- Porting note: `rw` is a bit brittle here, requiring the `dsimp` rule cancellation.
      dsimp [-prod.leftUnitor_inv]
      rw [uncurry_natural_left, prod.leftUnitor_inv_naturality_assoc f])

/-- The internal element which points at the given morphism. -/
def internalizeHom (f : A ⟶ Y) : ⊤_ C ⟶ A ⟹ Y :=
  CartesianClosed.curry (Limits.prod.fst ≫ f)

section Pre

variable {B}

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) [Exponentiable B] : exp A ⟶ exp B :=
  conjugateEquiv (exp.adjunction _) (exp.adjunction _) (prod.functor.map f)

theorem prod_map_pre_app_comp_ev (f : B ⟶ A) [Exponentiable B] (X : C) :
    Limits.prod.map (𝟙 B) ((pre f).app X) ≫ (exp.ev B).app X =
      Limits.prod.map f (𝟙 (A ⟹ X)) ≫ (exp.ev A).app X :=
  conjugateEquiv_counit _ _ (prod.functor.map f) X

theorem uncurry_pre (f : B ⟶ A) [Exponentiable B] (X : C) :
    CartesianClosed.uncurry ((pre f).app X) = Limits.prod.map f (𝟙 _) ≫ (exp.ev A).app X := by
  rw [uncurry_eq, prod_map_pre_app_comp_ev]

theorem coev_app_comp_pre_app (f : B ⟶ A) [Exponentiable B] :
    (exp.coev A).app X ≫ (pre f).app (A ⨯ X) =
      (exp.coev B).app X ≫ (exp B).map (Limits.prod.map f (𝟙 _)) :=
  unit_conjugateEquiv _ _ (prod.functor.map f) X

@[simp]
theorem pre_id (A : C) [Exponentiable A] : pre (𝟙 A) = 𝟙 _ := by simp [pre]

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Exponentiable A₁] [Exponentiable A₂] [Exponentiable A₃]
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) : pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp, prod.functor.map_comp]

end Pre

/-- The internal hom functor given by the cartesian closed structure. -/
def internalHom [CartesianClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := exp X.unop
  map f := pre f.unop

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
def zeroMul {I : C} (t : IsInitial I) : A ⨯ I ≅ I where
  hom := Limits.prod.snd
  inv := t.to _
  hom_inv_id := by
    have : (prod.snd : A ⨯ I ⟶ I) = CartesianClosed.uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mulZero {I : C} (t : IsInitial I) : I ⨯ A ≅ I :=
  Limits.prod.braiding _ _ ≪≫ zeroMul t

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def powZero {I : C} (t : IsInitial I) [CartesianClosed C] : I ⟹ B ≅ ⊤_ C where
  hom := default
  inv := CartesianClosed.curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mulZero t).inv]
    apply t.hom_ext

-- TODO: Generalise the below to its commuted variants.
-- TODO: Define a distributive category, so that zero_mul and friends can be derived from this.
/-- In a CCC with binary coproducts, the distribution morphism is an isomorphism. -/
def prodCoprodDistrib [HasBinaryCoproducts C] [CartesianClosed C] (X Y Z : C) :
    (Z ⨯ X) ⨿ Z ⨯ Y ≅ Z ⨯ X ⨿ Y where
  hom := coprod.desc (Limits.prod.map (𝟙 _) coprod.inl) (Limits.prod.map (𝟙 _) coprod.inr)
  inv :=
    CartesianClosed.uncurry
      (coprod.desc (CartesianClosed.curry coprod.inl) (CartesianClosed.curry coprod.inr))
  hom_inv_id := by
    ext
    · rw [coprod.inl_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inl_desc, uncurry_curry]
    rw [coprod.inr_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inr_desc, uncurry_curry]
  inv_hom_id := by
    rw [← uncurry_natural_right, ← eq_curry_iff]
    ext
    · rw [coprod.inl_desc_assoc, ← curry_natural_right, coprod.inl_desc, ← curry_natural_left,
        comp_id]
    rw [coprod.inr_desc_assoc, ← curry_natural_right, coprod.inr_desc, ← curry_natural_left,
      comp_id]

/-- If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  haveI : Mono f := by
    rw [← prod.lift_snd (𝟙 A) f, ← zeroMul_hom t]
    exact mono_comp _ _
  haveI : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [CartesianClosed C] : Mono (t.to B) :=
  ⟨fun g h _ => by
    haveI := strict_initial t g
    haveI := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

instance Initial.mono_to [HasInitial C] (B : C) [CartesianClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial

variable {D : Type u₂} [Category.{v₂} D]

section Functor

variable [HasFiniteProducts D]

/-- Transport the property of being cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prodComparison` isomorphism.
-/
def cartesianClosedOfEquiv (e : C ≌ D) [CartesianClosed C] : CartesianClosed D :=
  MonoidalClosed.ofEquiv (e.inverse.toMonoidalFunctorOfHasFiniteProducts) e.symm.toAdjunction

end Functor

attribute [nolint simpNF] CategoryTheory.CartesianClosed.homEquiv_apply_eq
  CategoryTheory.CartesianClosed.homEquiv_symm_apply_eq
end CategoryTheory
