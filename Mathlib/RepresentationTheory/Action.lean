/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Linear.FunctorCategory

#align_import representation_theory.Action from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = ModuleCat R`,
where `Action (ModuleCat R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (singleObj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.

* When `V` has (co)limits so does `Action V G`.
* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/


universe u v

open CategoryTheory Limits

variable (V : Type (u + 1)) [LargeCategory V]

-- Note: this is _not_ a categorical action of `G` on `V`.
/-- An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
structure Action (G : MonCat.{u}) where
  V : V
  ρ : G ⟶ MonCat.of (End V)

namespace Action

variable {V}

@[simp 1100]
theorem ρ_one {G : MonCat.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V := by rw [MonoidHom.map_one]; rfl

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρAut {G : GroupCat.{u}} (A : Action V (MonCat.of G)) : G ⟶ GroupCat.of (Aut A.V) where
  toFun g :=
    { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] Action.ρAut_apply_inv Action.ρAut_apply_hom

variable (G : MonCat.{u})

section

instance inhabited' : Inhabited (Action (Type u) G) :=
  ⟨⟨PUnit, 1⟩⟩

/-- The trivial representation of a group. -/
def trivial : Action AddCommGroupCat G where
  V := AddCommGroupCat.of PUnit
  ρ := 1

instance : Inhabited (Action AddCommGroupCat G) :=
  ⟨trivial G⟩

end

variable {G}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure Hom (M N : Action V G) where
  hom : M.V ⟶ N.V
  comm : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by aesop_cat

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

/-- The identity morphism on an `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.Hom M M where hom := 𝟙 M.V

instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  hom := p.hom ≫ q.hom

end Hom

instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g

-- porting note: added because `Hom.ext` is not triggered automatically
@[ext]
lemma hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Hom.ext _ _ h

@[simp]
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V :=
  rfl

@[simp]
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mkIso {M N : Action V G} (f : M.V ≅ N.V)
    (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g := by aesop_cat) : M ≅ N where
  hom :=
    { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }

instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := IsIso.of_iso (mkIso (asIso f.hom) f.comm)

instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) :
    @IsIso _ _ M N (Hom.mk f w) :=
  IsIso.of_iso (mkIso (asIso f) w)

namespace FunctorCategoryEquivalence

/-- Auxilliary definition for `functorCategoryEquivalence`. -/
@[simps]
def functor : Action V G ⥤ SingleObj G ⥤ V where
  obj M :=
    { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }

/-- Auxilliary definition for `functorCategoryEquivalence`. -/
@[simps]
def inverse : (SingleObj G ⥤ V) ⥤ Action V G where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }

/-- Auxilliary definition for `functorCategoryEquivalence`. -/
@[simps!]
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

/-- Auxilliary definition for `functorCategoryEquivalence`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents fun M => NatIso.ofComponents fun X => Iso.refl _

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `singleObj G ⥤ V`.
-/
@[simps]
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

/-
porting note: these two lemmas are redundant with the projections created by the @[simps]
attribute above

theorem functorCategoryEquivalence.functor_def :
    (functorCategoryEquivalence V G).functor = FunctorCategoryEquivalence.functor :=
  rfl

theorem functorCategoryEquivalence.inverse_def :
    (functorCategoryEquivalence V G).inverse = FunctorCategoryEquivalence.inverse :=
  rfl
-/

instance [HasFiniteProducts V] : HasFiniteProducts (Action V G) where
  out _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasFiniteLimits V] : HasFiniteLimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

end

section Forget

variable (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `CategoryTheory.forget` API provided by the `ConcreteCategory` instance below,
rather than using this directly.
-/
@[simps]
def forget : Action V G ⥤ V where
  obj M := M.V
  map f := f.hom

instance : Faithful (forget V G) where map_injective w := Hom.ext _ _ w

instance [ConcreteCategory V] : ConcreteCategory (Action V G) where
  forget := forget V G ⋙ ConcreteCategory.forget

instance hasForgetToV [ConcreteCategory V] : HasForget₂ (Action V G) V where forget₂ := forget V G

/-- The forgetful functor is intertwined by `functorCategoryEquivalence` with
evaluation at `PUnit.star`. -/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _

noncomputable instance instPreservesLimitsForget [HasLimits V] :
    Limits.PreservesLimits (forget V G) :=
  Limits.preservesLimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

noncomputable instance instPreservesColimitsForget [HasColimits V] :
    PreservesColimits (forget V G) :=
  preservesColimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) :=
      by rw [Iso.conj_apply, Iso.eq_inv_comp]; simp [f.hom.comm]

section HasZeroMorphisms

variable [HasZeroMorphisms V]

-- porting note: in order to ease automation, the `Zero` instance is introduced separately,
-- and the lemma `zero_hom` was moved just below
instance {X Y : Action V G} : Zero (X ⟶ Y) := ⟨0, by aesop_cat⟩

@[simp]
theorem zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 :=
  rfl

instance : HasZeroMorphisms (Action V G) where

instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where

instance forget₂_preservesZeroMorphisms [ConcreteCategory V] :
    Functor.PreservesZeroMorphisms (forget₂ (Action V G) V) where

instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).functor where

end HasZeroMorphisms

section Preadditive

variable [Preadditive V]

instance : Preadditive (Action V G) where
  homGroup X Y :=
    { add := fun f g => ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩
      neg := fun f => ⟨-f.hom, by simp [f.comm]⟩
      zero_add := by intros; ext; exact zero_add _
      add_zero := by intros; ext; exact add_zero _
      add_assoc := by intros; ext; exact add_assoc _ _ _
      add_left_neg := by intros; ext; exact add_left_neg _
      add_comm := by intros; ext; exact add_comm _ _ }
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _

instance forget_additive : Functor.Additive (forget V G) where

instance forget₂_additive [ConcreteCategory V] : Functor.Additive (forget₂ (Action V G) V) where

instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).functor where

@[simp]
theorem neg_hom {X Y : Action V G} (f : X ⟶ Y) : (-f).hom = -f.hom :=
  rfl

@[simp]
theorem add_hom {X Y : Action V G} (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom :=
  rfl

@[simp]
theorem sum_hom {X Y : Action V G} {ι : Type*} (f : ι → (X ⟶ Y)) (s : Finset ι) :
    (s.sum f).hom = s.sum fun i => (f i).hom :=
  (forget V G).map_sum f s

end Preadditive

section Linear

variable [Preadditive V] {R : Type*} [Semiring R] [Linear R V]

instance : Linear R (Action V G) where
  homModule X Y :=
    { smul := fun r f => ⟨r • f.hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext; exact smul_add _ _ _
      mul_smul := by intros; ext; exact mul_smul _ _ _ }
  smul_comp := by intros; ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul := by intros; ext; exact Linear.comp_smul _ _ _ _ _ _

instance forget_linear : Functor.Linear R (forget V G) where

instance forget₂_linear [ConcreteCategory V] : Functor.Linear R (forget₂ (Action V G) V) where

instance functorCategoryEquivalence_linear :
    Functor.Linear R (functorCategoryEquivalence V G).functor where

@[simp]
theorem smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom :=
  rfl

end Linear

section Abelian

/-- Auxilliary construction for the `Abelian (Action V G)` instance. -/
def abelianAux : Action V G ≌ ULift.{u} (SingleObj G) ⥤ V :=
  (functorCategoryEquivalence V G).trans (Equivalence.congrLeft ULift.equivalence)

noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.functor

end Abelian

section Monoidal

open MonoidalCategory

variable [MonoidalCategory V]

instance instMonoidalCategory : MonoidalCategory (Action V G) :=
  Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]
theorem tensorUnit_v : (𝟙_ (Action V G)).V = 𝟙_ V :=
  rfl

-- porting note: removed @[simp] as the simpNF linter complains
theorem tensorUnit_rho {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl

@[simp]
theorem tensor_v {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V :=
  rfl

-- porting note: removed @[simp] as the simpNF linter complains
theorem tensor_rho {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl

@[simp]
theorem tensorHom {W X Y Z : Action V G} (f : W ⟶ X) (g : Y ⟶ Z) : (f ⊗ g).hom = f.hom ⊗ g.hom :=
  rfl

-- porting note: removed @[simp] as the simpNF linter complains
theorem associator_hom_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).hom = (α_ X.V Y.V Z.V).hom := by
  dsimp
  simp

-- porting note: removed @[simp] as the simpNF linter complains
theorem associator_inv_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv := by
  dsimp
  simp

-- porting note: removed @[simp] as the simpNF linter complains
theorem leftUnitor_hom_hom {X : Action V G} : Hom.hom (λ_ X).hom = (λ_ X.V).hom := by
  dsimp
  simp

-- porting note: removed @[simp] as the simpNF linter complains
theorem leftUnitor_inv_hom {X : Action V G} : Hom.hom (λ_ X).inv = (λ_ X.V).inv := by
  dsimp
  simp

-- porting note: removed @[simp] as the simpNF linter complains
theorem rightUnitor_hom_hom {X : Action V G} : Hom.hom (ρ_ X).hom = (ρ_ X.V).hom := by
  dsimp
  simp

-- porting note: removed @[simp] as the simpNF linter complains
theorem rightUnitor_inv_hom {X : Action V G} : Hom.hom (ρ_ X).inv = (ρ_ X.V).inv := by
  dsimp
  simp

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f fun _ => by
    simp only [MonoidHom.one_apply, End.one_def, Category.id_comp f.hom, tensorUnit_rho,
      MonCat.oneHom_apply, MonCat.one_of, Category.comp_id]

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
  { toFunctor := Action.forget _ _
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }

instance forgetMonoidal_faithful : Faithful (forgetMonoidal V G).toFunctor := by
  change Faithful (forget V G); infer_instance

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _)
    (fun g => by simp [FunctorCategoryEquivalence.inverse])) (by aesop_cat)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps!]
def forgetBraided : BraidedFunctor (Action V G) V :=
  { forgetMonoidal _ _ with }

instance forgetBraided_faithful : Faithful (forgetBraided V G).toFunctor := by
  change Faithful (forget V G); infer_instance

end

instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  symmetricCategoryOfFaithful (forgetBraided V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] MonoidalPreadditive.tensor_add MonoidalPreadditive.add_tensor

instance : MonoidalPreadditive (Action V G) where

variable {R : Type*} [Semiring R] [Linear R V] [MonoidalLinear R V]

instance : MonoidalLinear R (Action V G) where

end

noncomputable section

/-- Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor. -/
def functorCategoryMonoidalEquivalence : MonoidalFunctor (Action V G) (SingleObj G ⥤ V) :=
  Monoidal.fromTransported (Action.functorCategoryEquivalence _ _).symm

instance : IsEquivalence (functorCategoryMonoidalEquivalence V G).toFunctor := by
  change IsEquivalence (Action.functorCategoryEquivalence _ _).functor; infer_instance

@[simp]
theorem functorCategoryMonoidalEquivalence.μ_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μ A B).app PUnit.unit = 𝟙 _ := by
  dsimp only [functorCategoryMonoidalEquivalence]
  simp only [Monoidal.fromTransported_toLaxMonoidalFunctor_μ, NatTrans.comp_app]
  -- porting note: Lean3 was able to see through some defeq, as the mathlib3 proof was
  --   show (𝟙 A.V ⊗ 𝟙 B.V) ≫ 𝟙 (A.V ⊗ B.V) ≫ (𝟙 A.V ⊗ 𝟙 B.V) = 𝟙 (A.V ⊗ B.V)
  --   simp only [monoidal_category.tensor_id, category.comp_id]
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.μIso_inv_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μIso A B).inv.app PUnit.unit = 𝟙 _ := by
  rw [← NatIso.app_inv, ← IsIso.Iso.inv_hom]
  refine' IsIso.inv_eq_of_hom_inv_id _
  rw [Category.comp_id, NatIso.app_hom, MonoidalFunctor.μIso_hom,
    functorCategoryMonoidalEquivalence.μ_app]

@[simp]
theorem functorCategoryMonoidalEquivalence.ε_app :
    (functorCategoryMonoidalEquivalence V G).ε.app PUnit.unit = 𝟙 _ := by
  dsimp only [functorCategoryMonoidalEquivalence]
  simp only [Monoidal.fromTransported_toLaxMonoidalFunctor_ε]
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.inv_counit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalEquivalence _ _).inv.adjunction.counit.app A).hom = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.counit_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalEquivalence _ _).adjunction.counit.app A).app PUnit.unit = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.inv_unit_app_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalEquivalence _ _).inv.adjunction.unit.app A).app PUnit.unit = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.unit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalEquivalence _ _).adjunction.unit.app A).hom = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.functor_map {A B : Action V G} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).map f = FunctorCategoryEquivalence.functor.map f :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.inverse_map {A B : SingleObj G ⥤ V} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).inv.map f = FunctorCategoryEquivalence.inverse.map f :=
  rfl

variable (H : GroupCat.{u})

instance [RightRigidCategory V] : RightRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RightRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change LeftRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [RigidCategory V] : RigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

variable {V H}
variable (X : Action V H)

@[simp]
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl

@[simp]
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
  rw [← SingleObj.inv_as_inv]; rfl

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
  rw [← SingleObj.inv_as_inv]; rfl

end

end Monoidal

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def actionPunitEquivalence : Action V (MonCat.of PUnit) ≌ V where
  functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [MonCat.oneHom_apply, MonCat.one_of, End.one_def, id_eq, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun X => Iso.refl _

variable (V)

/-- The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : MonCat} (f : G ⟶ H) : Action V H ⥤ Action V G where
  obj M :=
    { V := M.V
      ρ := f ≫ M.ρ }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }

/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
@[simps!]
def resId {G : MonCat} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
@[simps!]
def resComp {G H K : MonCat} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.
variable {H : MonCat.{u}} (f : G ⟶ H)

instance res_additive [Preadditive V] : (res V f).Additive where

variable {R : Type*} [Semiring R]

instance res_linear [Preadditive V] [Linear R V] : (res V f).Linear R where

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
def ofMulAction (G H : Type u) [Monoid G] [MulAction G H] : Action (Type u) (MonCat.of G) where
  V := H
  ρ := @MulAction.toEndHom _ _ _ (by assumption)

@[simp]
theorem ofMulAction_apply {G H : Type u} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl

/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι → Type max v u)
    [∀ i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => Action.ofMulAction G (F i)) where
  cone :=
    { pt := Action.ofMulAction G (∀ i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨fun x => x i.as, fun g => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact congr_fun ((s.π.app ⟨j⟩).comm g) x }
      fac := fun s j => rfl
      uniq := fun s f h => by
        ext x
        funext j
        dsimp at *
        rw [← h ⟨j⟩]
        rfl }

/-- The `G`-set `G`, acting on itself by left multiplication. -/
@[simps!]
def leftRegular (G : Type u) [Monoid G] : Action (Type u) (MonCat.of G) :=
  Action.ofMulAction G G

/-- The `G`-set `Gⁿ`, acting on itself by left multiplication. -/
@[simps!]
def diagonal (G : Type u) [Monoid G] (n : ℕ) : Action (Type u) (MonCat.of G) :=
  Action.ofMulAction G (Fin n → G)

/-- We have `fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication. -/
def diagonalOneIsoLeftRegular (G : Type u) [Monoid G] : diagonal G 1 ≅ leftRegular G :=
  Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

open MonoidalCategory

/-- Given `X : Action (Type u) (Mon.of G)` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps]
noncomputable def leftRegularTensorIso (G : Type u) [Group G] (X : Action (Type u) (MonCat.of G)) :
    leftRegular G ⊗ X ≅ leftRegular G ⊗ Action.mk X.V 1 where
  hom :=
    { hom := fun g => ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine' Prod.ext rfl _
        change (X.ρ ((g * x₁)⁻¹ : G) * X.ρ g) x₂ = X.ρ _ _
        rw [mul_inv_rev, ← X.ρ.map_mul, inv_mul_cancel_right] }
  inv :=
    { hom := fun g => ⟨g.1, X.ρ g.1 g.2⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine' Prod.ext rfl _
        erw [tensor_rho, tensor_rho]
        dsimp
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [leftRegular_ρ_apply]
        erw [map_mul]
        rfl }
  hom_inv_id := by
    apply Hom.ext
    funext x
    refine' Prod.ext rfl _
    change (X.ρ x.1 * X.ρ (x.1⁻¹ : G)) x.2 = x.2
    rw [← X.ρ.map_mul, mul_inv_self, X.ρ.map_one, MonCat.one_of, End.one_def, types_id_apply]
  inv_hom_id := by
    apply Hom.ext
    funext x
    refine' Prod.ext rfl _
    change (X.ρ (x.1⁻¹ : G) * X.ρ x.1) x.2 = x.2
    rw [← X.ρ.map_mul, inv_mul_self, X.ρ.map_one, MonCat.one_of, End.one_def, types_id_apply]

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps!]
noncomputable def diagonalSucc (G : Type u) [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Equiv.piFinSuccAboveEquiv _ 0).toIso fun _ => rfl

end Action

namespace CategoryTheory.Functor

variable {V} {W : Type (u + 1)} [LargeCategory W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction (F : V ⥤ W) (G : MonCat.{u}) : Action V G ⥤ Action W G where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp only [End.one_def, Action.ρ_one, F.map_id, MonCat.one_of]
          map_mul' := fun g h => by
            dsimp
            rw [map_mul, MonCat.mul_of, End.mul_def, End.mul_def, F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]

variable (F : V ⥤ W) (G : MonCat.{u}) [Preadditive V] [Preadditive W]

instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]

instance mapAction_linear [F.Additive] [F.Linear R] : (F.mapAction G).Linear R where

end CategoryTheory.Functor

namespace CategoryTheory.MonoidalFunctor

open Action

variable {V}
variable {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]
  (F : MonoidalFunctor V W) (G : MonCat.{u})

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction : MonoidalFunctor (Action V G) (Action W G) where
  toFunctor := F.toFunctor.mapAction G
  ε :=
    { hom := F.ε
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp, F.map_id, Category.comp_id] }
  μ := fun X Y =>
    { hom := F.μ X.V Y.V
      comm := fun g => F.toLaxMonoidalFunctor.μ_natural (X.ρ g) (Y.ρ g) }
  -- using `dsimp` before `simp` speeds these up
  μ_natural {X Y X' Y'} f g := by ext; dsimp; simp
  associativity X Y Z := by ext; dsimp; simp
  left_unitality X := by ext; dsimp; simp
  right_unitality X := by
    ext
    dsimp
    simp only [MonoidalCategory.rightUnitor_conjugation,
      LaxMonoidalFunctor.right_unitality, Category.id_comp, Category.assoc,
      LaxMonoidalFunctor.right_unitality_inv_assoc, Category.comp_id, Iso.hom_inv_id]
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]

@[simp]
theorem mapAction_ε_inv_hom : (inv (F.mapAction G).ε).hom = inv F.ε := by
  rw [← cancel_mono F.ε, IsIso.inv_hom_id, ← F.mapAction_toLaxMonoidalFunctor_ε_hom G,
    ← Action.comp_hom, IsIso.inv_hom_id, Action.id_hom]

@[simp]
theorem mapAction_μ_inv_hom (X Y : Action V G) :
    (inv ((F.mapAction G).μ X Y)).hom = inv (F.μ X.V Y.V) := by
  rw [← cancel_mono (F.μ X.V Y.V), IsIso.inv_hom_id, ← F.mapAction_toLaxMonoidalFunctor_μ_hom G,
    ← Action.comp_hom, IsIso.inv_hom_id, Action.id_hom]

end CategoryTheory.MonoidalFunctor
