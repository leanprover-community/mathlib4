/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module representation_theory.Action
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.SingleObj
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Monoidal.FunctorCategory
import Mathbin.CategoryTheory.Monoidal.Transport
import Mathbin.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathbin.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathbin.CategoryTheory.Monoidal.Linear
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Monoidal.Types.Symmetric
import Mathbin.CategoryTheory.Abelian.FunctorCategory
import Mathbin.CategoryTheory.Abelian.Transfer
import Mathbin.CategoryTheory.Conj
import Mathbin.CategoryTheory.Linear.FunctorCategory

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = Module R`,
where `Action (Module R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (single_obj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.

* When `V` has (co)limits so does `Action V G`.
* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

variable (V : Type (u + 1)) [LargeCategory V]

-- Note: this is _not_ a categorical action of `G` on `V`.
/-- An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = Module R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
structure Action (G : MonCat.{u}) where
  V : V
  ρ : G ⟶ MonCat.of (End V)
#align Action Action

namespace Action

variable {V}

@[simp]
theorem ρ_one {G : MonCat.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V := by rw [MonoidHom.map_one]; rfl
#align Action.ρ_one Action.ρ_one

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρAut {G : GroupCat.{u}} (A : Action V (MonCat.of G)) : G ⟶ GroupCat.of (Aut A.V)
    where
  toFun g :=
    { Hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id' := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one])
      inv_hom_id' := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]) }
  map_one' := by ext; exact A.ρ.map_one
  map_mul' x y := by ext; exact A.ρ.map_mul x y
#align Action.ρ_Aut Action.ρAut

variable (G : MonCat.{u})

section

instance inhabited' : Inhabited (Action (Type u) G) :=
  ⟨⟨PUnit, 1⟩⟩
#align Action.inhabited' Action.inhabited'

/-- The trivial representation of a group. -/
def trivial : Action AddCommGroupCat G
    where
  V := AddCommGroupCat.of PUnit
  ρ := 1
#align Action.trivial Action.trivial

instance : Inhabited (Action AddCommGroupCat G) :=
  ⟨trivial G⟩

end

variable {G V}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure Hom (M N : Action V G) where
  Hom : M.V ⟶ N.V
  comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by obviously
#align Action.hom Action.Hom

restate_axiom hom.comm'

namespace Hom

/-- The identity morphism on a `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.Hom M M where Hom := 𝟙 M.V
#align Action.hom.id Action.Hom.id

instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K
    where
  Hom := p.Hom ≫ q.Hom
  comm' g := by rw [← category.assoc, p.comm, category.assoc, q.comm, ← category.assoc]
#align Action.hom.comp Action.Hom.comp

end Hom

instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp M N K f g := Hom.comp f g

@[simp]
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).Hom = 𝟙 M.V :=
  rfl
#align Action.id_hom Action.id_hom

@[simp]
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl
#align Action.comp_hom Action.comp_hom

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mkIso {M N : Action V G} (f : M.V ≅ N.V) (comm : ∀ g : G, M.ρ g ≫ f.Hom = f.Hom ≫ N.ρ g) : M ≅ N
    where
  Hom :=
    { Hom := f.Hom
      comm' := comm }
  inv :=
    { Hom := f.inv
      comm' := fun g => by have w := comm g =≫ f.inv; simp at w ; simp [w] }
#align Action.mk_iso Action.mkIso

instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.Hom] :
    IsIso f := by convert is_iso.of_iso (mk_iso (as_iso f.hom) f.comm); ext; rfl
#align Action.is_iso_of_hom_is_iso Action.isIso_of_hom_isIso

instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) : @IsIso _ _ M N ⟨f, w⟩ :=
  IsIso.of_iso (mkIso (asIso f) w)
#align Action.is_iso_hom_mk Action.isIso_hom_mk

namespace FunctorCategoryEquivalence

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def functor : Action V G ⥤ SingleObj G ⥤ V
    where
  obj M :=
    { obj := fun _ => M.V
      map := fun _ _ g => M.ρ g
      map_id' := fun _ => M.ρ.map_one
      map_comp' := fun _ _ _ g h => M.ρ.map_mul h g }
  map M N f :=
    { app := fun _ => f.Hom
      naturality' := fun _ _ g => f.comm g }
#align Action.functor_category_equivalence.functor Action.FunctorCategoryEquivalence.functor

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def inverse : (SingleObj G ⥤ V) ⥤ Action V G
    where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map M N f :=
    { Hom := f.app PUnit.unit
      comm' := fun g => f.naturality g }
#align Action.functor_category_equivalence.inverse Action.FunctorCategoryEquivalence.inverse

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun M => mkIso (Iso.refl _) (by tidy)) (by tidy)
#align Action.functor_category_equivalence.unit_iso Action.FunctorCategoryEquivalence.unitIso

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (by tidy) (by tidy)) (by tidy)
#align Action.functor_category_equivalence.counit_iso Action.FunctorCategoryEquivalence.counitIso

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `single_obj G ⥤ V`.
-/
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V
    where
  Functor := Functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
#align Action.functor_category_equivalence Action.functorCategoryEquivalence

attribute [simps] functor_category_equivalence

theorem functorCategoryEquivalence.functor_def :
    (functorCategoryEquivalence V G).Functor = FunctorCategoryEquivalence.functor :=
  rfl
#align Action.functor_category_equivalence.functor_def Action.functorCategoryEquivalence.functor_def

theorem functorCategoryEquivalence.inverse_def :
    (functorCategoryEquivalence V G).inverse = FunctorCategoryEquivalence.inverse :=
  rfl
#align Action.functor_category_equivalence.inverse_def Action.functorCategoryEquivalence.inverse_def

instance [HasFiniteProducts V] : HasFiniteProducts (Action V G)
    where out n :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

instance [HasFiniteLimits V] : HasFiniteLimits (Action V G)
    where out J _ _ :=
    adjunction.has_limits_of_shape_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).Functor

end

section Forget

variable (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
@[simps]
def forget : Action V G ⥤ V where
  obj M := M.V
  map M N f := f.Hom
#align Action.forget Action.forget

instance : Faithful (forget V G) where map_injective' X Y f g w := Hom.ext _ _ w

instance [ConcreteCategory V] : ConcreteCategory (Action V G)
    where forget := forget V G ⋙ ConcreteCategory.forget V

instance hasForgetToV [ConcreteCategory V] : HasForget₂ (Action V G) V where forget₂ := forget V G
#align Action.has_forget_to_V Action.hasForgetToV

/-- The forgetful functor is intertwined by `functor_category_equivalence` with
evaluation at `punit.star`. -/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).Functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _
#align Action.functor_category_equivalence_comp_evaluation Action.functorCategoryEquivalenceCompEvaluation

noncomputable instance [HasLimits V] : Limits.PreservesLimits (forget V G) :=
  Limits.preservesLimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

noncomputable instance [HasColimits V] : PreservesColimits (forget V G) :=
  preservesColimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) := by rw [iso.conj_apply, iso.eq_inv_comp];
  simp [f.hom.comm']
#align Action.iso.conj_ρ Action.Iso.conj_ρ

section HasZeroMorphisms

variable [HasZeroMorphisms V]

instance : HasZeroMorphisms (Action V G)
    where
  Zero X Y := ⟨⟨0, by intro g; simp⟩⟩
  comp_zero P Q f R := by ext1; simp
  zero_comp P Q R f := by ext1; simp

instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where
#align Action.forget_preserves_zero_morphisms Action.forget_preservesZeroMorphisms

instance forget₂_preservesZeroMorphisms [ConcreteCategory V] :
    Functor.PreservesZeroMorphisms (forget₂ (Action V G) V) where
#align Action.forget₂_preserves_zero_morphisms Action.forget₂_preservesZeroMorphisms

instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).Functor where
#align Action.functor_category_equivalence_preserves_zero_morphisms Action.functorCategoryEquivalence_preservesZeroMorphisms

end HasZeroMorphisms

section Preadditive

variable [Preadditive V]

instance : Preadditive (Action V G)
    where
  homGroup X Y :=
    { zero := ⟨0, by simp⟩
      add := fun f g => ⟨f.Hom + g.Hom, by simp [f.comm, g.comm]⟩
      neg := fun f => ⟨-f.Hom, by simp [f.comm]⟩
      zero_add := by intros; ext; exact zero_add _
      add_zero := by intros; ext; exact add_zero _
      add_assoc := by intros; ext; exact add_assoc _ _ _
      add_left_neg := by intros; ext; exact add_left_neg _
      add_comm := by intros; ext; exact add_comm _ _ }
  add_comp := by intros; ext; exact preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact preadditive.comp_add _ _ _ _ _ _

instance forget_additive : Functor.Additive (forget V G) where
#align Action.forget_additive Action.forget_additive

instance forget₂_additive [ConcreteCategory V] : Functor.Additive (forget₂ (Action V G) V) where
#align Action.forget₂_additive Action.forget₂_additive

instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).Functor where
#align Action.functor_category_equivalence_additive Action.functorCategoryEquivalence_additive

@[simp]
theorem zero_hom {X Y : Action V G} : (0 : X ⟶ Y).Hom = 0 :=
  rfl
#align Action.zero_hom Action.zero_hom

@[simp]
theorem neg_hom {X Y : Action V G} (f : X ⟶ Y) : (-f).Hom = -f.Hom :=
  rfl
#align Action.neg_hom Action.neg_hom

@[simp]
theorem add_hom {X Y : Action V G} (f g : X ⟶ Y) : (f + g).Hom = f.Hom + g.Hom :=
  rfl
#align Action.add_hom Action.add_hom

@[simp]
theorem sum_hom {X Y : Action V G} {ι : Type _} (f : ι → (X ⟶ Y)) (s : Finset ι) :
    (s.Sum f).Hom = s.Sum fun i => (f i).Hom :=
  (forget V G).map_sum f s
#align Action.sum_hom Action.sum_hom

end Preadditive

section Linear

variable [Preadditive V] {R : Type _} [Semiring R] [Linear R V]

instance : Linear R (Action V G)
    where
  homModule X Y :=
    { smul := fun r f => ⟨r • f.Hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext; exact smul_add _ _ _
      mul_smul := by intros; ext; exact mul_smul _ _ _ }
  smul_comp' := by intros; ext; exact linear.smul_comp _ _ _ _ _ _
  comp_smul' := by intros; ext; exact linear.comp_smul _ _ _ _ _ _

instance forget_linear : Functor.Linear R (forget V G) where
#align Action.forget_linear Action.forget_linear

instance forget₂_linear [ConcreteCategory V] : Functor.Linear R (forget₂ (Action V G) V) where
#align Action.forget₂_linear Action.forget₂_linear

instance functorCategoryEquivalence_linear :
    Functor.Linear R (functorCategoryEquivalence V G).Functor where
#align Action.functor_category_equivalence_linear Action.functorCategoryEquivalence_linear

@[simp]
theorem smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).Hom = r • f.Hom :=
  rfl
#align Action.smul_hom Action.smul_hom

end Linear

section Abelian

/-- Auxilliary construction for the `abelian (Action V G)` instance. -/
def abelianAux : Action V G ≌ ULift.{u} (SingleObj G) ⥤ V :=
  (functorCategoryEquivalence V G).trans (Equivalence.congrLeft ULift.equivalence)
#align Action.abelian_aux Action.abelianAux

noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.Functor

end Abelian

section Monoidal

variable [MonoidalCategory V]

instance : MonoidalCategory (Action V G) :=
  Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]
theorem tensorUnit_v : (𝟙_ (Action V G)).V = 𝟙_ V :=
  rfl
#align Action.tensor_unit_V Action.tensorUnit_v

@[simp]
theorem tensorUnit_rho {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl
#align Action.tensor_unit_rho Action.tensorUnit_rho

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_v {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V :=
  rfl
#align Action.tensor_V Action.tensor_v

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_rho {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl
#align Action.tensor_rho Action.tensor_rho

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensorHom {W X Y Z : Action V G} (f : W ⟶ X) (g : Y ⟶ Z) : (f ⊗ g).Hom = f.Hom ⊗ g.Hom :=
  rfl
#align Action.tensor_hom Action.tensorHom

@[simp]
theorem associator_hom_hom {X Y Z : Action V G} : Hom.hom (α_ X Y Z).Hom = (α_ X.V Y.V Z.V).Hom :=
  by
  dsimp [monoidal.transport_associator]
  simp
#align Action.associator_hom_hom Action.associator_hom_hom

@[simp]
theorem associator_inv_hom {X Y Z : Action V G} : Hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv :=
  by
  dsimp [monoidal.transport_associator]
  simp
#align Action.associator_inv_hom Action.associator_inv_hom

@[simp]
theorem leftUnitor_hom_hom {X : Action V G} : Hom.hom (λ_ X).Hom = (λ_ X.V).Hom :=
  by
  dsimp [monoidal.transport_left_unitor]
  simp
#align Action.left_unitor_hom_hom Action.leftUnitor_hom_hom

@[simp]
theorem leftUnitor_inv_hom {X : Action V G} : Hom.hom (λ_ X).inv = (λ_ X.V).inv :=
  by
  dsimp [monoidal.transport_left_unitor]
  simp
#align Action.left_unitor_inv_hom Action.leftUnitor_inv_hom

@[simp]
theorem rightUnitor_hom_hom {X : Action V G} : Hom.hom (ρ_ X).Hom = (ρ_ X.V).Hom :=
  by
  dsimp [monoidal.transport_right_unitor]
  simp
#align Action.right_unitor_hom_hom Action.rightUnitor_hom_hom

@[simp]
theorem rightUnitor_inv_hom {X : Action V G} : Hom.hom (ρ_ X).inv = (ρ_ X.V).inv :=
  by
  dsimp [monoidal.transport_right_unitor]
  simp
#align Action.right_unitor_inv_hom Action.rightUnitor_inv_hom

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f fun g => by
    simp only [MonoidHom.one_apply, End.one_def, category.id_comp f.hom, tensor_unit_rho,
      category.comp_id]
#align Action.tensor_unit_iso Action.tensorUnitIso

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
  { Action.forget _ _ with
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }
#align Action.forget_monoidal Action.forgetMonoidal

instance forgetMonoidal_faithful : Faithful (forgetMonoidal V G).toFunctor := by
  change faithful (forget V G); infer_instance
#align Action.forget_monoidal_faithful Action.forgetMonoidal_faithful

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _) (by tidy)) (by tidy)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps]
def forgetBraided : BraidedFunctor (Action V G) V :=
  { forgetMonoidal _ _ with }
#align Action.forget_braided Action.forgetBraided

instance forgetBraided_faithful : Faithful (forgetBraided V G).toFunctor := by
  change faithful (forget V G); infer_instance
#align Action.forget_braided_faithful Action.forgetBraided_faithful

end

instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  symmetricCategoryOfFaithful (forgetBraided V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance : MonoidalPreadditive (Action V G) where

variable {R : Type _} [Semiring R] [Linear R V] [MonoidalLinear R V]

instance : MonoidalLinear R (Action V G) where

end

variable (V G)

noncomputable section

/-- Upgrading the functor `Action V G ⥤ (single_obj G ⥤ V)` to a monoidal functor. -/
def functorCategoryMonoidalEquivalence : MonoidalFunctor (Action V G) (SingleObj G ⥤ V) :=
  Monoidal.fromTransported (Action.functorCategoryEquivalence _ _).symm
#align Action.functor_category_monoidal_equivalence Action.functorCategoryMonoidalEquivalence

instance : IsEquivalence (functorCategoryMonoidalEquivalence V G).toFunctor := by
  change is_equivalence (Action.functorCategoryEquivalence _ _).Functor; infer_instance

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem functorCategoryMonoidalEquivalence.μ_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μ A B).app PUnit.unit = 𝟙 _ :=
  by
  dsimp only [functor_category_monoidal_equivalence]
  simp only [monoidal.from_transported_to_lax_monoidal_functor_μ]
  show (𝟙 A.V ⊗ 𝟙 B.V) ≫ 𝟙 (A.V ⊗ B.V) ≫ (𝟙 A.V ⊗ 𝟙 B.V) = 𝟙 (A.V ⊗ B.V)
  simp only [monoidal_category.tensor_id, category.comp_id]
#align Action.functor_category_monoidal_equivalence.μ_app Action.functorCategoryMonoidalEquivalence.μ_app

@[simp]
theorem functorCategoryMonoidalEquivalence.μIso_inv_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μIso A B).inv.app PUnit.unit = 𝟙 _ :=
  by
  rw [← nat_iso.app_inv, ← is_iso.iso.inv_hom]
  refine' is_iso.inv_eq_of_hom_inv_id _
  rw [category.comp_id, nat_iso.app_hom, monoidal_functor.μ_iso_hom,
    functor_category_monoidal_equivalence.μ_app]
#align Action.functor_category_monoidal_equivalence.μ_iso_inv_app Action.functorCategoryMonoidalEquivalence.μIso_inv_app

@[simp]
theorem functorCategoryMonoidalEquivalence.ε_app :
    (functorCategoryMonoidalEquivalence V G).ε.app PUnit.unit = 𝟙 _ :=
  by
  dsimp only [functor_category_monoidal_equivalence]
  simp only [monoidal.from_transported_to_lax_monoidal_functor_ε]
  show 𝟙 (monoidal_category.tensor_unit V) ≫ _ = 𝟙 (monoidal_category.tensor_unit V)
  rw [nat_iso.is_iso_inv_app, category.id_comp]
  exact is_iso.inv_id
#align Action.functor_category_monoidal_equivalence.ε_app Action.functorCategoryMonoidalEquivalence.ε_app

@[simp]
theorem functorCategoryMonoidalEquivalence.inv_counit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalEquivalence _ _).inv.Adjunction.counit.app A).Hom = 𝟙 _ :=
  rfl
#align Action.functor_category_monoidal_equivalence.inv_counit_app_hom Action.functorCategoryMonoidalEquivalence.inv_counit_app_hom

@[simp]
theorem functorCategoryMonoidalEquivalence.counit_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalEquivalence _ _).Adjunction.counit.app A).app PUnit.unit = 𝟙 _ :=
  rfl
#align Action.functor_category_monoidal_equivalence.counit_app Action.functorCategoryMonoidalEquivalence.counit_app

@[simp]
theorem functorCategoryMonoidalEquivalence.inv_unit_app_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalEquivalence _ _).inv.Adjunction.Unit.app A).app PUnit.unit = 𝟙 _ :=
  rfl
#align Action.functor_category_monoidal_equivalence.inv_unit_app_app Action.functorCategoryMonoidalEquivalence.inv_unit_app_app

@[simp]
theorem functorCategoryMonoidalEquivalence.unit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalEquivalence _ _).Adjunction.Unit.app A).Hom = 𝟙 _ :=
  rfl
#align Action.functor_category_monoidal_equivalence.unit_app_hom Action.functorCategoryMonoidalEquivalence.unit_app_hom

@[simp]
theorem functorCategoryMonoidalEquivalence.functor_map {A B : Action V G} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).map f = FunctorCategoryEquivalence.functor.map f :=
  rfl
#align Action.functor_category_monoidal_equivalence.functor_map Action.functorCategoryMonoidalEquivalence.functor_map

@[simp]
theorem functorCategoryMonoidalEquivalence.inverse_map {A B : SingleObj G ⥤ V} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).inv.map f = FunctorCategoryEquivalence.inverse.map f :=
  rfl
#align Action.functor_category_monoidal_equivalence.inverse_map Action.functorCategoryMonoidalEquivalence.inverse_map

variable (H : GroupCat.{u})

instance [RightRigidCategory V] : RightRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change right_rigid_category (single_obj H ⥤ V); infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change left_rigid_category (single_obj H ⥤ V); infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [RigidCategory V] : RigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change rigid_category (single_obj H ⥤ V); infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

variable {V H} (X : Action V H)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl
#align Action.right_dual_V Action.rightDual_v

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl
#align Action.left_dual_V Action.leftDual_v

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = X.ρ (h⁻¹ : H)ᘁ := by
  rw [← single_obj.inv_as_inv]; rfl
#align Action.right_dual_ρ Action.rightDual_ρ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
  rw [← single_obj.inv_as_inv]; rfl
#align Action.left_dual_ρ Action.leftDual_ρ

end Monoidal

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def actionPunitEquivalence : Action V (MonCat.of PUnit) ≌ V
    where
  Functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun X Y f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents (fun X => mkIso (Iso.refl _) fun ⟨⟩ => by simpa using ρ_one X) (by tidy)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align Action.Action_punit_equivalence Action.actionPunitEquivalence

variable (V)

/-- The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : MonCat} (f : G ⟶ H) : Action V H ⥤ Action V G
    where
  obj M :=
    { V := M.V
      ρ := f ≫ M.ρ }
  map M N p :=
    { Hom := p.Hom
      comm' := fun g => p.comm (f g) }
#align Action.res Action.res

/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
def resId {G : MonCat} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents (fun M => mkIso (Iso.refl _) (by tidy)) (by tidy)
#align Action.res_id Action.resId

attribute [simps] res_id

/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
def resComp {G H K : MonCat} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
  NatIso.ofComponents (fun M => mkIso (Iso.refl _) (by tidy)) (by tidy)
#align Action.res_comp Action.resComp

attribute [simps] res_comp

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.
variable {G} {H : MonCat.{u}} (f : G ⟶ H)

instance res_additive [Preadditive V] : (res V f).Additive where
#align Action.res_additive Action.res_additive

variable {R : Type _} [Semiring R]

instance res_linear [Preadditive V] [Linear R V] : (res V f).Linear R where
#align Action.res_linear Action.res_linear

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
def ofMulAction (G H : Type u) [Monoid G] [MulAction G H] : Action (Type u) (MonCat.of G)
    where
  V := H
  ρ := @MulAction.toEndHom _ _ _ (by assumption)
#align Action.of_mul_action Action.ofMulAction

@[simp]
theorem ofMulAction_apply {G H : Type u} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl
#align Action.of_mul_action_apply Action.ofMulAction_apply

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι → Type max v u)
    [∀ i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => Action.ofMulAction G (F i))
    where
  Cone :=
    { pt := Action.ofMulAction G (∀ i : ι, F i)
      π :=
        { app := fun i => ⟨fun x => x i.as, fun g => by ext <;> rfl⟩
          naturality' := fun i j x => by
            ext
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
            cases x
            congr } }
  IsLimit :=
    { lift := fun s =>
        { Hom := fun x i => (s.π.app ⟨i⟩).Hom x
          comm' := fun g => by
            ext (x j)
            dsimp
            exact congr_fun ((s.π.app ⟨j⟩).comm g) x }
      fac := fun s j => by
        ext
        dsimp
        congr
        rw [discrete.mk_as]
      uniq := fun s f h => by
        ext (x j)
        dsimp at *
        rw [← h ⟨j⟩]
        congr }
#align Action.of_mul_action_limit_cone Action.ofMulActionLimitCone

/-- The `G`-set `G`, acting on itself by left multiplication. -/
@[simps]
def leftRegular (G : Type u) [Monoid G] : Action (Type u) (MonCat.of G) :=
  Action.ofMulAction G G
#align Action.left_regular Action.leftRegular

/-- The `G`-set `Gⁿ`, acting on itself by left multiplication. -/
@[simps]
def diagonal (G : Type u) [Monoid G] (n : ℕ) : Action (Type u) (MonCat.of G) :=
  Action.ofMulAction G (Fin n → G)
#align Action.diagonal Action.diagonal

/-- We have `fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication. -/
def diagonalOneIsoLeftRegular (G : Type u) [Monoid G] : diagonal G 1 ≅ leftRegular G :=
  Action.mkIso (Equiv.funUnique _ _).toIso fun g => rfl
#align Action.diagonal_one_iso_left_regular Action.diagonalOneIsoLeftRegular

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given `X : Action (Type u) (Mon.of G)` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps]
def leftRegularTensorIso (G : Type u) [Group G] (X : Action (Type u) (MonCat.of G)) :
    leftRegular G ⊗ X ≅ leftRegular G ⊗ Action.mk X.V 1
    where
  Hom :=
    { Hom := fun g => ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
      comm' := fun g =>
        funext fun x =>
          Prod.ext rfl <|
            show (X.ρ ((g * x.1)⁻¹ : G) * X.ρ g) x.2 = _ by
              simpa only [mul_inv_rev, ← X.ρ.map_mul, inv_mul_cancel_right] }
  inv :=
    { Hom := fun g => ⟨g.1, X.ρ g.1 g.2⟩
      comm' := fun g =>
        funext fun x =>
          Prod.ext rfl <| by
            simpa only [tensor_rho, types_comp_apply, tensor_apply, left_regular_ρ_apply, map_mul] }
  hom_inv_id' :=
    Hom.ext _ _
      (funext fun x =>
        Prod.ext rfl <|
          show (X.ρ x.1 * X.ρ (x.1⁻¹ : G)) x.2 = _ by
            simpa only [← X.ρ.map_mul, mul_inv_self, X.ρ.map_one])
  inv_hom_id' :=
    Hom.ext _ _
      (funext fun x =>
        Prod.ext rfl <|
          show (X.ρ (x.1⁻¹ : G) * X.ρ x.1) _ = _ by
            simpa only [← X.ρ.map_mul, inv_mul_self, X.ρ.map_one])
#align Action.left_regular_tensor_iso Action.leftRegularTensorIso

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps]
def diagonalSucc (G : Type u) [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Equiv.piFinSuccAboveEquiv _ 0).toIso fun g => rfl
#align Action.diagonal_succ Action.diagonalSucc

end Action

namespace CategoryTheory.Functor

variable {V} {W : Type (u + 1)} [LargeCategory W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction (F : V ⥤ W) (G : MonCat.{u}) : Action V G ⥤ Action W G
    where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp only [End.one_def, Action.ρ_one, F.map_id]
          map_mul' := fun g h => by simp only [End.mul_def, F.map_comp, map_mul] } }
  map M N f :=
    { Hom := F.map f.Hom
      comm' := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id' M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp' M N P f g := by ext; simp only [Action.comp_hom, F.map_comp]
#align category_theory.functor.map_Action CategoryTheory.Functor.mapAction

variable (F : V ⥤ W) (G : MonCat.{u}) [Preadditive V] [Preadditive W]

instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where
#align category_theory.functor.map_Action_preadditive CategoryTheory.Functor.mapAction_preadditive

variable {R : Type _} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]

instance mapAction_linear [F.Additive] [F.Linear R] : (F.mapAction G).Linear R where
#align category_theory.functor.map_Action_linear CategoryTheory.Functor.mapAction_linear

end CategoryTheory.Functor

namespace CategoryTheory.MonoidalFunctor

open Action

variable {V} {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]
  (F : MonoidalFunctor V W) (G : MonCat.{u})

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps]
def mapAction : MonoidalFunctor (Action V G) (Action W G) :=
  {-- See note [dsimp, simp].
          F.toFunctor.mapAction
      G with
    ε :=
      { Hom := F.ε
        comm' := fun g => by dsimp;
          erw [category.id_comp, CategoryTheory.Functor.map_id, category.comp_id] }
    μ := fun X Y =>
      { Hom := F.μ X.V Y.V
        comm' := fun g => F.toLaxMonoidalFunctor.μ_natural (X.ρ g) (Y.ρ g) }
    ε_isIso := by infer_instance
    μ_isIso := by infer_instance
    μ_natural' := by intros; ext; dsimp; simp
    associativity' := by intros; ext; dsimp; simp; dsimp; simp
    left_unitality' := by intros; ext; dsimp; simp; dsimp; simp
    right_unitality' := by intros; ext; dsimp; simp; dsimp; simp }
#align category_theory.monoidal_functor.map_Action CategoryTheory.MonoidalFunctor.mapAction

@[simp]
theorem mapAction_ε_inv_hom : (inv (F.mapAction G).ε).Hom = inv F.ε :=
  by
  ext
  simp only [← F.map_Action_to_lax_monoidal_functor_ε_hom G, ← Action.comp_hom, is_iso.hom_inv_id,
    id_hom]
#align category_theory.monoidal_functor.map_Action_ε_inv_hom CategoryTheory.MonoidalFunctor.mapAction_ε_inv_hom

@[simp]
theorem mapAction_μ_inv_hom (X Y : Action V G) :
    (inv ((F.mapAction G).μ X Y)).Hom = inv (F.μ X.V Y.V) :=
  by
  ext
  simpa only [← F.map_Action_to_lax_monoidal_functor_μ_hom G, ← Action.comp_hom, is_iso.hom_inv_id,
    id_hom]
#align category_theory.monoidal_functor.map_Action_μ_inv_hom CategoryTheory.MonoidalFunctor.mapAction_μ_inv_hom

end CategoryTheory.MonoidalFunctor

