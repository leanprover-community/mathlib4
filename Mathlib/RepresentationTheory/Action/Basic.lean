/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Conj

#align_import representation_theory.Action from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = ModuleCat R`,
where `Action (ModuleCat R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (singleObj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.
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
set_option linter.uppercaseLean3 false in
#align Action Action

namespace Action

variable {V}

@[simp 1100]
theorem ρ_one {G : MonCat.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V := by rw [MonoidHom.map_one]; rfl
set_option linter.uppercaseLean3 false in
#align Action.ρ_one Action.ρ_one

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρAut {G : Grp.{u}} (A : Action V (MonCat.of G)) : G ⟶ Grp.of (Aut A.V) where
  toFun g :=
    { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)
set_option linter.uppercaseLean3 false in
#align Action.ρ_Aut Action.ρAut

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] Action.ρAut_apply_inv Action.ρAut_apply_hom

variable (G : MonCat.{u})

section

instance inhabited' : Inhabited (Action (Type u) G) :=
  ⟨⟨PUnit, 1⟩⟩
set_option linter.uppercaseLean3 false in
#align Action.inhabited' Action.inhabited'

/-- The trivial representation of a group. -/
def trivial : Action AddCommGrp G where
  V := AddCommGrp.of PUnit
  ρ := 1
set_option linter.uppercaseLean3 false in
#align Action.trivial Action.trivial

instance : Inhabited (Action AddCommGrp G) :=
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
set_option linter.uppercaseLean3 false in
#align Action.hom Action.Hom

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

/-- The identity morphism on an `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.Hom M M where hom := 𝟙 M.V
set_option linter.uppercaseLean3 false in
#align Action.hom.id Action.Hom.id

instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  hom := p.hom ≫ q.hom
set_option linter.uppercaseLean3 false in
#align Action.hom.comp Action.Hom.comp

end Hom

instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g

-- Porting note: added because `Hom.ext` is not triggered automatically
@[ext]
lemma hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Hom.ext _ _ h

@[simp]
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.id_hom Action.id_hom

@[simp]
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.comp_hom Action.comp_hom

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
set_option linter.uppercaseLean3 false in
#align Action.mk_iso Action.mkIso

instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := (mkIso (asIso f.hom) f.comm).isIso_hom
set_option linter.uppercaseLean3 false in
#align Action.is_iso_of_hom_is_iso Action.isIso_of_hom_isIso

instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) :
    @IsIso _ _ M N (Hom.mk f w) :=
  (mkIso (asIso f) w).isIso_hom
set_option linter.uppercaseLean3 false in
#align Action.is_iso_hom_mk Action.isIso_hom_mk

namespace FunctorCategoryEquivalence

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
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
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence.functor Action.FunctorCategoryEquivalence.functor

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
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
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence.inverse Action.FunctorCategoryEquivalence.inverse

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence.unit_iso Action.FunctorCategoryEquivalence.unitIso

/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents fun M => NatIso.ofComponents fun X => Iso.refl _
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence.counit_iso Action.FunctorCategoryEquivalence.counitIso

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
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence Action.functorCategoryEquivalence
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence.functor_def Action.functorCategoryEquivalence_functor
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence.inverse_def Action.functorCategoryEquivalence_inverse

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
set_option linter.uppercaseLean3 false in
#align Action.forget Action.forget

instance : (forget V G).Faithful where map_injective w := Hom.ext _ _ w

instance [ConcreteCategory V] : ConcreteCategory (Action V G) where
  forget := forget V G ⋙ ConcreteCategory.forget

instance hasForgetToV [ConcreteCategory V] : HasForget₂ (Action V G) V where forget₂ := forget V G
set_option linter.uppercaseLean3 false in
#align Action.has_forget_to_V Action.hasForgetToV

/-- The forgetful functor is intertwined by `functorCategoryEquivalence` with
evaluation at `PUnit.star`. -/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence_comp_evaluation Action.functorCategoryEquivalenceCompEvaluation

noncomputable instance instPreservesLimitsForget [HasLimits V] :
    Limits.PreservesLimits (forget V G) :=
  Limits.preservesLimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

noncomputable instance instPreservesColimitsForget [HasColimits V] :
    PreservesColimits (forget V G) :=
  preservesColimitsOfNatIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) := by
      rw [Iso.conj_apply, Iso.eq_inv_comp]; simp [f.hom.comm]
set_option linter.uppercaseLean3 false in
#align Action.iso.conj_ρ Action.Iso.conj_ρ

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
set_option linter.uppercaseLean3 false in
#align Action.Action_punit_equivalence Action.actionPunitEquivalence

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
set_option linter.uppercaseLean3 false in
#align Action.res Action.res

/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
@[simps!]
def resId {G : MonCat} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)
set_option linter.uppercaseLean3 false in
#align Action.res_id Action.resId

/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
@[simps!]
def resComp {G H K : MonCat} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)
set_option linter.uppercaseLean3 false in
#align Action.res_comp Action.resComp

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

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
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_Action CategoryTheory.Functor.mapAction

end CategoryTheory.Functor
