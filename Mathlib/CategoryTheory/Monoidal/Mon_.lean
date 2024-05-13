/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Algebra.PUnitInstances

#align_import category_theory.monoidal.Mon_ from "leanprover-community/mathlib"@"a836c6dba9bd1ee2a0cdc9af0006a596f243031c"

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/

set_option linter.uppercaseLean3 false

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ where
  X : C
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul : (one ▷ X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat
#align Mon_ Mon_

attribute [reassoc] Mon_.one_mul Mon_.mul_one

attribute [simp] Mon_.one_mul Mon_.mul_one

-- We prove a more general `@[simp]` lemma below.
attribute [reassoc (attr := simp)] Mon_.mul_assoc

namespace Mon_

/-- The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps]
def trivial : Mon_ C where
  X := 𝟙_ C
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc := by coherence
  mul_one := by coherence
#align Mon_.trivial Mon_.trivial

instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩

variable {C}
variable {M : Mon_ C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, M.one_mul, leftUnitor_naturality]
#align Mon_.one_mul_hom Mon_.one_mul_hom

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, M.mul_one, rightUnitor_naturality]
#align Mon_.mul_one_hom Mon_.mul_one_hom

theorem assoc_flip :
    (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul := by simp
#align Mon_.assoc_flip Mon_.assoc_flip

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mon_ C) where
  hom : M.X ⟶ N.X
  one_hom : M.one ≫ hom = N.one := by aesop_cat
  mul_hom : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul := by aesop_cat
#align Mon_.hom Mon_.Hom

attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : Hom M M where
  hom := 𝟙 M.X
#align Mon_.id Mon_.id

instance homInhabited (M : Mon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩
#align Mon_.hom_inhabited Mon_.homInhabited

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom
#align Mon_.comp Mon_.comp

instance : Category (Mon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

-- Porting note: added, as `Hom.ext` does not apply to a morphism.
@[ext]
lemma ext {X Y : Mon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext _ _ w

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl
#align Mon_.id_hom' Mon_.id_hom'

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl
#align Mon_.comp_hom' Mon_.comp_hom'

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C where
  obj A := A.X
  map f := f.hom
#align Mon_.forget Mon_.forget

end

instance forget_faithful : (forget C).Faithful where
#align Mon_.forget_faithful Mon_.forget_faithful

instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom
        mul_hom := by
          simp only [IsIso.comp_inv_eq, Hom.mul_hom, Category.assoc, ← tensor_comp_assoc,
            IsIso.inv_hom_id, tensor_id, Category.id_comp] },
        by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def isoOfIso {M N : Mon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one)
    (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul) : M ≅ N where
  hom :=
    { hom := f.hom
      one_hom := one_f
      mul_hom := mul_f }
  inv :=
    { hom := f.inv
      one_hom := by rw [← one_f]; simp
      mul_hom := by
        rw [← cancel_mono f.hom]
        slice_rhs 2 3 => rw [mul_f]
        simp }
#align Mon_.iso_of_iso Mon_.isoOfIso

instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A) where
  default :=
    { hom := A.one
      one_hom := by dsimp; simp
      mul_hom := by dsimp; simp [A.one_mul, unitors_equal] }
  uniq f := by
    ext; simp
    rw [← Category.id_comp f.hom]
    erw [f.one_hom]
#align Mon_.unique_hom_from_trivial Mon_.uniqueHomFromTrivial

open CategoryTheory.Limits

instance : HasInitial (Mon_ C) :=
  hasInitial_of_unique (trivial C)

end Mon_

namespace CategoryTheory.LaxMonoidalFunctor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMon A)
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
@[simps]
def mapMon (F : LaxMonoidalFunctor C D) : Mon_ C ⥤ Mon_ D where
  obj A :=
    { X := F.obj A.X
      one := F.ε ≫ F.map A.one
      mul := F.μ _ _ ≫ F.map A.mul
      one_mul := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, left_unitality]
        slice_lhs 3 4 => rw [← F.toFunctor.map_comp, A.one_mul]
      mul_one := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
          right_unitality]
        slice_lhs 3 4 => rw [← F.toFunctor.map_comp, A.mul_one]
      mul_assoc := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
        slice_lhs 3 4 => rw [← F.toFunctor.map_comp, A.mul_assoc]
        simp }
  map f :=
    { hom := F.map f.hom
      one_hom := by dsimp; rw [Category.assoc, ← F.toFunctor.map_comp, f.one_hom]
      mul_hom := by
        dsimp
        rw [Category.assoc, F.μ_natural_assoc, ← F.toFunctor.map_comp, ← F.toFunctor.map_comp,
          f.mul_hom] }
  map_id A := by ext; simp
  map_comp f g := by ext; simp
#align category_theory.lax_monoidal_functor.map_Mon CategoryTheory.LaxMonoidalFunctor.mapMon

variable (C D)

/-- `mapMon` is functorial in the lax monoidal functor. -/
@[simps] -- Porting note: added this, not sure how it worked previously without.
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_ C ⥤ Mon_ D where
  obj := mapMon
  map α := { app := fun A => { hom := α.app A.X } }
#align category_theory.lax_monoidal_functor.map_Mon_functor CategoryTheory.LaxMonoidalFunctor.mapMonFunctor

end CategoryTheory.LaxMonoidalFunctor

namespace Mon_

open CategoryTheory.LaxMonoidalFunctor

namespace EquivLaxMonoidalFunctorPUnit

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_ C where
  obj F := (F.mapMon : Mon_ _ ⥤ Mon_ C).obj (trivial (Discrete PUnit))
  map α := ((mapMonFunctor (Discrete PUnit) C).map α).app _
#align Mon_.equiv_lax_monoidal_functor_punit.lax_monoidal_to_Mon Mon_.EquivLaxMonoidalFunctorPUnit.laxMonoidalToMon

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : Mon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A :=
    { obj := fun _ => A.X
      map := fun _ => 𝟙 _
      ε := A.one
      μ := fun _ _ => A.mul
      map_id := fun _ => rfl
      map_comp := fun _ _ => (Category.id_comp (𝟙 A.X)).symm }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ _ => by dsimp; rw [Category.id_comp, Category.comp_id]
      unit := f.one_hom
      tensor := fun _ _ => f.mul_hom }
#align Mon_.equiv_lax_monoidal_functor_punit.Mon_to_lax_monoidal Mon_.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidal

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

attribute [local simp] eqToIso_map

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F =>
      MonoidalNatIso.ofComponents (fun _ => F.toFunctor.mapIso (eqToIso (by ext))) (by aesop_cat)
        (by aesop_cat) (by aesop_cat))
    (by aesop_cat)
#align Mon_.equiv_lax_monoidal_functor_punit.unit_iso Mon_.EquivLaxMonoidalFunctorPUnit.unitIso

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents
    (fun F =>
      { hom := { hom := 𝟙 _ }
        inv := { hom := 𝟙 _ } })
    (by aesop_cat)
#align Mon_.equiv_lax_monoidal_functor_punit.counit_iso Mon_.EquivLaxMonoidalFunctorPUnit.counitIso

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_ C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C
#align Mon_.equiv_lax_monoidal_functor_punit Mon_.equivLaxMonoidalFunctorPUnit

end Mon_

namespace Mon_

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the multiplication on the tensor product `M.X ⊗ N.X` is defined in the obvious way:
it is the tensor product of the multiplications on `M` and `N`,
except that the tensor factors in the source come in the wrong order,
which we fix by pre-composing with a permutation isomorphism constructed from the braiding.

(There is a subtlety here: in fact there are two ways to do these,
using either the positive or negative crossing.)

A more conceptual way of understanding this definition is the following:
The braiding on `C` gives rise to a monoidal structure on
the tensor product functor from `C × C` to `C`.
A pair of monoids in `C` gives rise to a monoid in `C × C`,
which the tensor product functor by being monoidal takes to a monoid in `C`.
The permutation isomorphism appearing in the definition of
the multiplication on the tensor product of two monoids is
an instance of a more general family of isomorphisms
which together form a strength that equips the tensor product functor with a monoidal structure,
and the monoid axioms for the tensor product follow from the monoid axioms for the tensor factors
plus the properties of the strength (i.e., monoidal functor axioms).
The strength `tensor_μ` of the tensor product functor has been defined in
`Mathlib.CategoryTheory.Monoidal.Braided`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapMon`,
but we chose to give a more explicit definition directly in terms of `tensor_μ`.

To complete the definition of the monoidal category structure on the category of monoids,
we need to provide definitions of associator and unitors.
The obvious candidates are the associator and unitors from `C`,
but we need to prove that they are monoid morphisms, i.e., compatible with unit and multiplication.
These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate),
which have also been proved in `Mathlib.CategoryTheory.Monoidal.Braided`.

-/


variable {C}

-- The proofs that associators and unitors preserve monoid units don't require braiding.
theorem one_associator {M N P : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ P.one)) ≫ (α_ M.X N.X P.X).hom =
      (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ (λ_ (𝟙_ C)).inv ≫ (N.one ⊗ P.one)) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp P.one, tensor_comp]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp M.one, tensor_comp]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp
#align Mon_.one_associator Mon_.one_associator

theorem one_leftUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ M.one)) ≫ (λ_ M.X).hom = M.one := by
  simp
#align Mon_.one_left_unitor Mon_.one_leftUnitor

theorem one_rightUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M.X).hom = M.one := by
  simp [← unitors_equal]
#align Mon_.one_right_unitor Mon_.one_rightUnitor

variable [BraidedCategory C]

theorem Mon_tensor_one_mul (M N : Mon_ C) :
    (((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ▷ (M.X ⊗ N.X)) ≫
        tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) =
      (λ_ (M.X ⊗ N.X)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensor_μ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul M, one_mul N]
  symm
  exact tensor_left_unitality C M.X N.X
#align Mon_.Mon_tensor_one_mul Mon_.Mon_tensor_one_mul

theorem Mon_tensor_mul_one (M N : Mon_ C) :
    (M.X ⊗ N.X) ◁ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
        tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) =
      (ρ_ (M.X ⊗ N.X)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensor_μ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one M, mul_one N]
  symm
  exact tensor_right_unitality C M.X N.X
#align Mon_.Mon_tensor_mul_one Mon_.Mon_tensor_mul_one

theorem Mon_tensor_mul_assoc (M N : Mon_ C) :
    ((tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)) ▷ (M.X ⊗ N.X)) ≫
        tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) =
      (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫
        ((M.X ⊗ N.X) ◁ (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul))) ≫
          tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) := by
  simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensor_μ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc M, mul_assoc N, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensor_μ_natural_right]
  simp
#align Mon_.Mon_tensor_mul_assoc Mon_.Mon_tensor_mul_assoc

theorem mul_associator {M N P : Mon_ C} :
    (tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫
          (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) ⊗ P.mul)) ≫
        (α_ M.X N.X P.X).hom =
      ((α_ M.X N.X P.X).hom ⊗ (α_ M.X N.X P.X).hom) ≫
        tensor_μ C (M.X, N.X ⊗ P.X) (M.X, N.X ⊗ P.X) ≫
          (M.mul ⊗ tensor_μ C (N.X, P.X) (N.X, P.X) ≫ (N.mul ⊗ P.mul)) := by
  simp only [tensor_obj, prodMonoidal_tensorObj, Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp P.mul, tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp M.mul, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]
#align Mon_.mul_associator Mon_.mul_associator

theorem mul_leftUnitor {M : Mon_ C} :
    (tensor_μ C (𝟙_ C, M.X) (𝟙_ C, M.X) ≫ ((λ_ (𝟙_ C)).hom ⊗ M.mul)) ≫ (λ_ M.X).hom =
      ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ M.mul := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp M.mul, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]
#align Mon_.mul_left_unitor Mon_.mul_leftUnitor

theorem mul_rightUnitor {M : Mon_ C} :
    (tensor_μ C (M.X, 𝟙_ C) (M.X, 𝟙_ C) ≫ (M.mul ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M.X).hom =
      ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ M.mul := by
  rw [← Category.id_comp M.mul, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]
#align Mon_.mul_right_unitor Mon_.mul_rightUnitor

@[simps tensorObj_X tensorHom_hom]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_ C) :=
  let tensorObj (M N : Mon_ C) : Mon_ C :=
    { X := M.X ⊗ N.X
      one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)
      mul := tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
      one_mul := Mon_tensor_one_mul M N
      mul_one := Mon_tensor_mul_one M N
      mul_assoc := Mon_tensor_mul_assoc M N }
  let tensorHom {X₁ Y₁ X₂ Y₂ : Mon_ C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
      tensorObj _ _ ⟶ tensorObj _ _ :=
    { hom := f.hom ⊗ g.hom
      one_hom := by
        dsimp
        slice_lhs 2 3 => rw [← tensor_comp, Hom.one_hom f, Hom.one_hom g]
      mul_hom := by
        dsimp
        slice_rhs 1 2 => rw [tensor_μ_natural]
        slice_lhs 2 3 => rw [← tensor_comp, Hom.mul_hom f, Hom.mul_hom g, tensor_comp]
        simp only [Category.assoc] }
  { tensorObj := tensorObj
    tensorHom := tensorHom
    whiskerRight := fun f Y => tensorHom f (𝟙 Y)
    whiskerLeft := fun X _ _ g => tensorHom (𝟙 X) g
    tensorUnit := trivial C
    associator := fun M N P ↦ isoOfIso (α_ M.X N.X P.X) one_associator mul_associator
    leftUnitor := fun M ↦ isoOfIso (λ_ M.X) one_leftUnitor mul_leftUnitor
    rightUnitor := fun M ↦ isoOfIso (ρ_ M.X) one_rightUnitor mul_rightUnitor }

@[simp]
theorem tensorUnit_X : (𝟙_ (Mon_ C)).X = 𝟙_ C := rfl

@[simp]
theorem whiskerLeft_hom {X Y : Mon_ C} (f : X ⟶ Y) (Z : Mon_ C) :
    (f ▷ Z).hom = f.hom ▷ Z.X := by
  rw [← tensorHom_id]; rfl

@[simp]
theorem whiskerRight_hom (X : Mon_ C) {Y Z : Mon_ C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.X ◁ f.hom := by
  rw [← id_tensorHom]; rfl

@[simp]
theorem leftUnitor_hom_hom (X : Mon_ C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl

@[simp]
theorem leftUnitor_inv_hom (X : Mon_ C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl

@[simp]
theorem rightUnitor_hom_hom (X : Mon_ C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl

@[simp]
theorem rightUnitor_inv_hom (X : Mon_ C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[simp]
theorem associator_hom_hom (X Y Z : Mon_ C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl

@[simp]
theorem associator_inv_hom (X Y Z : Mon_ C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

instance monMonoidal : MonoidalCategory (Mon_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
#align Mon_.Mon_monoidal Mon_.monMonoidal

variable (C)

/-- The forgetful functor from `Mon_ C` to `C` is monoidal when `C` is braided monoidal. -/
def forgetMonoidal : MonoidalFunctor (Mon_ C) C :=
  { forget C with
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }

@[simp] theorem forgetMonoidal_toFunctor : (forgetMonoidal C).toFunctor = forget C := rfl
@[simp] theorem forgetMonoidal_ε : (forgetMonoidal C).ε = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forgetMonoidal_μ (X Y : Mon_ C) : (forgetMonoidal C).μ X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end Mon_

/-!
Projects:
* Check that `Mon_ MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `MonCat` first,
  available in mathlib3#3463)
* More generally, check that `Mon_ (Mon_ C) ≌ CommMon_ C` when `C` is braided.
* Check that `Mon_ TopCat ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGroupCat ≌ RingCat`.
  (We've already got `Mon_ (ModuleCat R) ≌ AlgebraCat R`,
  in `Mathlib.CategoryTheory.Monoidal.Internal.Module`.)
* Can you transport this monoidal structure to `RingCat` or `AlgebraCat R`?
  How does it compare to the "native" one?
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor `map_Mon F : Mon_ C ⥤ Mon_ D`
  is lax monoidal.
-/
