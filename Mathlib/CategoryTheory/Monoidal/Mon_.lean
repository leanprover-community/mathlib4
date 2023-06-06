/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.Mon_
! leanprover-community/mathlib commit a836c6dba9bd1ee2a0cdc9af0006a596f243031c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Monoidal.Discrete
import Mathbin.CategoryTheory.Monoidal.CoherenceLemmas
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.Algebra.PunitInstances

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ where
  pt : C
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul' : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).Hom := by obviously
  mul_one' : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).Hom := by obviously
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc' : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).Hom ≫ (𝟙 X ⊗ mul) ≫ mul := by obviously
#align Mon_ Mon_

restate_axiom Mon_.one_mul'

restate_axiom Mon_.mul_one'

restate_axiom Mon_.mul_assoc'

attribute [reassoc] Mon_.one_mul Mon_.mul_one

-- We prove a more general `@[simp]` lemma below.
attribute [simp, reassoc] Mon_.mul_assoc

namespace Mon_

/-- The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps]
def trivial : Mon_ C where
  pt := 𝟙_ C
  one := 𝟙 _
  mul := (λ_ _).Hom
  mul_assoc' := by coherence
  mul_one' := by coherence
#align Mon_.trivial Mon_.trivial

instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩

variable {C} {M : Mon_ C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.pt) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).Hom ≫ f := by
  rw [← id_tensor_comp_tensor_id, category.assoc, M.one_mul, left_unitor_naturality]
#align Mon_.one_mul_hom Mon_.one_mul_hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.pt) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).Hom ≫ f := by
  rw [← tensor_id_comp_id_tensor, category.assoc, M.mul_one, right_unitor_naturality]
#align Mon_.mul_one_hom Mon_.mul_one_hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem assoc_flip :
    (𝟙 M.pt ⊗ M.mul) ≫ M.mul = (α_ M.pt M.pt M.pt).inv ≫ (M.mul ⊗ 𝟙 M.pt) ≫ M.mul := by simp
#align Mon_.assoc_flip Mon_.assoc_flip

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mon_ C) where
  Hom : M.pt ⟶ N.pt
  one_hom' : M.one ≫ hom = N.one := by obviously
  mul_hom' : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul := by obviously
#align Mon_.hom Mon_.Hom

restate_axiom hom.one_hom'

restate_axiom hom.mul_hom'

attribute [simp, reassoc] hom.one_hom hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : Hom M M where Hom := 𝟙 M.pt
#align Mon_.id Mon_.id

instance homInhabited (M : Mon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩
#align Mon_.hom_inhabited Mon_.homInhabited

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where Hom := f.Hom ≫ g.Hom
#align Mon_.comp Mon_.comp

instance : Category (Mon_ C) where
  Hom M N := Hom M N
  id := id
  comp M N O f g := comp f g

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).Hom = 𝟙 M.pt :=
  rfl
#align Mon_.id_hom' Mon_.id_hom'

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl
#align Mon_.comp_hom' Mon_.comp_hom'

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C where
  obj A := A.pt
  map A B f := f.Hom
#align Mon_.forget Mon_.forget

end

instance forget_faithful : Faithful (@forget C _ _) where
#align Mon_.forget_faithful Mon_.forget_faithful

instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.Hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : ReflectsIsomorphisms (forget C)
    where reflects X Y f e :=
    ⟨⟨{   Hom := inv f.hom
          mul_hom' := by
            simp only [is_iso.comp_inv_eq, hom.mul_hom, category.assoc, ← tensor_comp_assoc,
              is_iso.inv_hom_id, tensor_id, category.id_comp] },
        by tidy⟩⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
def isoOfIso {M N : Mon_ C} (f : M.pt ≅ N.pt) (one_f : M.one ≫ f.Hom = N.one)
    (mul_f : M.mul ≫ f.Hom = (f.Hom ⊗ f.Hom) ≫ N.mul) : M ≅ N
    where
  Hom :=
    { Hom := f.Hom
      one_hom' := one_f
      mul_hom' := mul_f }
  inv :=
    { Hom := f.inv
      one_hom' := by rw [← one_f]; simp
      mul_hom' := by
        rw [← cancel_mono f.hom]
        slice_rhs 2 3 => rw [mul_f]
        simp }
#align Mon_.iso_of_iso Mon_.isoOfIso

instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A)
    where
  default :=
    { Hom := A.one
      one_hom' := by dsimp; simp
      mul_hom' := by dsimp; simp [A.one_mul, unitors_equal] }
  uniq f := by
    ext; simp
    rw [← category.id_comp f.hom]
    erw [f.one_hom]
#align Mon_.unique_hom_from_trivial Mon_.uniqueHomFromTrivial

open CategoryTheory.Limits

instance : HasInitial (Mon_ C) :=
  hasInitial_of_unique (trivial C)

end Mon_

namespace CategoryTheory.LaxMonoidalFunctor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

-- TODO: map_Mod F A : Mod A ⥤ Mod (F.map_Mon A)
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
@[simps]
def mapMon (F : LaxMonoidalFunctor C D) : Mon_ C ⥤ Mon_ D
    where
  obj A :=
    { pt := F.obj A.pt
      one := F.ε ≫ F.map A.one
      mul := F.μ _ _ ≫ F.map A.mul
      one_mul' := by
        conv_lhs => rw [comp_tensor_id, ← F.to_functor.map_id]
        slice_lhs 2 3 => rw [F.μ_natural]
        slice_lhs 3 4 => rw [← F.to_functor.map_comp, A.one_mul]
        rw [F.to_functor.map_id]
        rw [F.left_unitality]
      mul_one' := by
        conv_lhs => rw [id_tensor_comp, ← F.to_functor.map_id]
        slice_lhs 2 3 => rw [F.μ_natural]
        slice_lhs 3 4 => rw [← F.to_functor.map_comp, A.mul_one]
        rw [F.to_functor.map_id]
        rw [F.right_unitality]
      mul_assoc' := by
        conv_lhs => rw [comp_tensor_id, ← F.to_functor.map_id]
        slice_lhs 2 3 => rw [F.μ_natural]
        slice_lhs 3 4 => rw [← F.to_functor.map_comp, A.mul_assoc]
        conv_lhs => rw [F.to_functor.map_id]
        conv_lhs => rw [F.to_functor.map_comp, F.to_functor.map_comp]
        conv_rhs => rw [id_tensor_comp, ← F.to_functor.map_id]
        slice_rhs 3 4 => rw [F.μ_natural]
        conv_rhs => rw [F.to_functor.map_id]
        slice_rhs 1 3 => rw [← F.associativity]
        simp only [category.assoc] }
  map A B f :=
    { Hom := F.map f.Hom
      one_hom' := by dsimp; rw [category.assoc, ← F.to_functor.map_comp, f.one_hom]
      mul_hom' := by
        dsimp
        rw [category.assoc, F.μ_natural_assoc, ← F.to_functor.map_comp, ← F.to_functor.map_comp,
          f.mul_hom] }
  map_id' A := by ext; simp
  map_comp' A B C f g := by ext; simp
#align category_theory.lax_monoidal_functor.map_Mon CategoryTheory.LaxMonoidalFunctor.mapMon

variable (C D)

/-- `map_Mon` is functorial in the lax monoidal functor. -/
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_ C ⥤ Mon_ D
    where
  obj := mapMon
  map F G α := { app := fun A => { Hom := α.app A.pt } }
#align category_theory.lax_monoidal_functor.map_Mon_functor CategoryTheory.LaxMonoidalFunctor.mapMonFunctor

end CategoryTheory.LaxMonoidalFunctor

namespace Mon_

open CategoryTheory.LaxMonoidalFunctor

namespace EquivLaxMonoidalFunctorPunit

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_ C
    where
  obj F := (F.mapMon : Mon_ _ ⥤ Mon_ C).obj (trivial (Discrete PUnit))
  map F G α := ((mapMonFunctor (Discrete PUnit) C).map α).app _
#align Mon_.equiv_lax_monoidal_functor_punit.lax_monoidal_to_Mon Mon_.EquivLaxMonoidalFunctorPunit.laxMonoidalToMon

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def monToLaxMonoidal : Mon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C
    where
  obj A :=
    { obj := fun _ => A.pt
      map := fun _ _ _ => 𝟙 _
      ε := A.one
      μ := fun _ _ => A.mul
      map_id' := fun _ => rfl
      map_comp' := fun _ _ _ _ _ => (Category.id_comp (𝟙 A.pt)).symm }
  map A B f :=
    { app := fun _ => f.Hom
      naturality' := fun _ _ _ => by dsimp; rw [category.id_comp, category.comp_id]
      unit' := f.OneHom
      tensor' := fun _ _ => f.MulHom }
#align Mon_.equiv_lax_monoidal_functor_punit.Mon_to_lax_monoidal Mon_.EquivLaxMonoidalFunctorPunit.monToLaxMonoidal

attribute [local tidy] tactic.discrete_cases

attribute [local simp] eq_to_iso_map

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F =>
      MonoidalNatIso.ofComponents (fun _ => F.toFunctor.mapIso (eqToIso (by ext))) (by tidy)
        (by tidy) (by tidy))
    (by tidy)
#align Mon_.equiv_lax_monoidal_functor_punit.unit_iso Mon_.EquivLaxMonoidalFunctorPunit.unitIso

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents
    (fun F =>
      { Hom := { Hom := 𝟙 _ }
        inv := { Hom := 𝟙 _ } })
    (by tidy)
#align Mon_.equiv_lax_monoidal_functor_punit.counit_iso Mon_.EquivLaxMonoidalFunctorPunit.counitIso

end EquivLaxMonoidalFunctorPunit

open EquivLaxMonoidalFunctorPunit

attribute [local simp] eq_to_iso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPunit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_ C
    where
  Functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C
#align Mon_.equiv_lax_monoidal_functor_punit Mon_.equivLaxMonoidalFunctorPunit

end Mon_

namespace Mon_

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`, the multiplication on the tensor
product `M.X ⊗ N.X` is defined in the obvious way: it is the tensor product of the multiplications
on `M` and `N`, except that the tensor factors in the source come in the wrong order, which we fix
by pre-composing with a permutation isomorphism constructed from the braiding.

A more conceptual way of understanding this definition is the following: The braiding on `C` gives
rise to a monoidal structure on the tensor product functor from `C × C` to `C`.  A pair of monoids
in `C` gives rise to a monoid in `C × C`, which the tensor product functor by being monoidal takes
to a monoid in `C`.  The permutation isomorphism appearing in the definition of the multiplication
on the tensor product of two monoids is an instance of a more general family of isomorphisms which
together form a strength that equips the tensor product functor with a monoidal structure, and the
monoid axioms for the tensor product follow from the monoid axioms for the tensor factors plus the
properties of the strength (i.e., monoidal functor axioms).  The strength `tensor_μ` of the tensor
product functor has been defined in `category_theory.monoidal.braided`.  Its properties, stated as
independent lemmas in that module, are used extensively in the proofs below.  Notice that we could
have followed the above plan not only conceptually but also as a possible implementation and could
have constructed the tensor product of monoids via `map_Mon`, but we chose to give a more explicit
definition directly in terms of `tensor_μ`.

To complete the definition of the monoidal category structure on the category of monoids, we need
to provide definitions of associator and unitors.  The obvious candidates are the associator and
unitors from `C`, but we need to prove that they are monoid morphisms, i.e., compatible with unit
and multiplication.  These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate), which have also been proved
in `category_theory.monoidal.braided`.

-/


variable {C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- The proofs that associators and unitors preserve monoid units don't require braiding.
theorem one_associator {M N P : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ P.one)) ≫ (α_ M.pt N.pt P.pt).Hom =
      (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ (λ_ (𝟙_ C)).inv ≫ (N.one ⊗ P.one)) :=
  by
  simp
  slice_lhs 1 3 => rw [← category.id_comp P.one, tensor_comp]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← category.id_comp M.one, tensor_comp]
  slice_lhs 1 2 => rw [← left_unitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [left_unitor_inv_naturality]
  simp only [category.assoc]
#align Mon_.one_associator Mon_.one_associator

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem one_leftUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ M.one)) ≫ (λ_ M.pt).Hom = M.one := by
  slice_lhs 2 3 => rw [left_unitor_naturality]; simp
#align Mon_.one_left_unitor Mon_.one_leftUnitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem one_rightUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M.pt).Hom = M.one := by
  slice_lhs 2 3 => rw [right_unitor_naturality, ← unitors_equal]; simp
#align Mon_.one_right_unitor Mon_.one_rightUnitor

variable [BraidedCategory C]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Mon_tensor_one_mul (M N : Mon_ C) :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ 𝟙 (M.pt ⊗ N.pt)) ≫
        tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul) =
      (λ_ (M.pt ⊗ N.pt)).Hom :=
  by
  rw [← category.id_comp (𝟙 (M.X ⊗ N.X)), tensor_comp]
  slice_lhs 2 3 => rw [← tensor_id, tensor_μ_natural]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul M, one_mul N]
  symm
  exact tensor_left_unitality C M.X N.X
#align Mon_.Mon_tensor_one_mul Mon_.Mon_tensor_one_mul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Mon_tensor_mul_one (M N : Mon_ C) :
    (𝟙 (M.pt ⊗ N.pt) ⊗ (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
        tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul) =
      (ρ_ (M.pt ⊗ N.pt)).Hom :=
  by
  rw [← category.id_comp (𝟙 (M.X ⊗ N.X)), tensor_comp]
  slice_lhs 2 3 => rw [← tensor_id, tensor_μ_natural]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one M, mul_one N]
  symm
  exact tensor_right_unitality C M.X N.X
#align Mon_.Mon_tensor_mul_one Mon_.Mon_tensor_mul_one

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Mon_tensor_mul_assoc (M N : Mon_ C) :
    (tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul) ⊗ 𝟙 (M.pt ⊗ N.pt)) ≫
        tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul) =
      (α_ (M.pt ⊗ N.pt) (M.pt ⊗ N.pt) (M.pt ⊗ N.pt)).Hom ≫
        (𝟙 (M.pt ⊗ N.pt) ⊗ tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul)) ≫
          tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul) :=
  by
  rw [← category.id_comp (𝟙 (M.X ⊗ N.X)), tensor_comp]
  slice_lhs 2 3 => rw [← tensor_id, tensor_μ_natural]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc M, mul_assoc N, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensor_μ_natural]
  slice_lhs 2 3 => rw [← tensor_comp, tensor_id]
  simp only [category.assoc]
#align Mon_.Mon_tensor_mul_assoc Mon_.Mon_tensor_mul_assoc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mul_associator {M N P : Mon_ C} :
    (tensor_μ C (M.pt ⊗ N.pt, P.pt) (M.pt ⊗ N.pt, P.pt) ≫
          (tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul) ⊗ P.mul)) ≫
        (α_ M.pt N.pt P.pt).Hom =
      ((α_ M.pt N.pt P.pt).Hom ⊗ (α_ M.pt N.pt P.pt).Hom) ≫
        tensor_μ C (M.pt, N.pt ⊗ P.pt) (M.pt, N.pt ⊗ P.pt) ≫
          (M.mul ⊗ tensor_μ C (N.pt, P.pt) (N.pt, P.pt) ≫ (N.mul ⊗ P.mul)) :=
  by
  simp
  slice_lhs 2 3 => rw [← category.id_comp P.mul, tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← category.id_comp M.mul, tensor_comp]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [category.assoc]
#align Mon_.mul_associator Mon_.mul_associator

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mul_leftUnitor {M : Mon_ C} :
    (tensor_μ C (𝟙_ C, M.pt) (𝟙_ C, M.pt) ≫ ((λ_ (𝟙_ C)).Hom ⊗ M.mul)) ≫ (λ_ M.pt).Hom =
      ((λ_ M.pt).Hom ⊗ (λ_ M.pt).Hom) ≫ M.mul :=
  by
  rw [← category.comp_id (λ_ (𝟙_ C)).Hom, ← category.id_comp M.mul, tensor_comp]
  slice_lhs 3 4 => rw [left_unitor_naturality]
  slice_lhs 1 3 => rw [← left_unitor_monoidal]
  simp only [category.assoc, category.id_comp]
#align Mon_.mul_left_unitor Mon_.mul_leftUnitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mul_rightUnitor {M : Mon_ C} :
    (tensor_μ C (M.pt, 𝟙_ C) (M.pt, 𝟙_ C) ≫ (M.mul ⊗ (λ_ (𝟙_ C)).Hom)) ≫ (ρ_ M.pt).Hom =
      ((ρ_ M.pt).Hom ⊗ (ρ_ M.pt).Hom) ≫ M.mul :=
  by
  rw [← category.id_comp M.mul, ← category.comp_id (λ_ (𝟙_ C)).Hom, tensor_comp]
  slice_lhs 3 4 => rw [right_unitor_naturality]
  slice_lhs 1 3 => rw [← right_unitor_monoidal]
  simp only [category.assoc, category.id_comp]
#align Mon_.mul_right_unitor Mon_.mul_rightUnitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance monMonoidal : MonoidalCategory (Mon_ C)
    where
  tensorObj M N :=
    { pt := M.pt ⊗ N.pt
      one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)
      mul := tensor_μ C (M.pt, N.pt) (M.pt, N.pt) ≫ (M.mul ⊗ N.mul)
      one_mul' := Mon_tensor_one_mul M N
      mul_one' := Mon_tensor_mul_one M N
      mul_assoc' := Mon_tensor_mul_assoc M N }
  tensorHom M N P Q f g :=
    { Hom := f.Hom ⊗ g.Hom
      one_hom' := by
        dsimp
        slice_lhs 2 3 => rw [← tensor_comp, hom.one_hom f, hom.one_hom g]
      mul_hom' := by
        dsimp
        slice_rhs 1 2 => rw [tensor_μ_natural]
        slice_lhs 2 3 => rw [← tensor_comp, hom.mul_hom f, hom.mul_hom g, tensor_comp]
        simp only [category.assoc] }
  tensor_id' := by intros; ext; apply tensor_id
  tensor_comp' := by intros; ext; apply tensor_comp
  tensorUnit := trivial C
  associator M N P := isoOfIso (α_ M.pt N.pt P.pt) one_associator mul_associator
  associator_naturality' := by intros; ext; dsimp; apply associator_naturality
  leftUnitor M := isoOfIso (λ_ M.pt) one_leftUnitor mul_leftUnitor
  leftUnitor_naturality' := by intros; ext; dsimp; apply left_unitor_naturality
  rightUnitor M := isoOfIso (ρ_ M.pt) one_rightUnitor mul_rightUnitor
  rightUnitor_naturality' := by intros; ext; dsimp; apply right_unitor_naturality
  pentagon' := by intros; ext; dsimp; apply pentagon
  triangle' := by intros; ext; dsimp; apply triangle
#align Mon_.Mon_monoidal Mon_.monMonoidal

end Mon_

/-!
Projects:
* Check that `Mon_ Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first, available in #3463)
* Check that `Mon_ Top ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGroup ≌ Ring`.
  (We've already got `Mon_ (Module R) ≌ Algebra R`, in `category_theory.monoidal.internal.Module`.)
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
* Show that when `C` is braided, the forgetful functor `Mon_ C ⥤ C` is monoidal.
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor `map_Mon F : Mon_ C ⥤ Mon_ D`
  is lax monoidal.
-/


