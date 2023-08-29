/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided
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
  one_mul : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).hom ≫ (𝟙 X ⊗ mul) ≫ mul := by aesop_cat
#align Mon_ Mon_

attribute [reassoc] Mon_.one_mul Mon_.mul_one

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
                  -- 🎉 no goals
                -- 🎉 no goals
  mul_one := by coherence
#align Mon_.trivial Mon_.trivial

instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩

variable {C}
variable {M : Mon_ C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).hom ≫ f := by
  rw [← id_tensor_comp_tensor_id, Category.assoc, M.one_mul, leftUnitor_naturality]
  -- 🎉 no goals
#align Mon_.one_mul_hom Mon_.one_mul_hom

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).hom ≫ f := by
  rw [← tensor_id_comp_id_tensor, Category.assoc, M.mul_one, rightUnitor_naturality]
  -- 🎉 no goals
#align Mon_.mul_one_hom Mon_.mul_one_hom

theorem assoc_flip :
    (𝟙 M.X ⊗ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ⊗ 𝟙 M.X) ≫ M.mul := by simp
                                                                                   -- 🎉 no goals
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

instance forget_faithful : Faithful (@forget C _ _) where
#align Mon_.forget_faithful Mon_.forget_faithful

instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : ReflectsIsomorphisms (forget C) where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom
        mul_hom := by
          simp only [IsIso.comp_inv_eq, Hom.mul_hom, Category.assoc, ← tensor_comp_assoc,
            IsIso.inv_hom_id, tensor_id, Category.id_comp] },
        by aesop_cat⟩⟩
           -- 🎉 no goals

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
def isoOfIso {M N : Mon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one)
    (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul) : M ≅ N where
  hom :=
    { hom := f.hom
      one_hom := one_f
      mul_hom := mul_f }
  inv :=
    { hom := f.inv
      one_hom := by rw [← one_f]; simp
                    -- ⊢ (M.one ≫ f.hom) ≫ f.inv = M.one
                                  -- 🎉 no goals
      mul_hom := by
        rw [← cancel_mono f.hom]
        -- ⊢ (N.mul ≫ f.inv) ≫ f.hom = ((f.inv ⊗ f.inv) ≫ M.mul) ≫ f.hom
        slice_rhs 2 3 => rw [mul_f]
        -- ⊢ (N.mul ≫ f.inv) ≫ f.hom = (f.inv ⊗ f.inv) ≫ (f.hom ⊗ f.hom) ≫ N.mul
        simp }
        -- 🎉 no goals
#align Mon_.iso_of_iso Mon_.isoOfIso

instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A) where
  default :=
    { hom := A.one
      one_hom := by dsimp; simp
                    -- ⊢ 𝟙 (𝟙_ C) ≫ A.one = A.one
                           -- 🎉 no goals
      mul_hom := by dsimp; simp [A.one_mul, unitors_equal] }
                    -- ⊢ (λ_ (𝟙_ C)).hom ≫ A.one = (A.one ⊗ A.one) ≫ A.mul
                           -- 🎉 no goals
  uniq f := by
    ext; simp
    -- ⊢ f.hom = default.hom
         -- ⊢ f.hom = A.one
    rw [← Category.id_comp f.hom]
    -- ⊢ 𝟙 (trivial C).X ≫ f.hom = A.one
    erw [f.one_hom]
    -- 🎉 no goals
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
        conv_lhs => rw [comp_tensor_id, ← F.toFunctor.map_id]
        -- ⊢ ((F.ε ⊗ F.map (𝟙 A.X)) ≫ (F.map A.one ⊗ F.map (𝟙 A.X))) ≫ μ F A.X A.X ≫ F.ma …
        slice_lhs 2 3 => rw [F.μ_natural]
        -- ⊢ (F.ε ⊗ F.map (𝟙 A.X)) ≫ (μ F (𝟙_ C) A.X ≫ F.map (A.one ⊗ 𝟙 A.X)) ≫ F.map A.m …
        slice_lhs 3 4 => rw [← F.toFunctor.map_comp, A.one_mul]
        -- ⊢ (F.ε ⊗ F.map (𝟙 A.X)) ≫ μ F (𝟙_ C) A.X ≫ F.map (λ_ A.X).hom = (λ_ (F.obj A.X …
        rw [F.toFunctor.map_id]
        -- ⊢ (F.ε ⊗ 𝟙 (F.obj A.X)) ≫ μ F (𝟙_ C) A.X ≫ F.map (λ_ A.X).hom = (λ_ (F.obj A.X …
        rw [F.left_unitality]
        -- 🎉 no goals
      mul_one := by
        conv_lhs => rw [id_tensor_comp, ← F.toFunctor.map_id]
        -- ⊢ ((F.map (𝟙 A.X) ⊗ F.ε) ≫ (F.map (𝟙 A.X) ⊗ F.map A.one)) ≫ μ F A.X A.X ≫ F.ma …
        slice_lhs 2 3 => rw [F.μ_natural]
        -- ⊢ (F.map (𝟙 A.X) ⊗ F.ε) ≫ (μ F A.X (𝟙_ C) ≫ F.map (𝟙 A.X ⊗ A.one)) ≫ F.map A.m …
        slice_lhs 3 4 => rw [← F.toFunctor.map_comp, A.mul_one]
        -- ⊢ (F.map (𝟙 A.X) ⊗ F.ε) ≫ μ F A.X (𝟙_ C) ≫ F.map (ρ_ A.X).hom = (ρ_ (F.obj A.X …
        rw [F.toFunctor.map_id]
        -- ⊢ (𝟙 (F.obj A.X) ⊗ F.ε) ≫ μ F A.X (𝟙_ C) ≫ F.map (ρ_ A.X).hom = (ρ_ (F.obj A.X …
        rw [F.right_unitality]
        -- 🎉 no goals
      mul_assoc := by
        conv_lhs => rw [comp_tensor_id, ← F.toFunctor.map_id]
        -- ⊢ ((μ F A.X A.X ⊗ F.map (𝟙 A.X)) ≫ (F.map A.mul ⊗ F.map (𝟙 A.X))) ≫ μ F A.X A. …
        slice_lhs 2 3 => rw [F.μ_natural]
        -- ⊢ (μ F A.X A.X ⊗ F.map (𝟙 A.X)) ≫ (μ F (A.X ⊗ A.X) A.X ≫ F.map (A.mul ⊗ 𝟙 A.X) …
        slice_lhs 3 4 => rw [← F.toFunctor.map_comp, A.mul_assoc]
        -- ⊢ (μ F A.X A.X ⊗ F.map (𝟙 A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map ((α_ A.X A.X A.X …
        conv_lhs => rw [F.toFunctor.map_id]
        -- ⊢ (μ F A.X A.X ⊗ 𝟙 (F.obj A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map ((α_ A.X A.X A.X …
        conv_lhs => rw [F.toFunctor.map_comp, F.toFunctor.map_comp]
        -- ⊢ (μ F A.X A.X ⊗ 𝟙 (F.obj A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map (α_ A.X A.X A.X) …
        conv_rhs => rw [id_tensor_comp, ← F.toFunctor.map_id]
        -- ⊢ (μ F A.X A.X ⊗ 𝟙 (F.obj A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map (α_ A.X A.X A.X) …
        slice_rhs 3 4 => rw [F.μ_natural]
        -- ⊢ (μ F A.X A.X ⊗ 𝟙 (F.obj A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map (α_ A.X A.X A.X) …
        conv_rhs => rw [F.toFunctor.map_id]
        -- ⊢ (μ F A.X A.X ⊗ 𝟙 (F.obj A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map (α_ A.X A.X A.X) …
        slice_rhs 1 3 => rw [← F.associativity]
        -- ⊢ (μ F A.X A.X ⊗ 𝟙 (F.obj A.X)) ≫ μ F (A.X ⊗ A.X) A.X ≫ F.map (α_ A.X A.X A.X) …
        simp only [Category.assoc] }
        -- 🎉 no goals
  map f :=
    { hom := F.map f.hom
      one_hom := by dsimp; rw [Category.assoc, ← F.toFunctor.map_comp, f.one_hom]
                    -- ⊢ (F.ε ≫ F.map X✝.one) ≫ F.map f.hom = F.ε ≫ F.map Y✝.one
                           -- 🎉 no goals
      mul_hom := by
        dsimp
        -- ⊢ (μ F X✝.X X✝.X ≫ F.map X✝.mul) ≫ F.map f.hom = (F.map f.hom ⊗ F.map f.hom) ≫ …
        rw [Category.assoc, F.μ_natural_assoc, ← F.toFunctor.map_comp, ← F.toFunctor.map_comp,
          f.mul_hom] }
  map_id A := by ext; simp
                 -- ⊢ ({ obj := fun A => Mon_.mk (F.obj A.X) (F.ε ≫ F.map A.one) (μ F A.X A.X ≫ F. …
                      -- 🎉 no goals
  map_comp f g := by ext; simp
                     -- ⊢ ({ obj := fun A => Mon_.mk (F.obj A.X) (F.ε ≫ F.map A.one) (μ F A.X A.X ≫ F. …
                          -- 🎉 no goals
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
                                    -- ⊢ 𝟙 X✝.X ≫ f.hom = f.hom ≫ 𝟙 Y✝.X
                                           -- 🎉 no goals
      unit := f.one_hom
      tensor := fun _ _ => f.mul_hom }
#align Mon_.equiv_lax_monoidal_functor_punit.Mon_to_lax_monoidal Mon_.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidal

attribute [local aesop safe tactic (rule_sets [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

attribute [local simp] eqToIso_map

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F =>
      MonoidalNatIso.ofComponents (fun _ => F.toFunctor.mapIso (eqToIso (by ext))) (by aesop_cat)
                                                                            -- 🎉 no goals
                                                                                       -- 🎉 no goals
        (by aesop_cat) (by aesop_cat))
            -- 🎉 no goals
                           -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
#align Mon_.equiv_lax_monoidal_functor_punit.unit_iso Mon_.EquivLaxMonoidalFunctorPUnit.unitIso

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents
    (fun F =>
      { hom := { hom := 𝟙 _ }
        inv := { hom := 𝟙 _ } })
    (by aesop_cat)
        -- 🎉 no goals
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
  simp
  -- ⊢ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ P.one) ≫ (α_ M.X N.X P.X).hom = M.one ⊗ …
  slice_lhs 1 3 => rw [← Category.id_comp P.one, tensor_comp]
  -- ⊢ (((λ_ (𝟙_ C)).inv ⊗ 𝟙 (𝟙_ C)) ≫ ((M.one ⊗ N.one) ⊗ P.one)) ≫ (α_ M.X N.X P.X …
  slice_lhs 2 3 => rw [associator_naturality]
  -- ⊢ ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (𝟙_ C)) ≫ (α_ tensorUnit' (𝟙_ C) (𝟙_ C)).hom ≫ (M.one ⊗ …
  slice_rhs 1 2 => rw [← Category.id_comp M.one, tensor_comp]
  -- ⊢ ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (𝟙_ C)) ≫ (α_ tensorUnit' (𝟙_ C) (𝟙_ C)).hom ≫ (M.one ⊗ …
  slice_lhs 1 2 => rw [← leftUnitor_tensor_inv]
  -- ⊢ (λ_ (tensorUnit' ⊗ 𝟙_ C)).inv ≫ (M.one ⊗ N.one ⊗ P.one) = (𝟙 (𝟙_ C) ⊗ (λ_ (𝟙 …
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  -- ⊢ (λ_ (𝟙_ C)).inv ≫ (λ_ (tensorUnit' ⊗ 𝟙_ C)).inv ≫ (M.one ⊗ N.one ⊗ P.one) =  …
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  -- ⊢ ((λ_ (𝟙_ C)).inv ≫ (𝟙 tensorUnit' ⊗ (λ_ (𝟙_ C)).inv)) ≫ (M.one ⊗ N.one ⊗ P.o …
  simp only [Category.assoc]
  -- 🎉 no goals
#align Mon_.one_associator Mon_.one_associator

theorem one_leftUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ M.one)) ≫ (λ_ M.X).hom = M.one := by
  slice_lhs 2 3 => rw [leftUnitor_naturality]
  -- ⊢ (λ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom ≫ M.one = M.one
  simp
  -- 🎉 no goals
#align Mon_.one_left_unitor Mon_.one_leftUnitor

theorem one_rightUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M.X).hom = M.one := by
  slice_lhs 2 3 => rw [rightUnitor_naturality, ← unitors_equal]
  -- ⊢ (λ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom ≫ M.one = M.one
  simp
  -- 🎉 no goals
#align Mon_.one_right_unitor Mon_.one_rightUnitor

variable [BraidedCategory C]

theorem Mon_tensor_one_mul (M N : Mon_ C) :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ 𝟙 (M.X ⊗ N.X)) ≫
        tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) =
      (λ_ (M.X ⊗ N.X)).hom := by
  rw [← Category.id_comp (𝟙 (M.X ⊗ N.X)), tensor_comp]
  -- ⊢ (((λ_ (𝟙_ C)).inv ⊗ 𝟙 (M.X ⊗ N.X)) ≫ ((M.one ⊗ N.one) ⊗ 𝟙 (M.X ⊗ N.X))) ≫ te …
  slice_lhs 2 3 => rw [← tensor_id, tensor_μ_natural]
  -- ⊢ ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (M.X ⊗ N.X)) ≫ (tensor_μ C (tensorUnit', 𝟙_ C) (M.X, N. …
  slice_lhs 3 4 => rw [← tensor_comp, one_mul M, one_mul N]
  -- ⊢ ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (M.X ⊗ N.X)) ≫ tensor_μ C (tensorUnit', 𝟙_ C) (M.X, N.X …
  symm
  -- ⊢ (λ_ (M.X ⊗ N.X)).hom = ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (M.X ⊗ N.X)) ≫ tensor_μ C (tenso …
  exact tensor_left_unitality C M.X N.X
  -- 🎉 no goals
#align Mon_.Mon_tensor_one_mul Mon_.Mon_tensor_one_mul

theorem Mon_tensor_mul_one (M N : Mon_ C) :
    (𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
        tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) =
      (ρ_ (M.X ⊗ N.X)).hom := by
  rw [← Category.id_comp (𝟙 (M.X ⊗ N.X)), tensor_comp]
  -- ⊢ ((𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv) ≫ (𝟙 (M.X ⊗ N.X) ⊗ M.one ⊗ N.one)) ≫ tens …
  slice_lhs 2 3 => rw [← tensor_id, tensor_μ_natural]
  -- ⊢ (𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv) ≫ (tensor_μ C (M.X, N.X) (tensorUnit', 𝟙_  …
  slice_lhs 3 4 => rw [← tensor_comp, mul_one M, mul_one N]
  -- ⊢ (𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv) ≫ tensor_μ C (M.X, N.X) (tensorUnit', 𝟙_ C …
  symm
  -- ⊢ (ρ_ (M.X ⊗ N.X)).hom = (𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv) ≫ tensor_μ C (M.X,  …
  exact tensor_right_unitality C M.X N.X
  -- 🎉 no goals
#align Mon_.Mon_tensor_mul_one Mon_.Mon_tensor_mul_one

theorem Mon_tensor_mul_assoc (M N : Mon_ C) :
    (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) ⊗ 𝟙 (M.X ⊗ N.X)) ≫
        tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) =
      (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫
        (𝟙 (M.X ⊗ N.X) ⊗ tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)) ≫
          tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) := by
  rw [← Category.id_comp (𝟙 (M.X ⊗ N.X)), tensor_comp]
  -- ⊢ ((tensor_μ C (M.X, N.X) (M.X, N.X) ⊗ 𝟙 (M.X ⊗ N.X)) ≫ ((M.mul ⊗ N.mul) ⊗ 𝟙 ( …
  slice_lhs 2 3 => rw [← tensor_id, tensor_μ_natural]
  -- ⊢ (tensor_μ C (M.X, N.X) (M.X, N.X) ⊗ 𝟙 (M.X ⊗ N.X)) ≫ (tensor_μ C (((M.X, N.X …
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc M, mul_assoc N, tensor_comp, tensor_comp]
  -- ⊢ (tensor_μ C (M.X, N.X) (M.X, N.X) ⊗ 𝟙 (M.X ⊗ N.X)) ≫ tensor_μ C (((M.X, N.X) …
  -- Porting note: needed to add `dsimp` here.
  slice_lhs 1 3 => dsimp; rw [tensor_associativity]
  -- ⊢ (((α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫ (𝟙 (M.X ⊗ N.X) ⊗ tensor_μ C …
  slice_lhs 3 4 => rw [← tensor_μ_natural]
  -- ⊢ (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫ (𝟙 (M.X ⊗ N.X) ⊗ tensor_μ C ( …
  slice_lhs 2 3 => rw [← tensor_comp, tensor_id]
  -- ⊢ (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫ ((𝟙 (M.X ⊗ N.X) ≫ 𝟙 (M.X ⊗ N. …
  simp only [Category.assoc]
  -- 🎉 no goals
#align Mon_.Mon_tensor_mul_assoc Mon_.Mon_tensor_mul_assoc

theorem mul_associator {M N P : Mon_ C} :
    (tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫
          (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) ⊗ P.mul)) ≫
        (α_ M.X N.X P.X).hom =
      ((α_ M.X N.X P.X).hom ⊗ (α_ M.X N.X P.X).hom) ≫
        tensor_μ C (M.X, N.X ⊗ P.X) (M.X, N.X ⊗ P.X) ≫
          (M.mul ⊗ tensor_μ C (N.X, P.X) (N.X, P.X) ≫ (N.mul ⊗ P.mul)) := by
  simp
  -- ⊢ tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫ (tensor_μ C (M.X, N.X) (M.X,  …
  slice_lhs 2 3 => rw [← Category.id_comp P.mul, tensor_comp]
  -- ⊢ tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫ ((tensor_μ C (M.X, N.X) (M.X, …
  slice_lhs 3 4 => rw [associator_naturality]
  -- ⊢ tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫ (tensor_μ C (M.X, N.X) (M.X,  …
  slice_rhs 3 4 => rw [← Category.id_comp M.mul, tensor_comp]
  -- ⊢ tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫ (tensor_μ C (M.X, N.X) (M.X,  …
  slice_lhs 1 3 => rw [associator_monoidal]
  -- ⊢ (((α_ M.X N.X P.X).hom ⊗ (α_ M.X N.X P.X).hom) ≫ tensor_μ C (M.X, N.X ⊗ P.X) …
  simp only [Category.assoc]
  -- 🎉 no goals
#align Mon_.mul_associator Mon_.mul_associator

theorem mul_leftUnitor {M : Mon_ C} :
    (tensor_μ C (𝟙_ C, M.X) (𝟙_ C, M.X) ≫ ((λ_ (𝟙_ C)).hom ⊗ M.mul)) ≫ (λ_ M.X).hom =
      ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ M.mul := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp M.mul, tensor_comp]
  -- ⊢ (tensor_μ C (𝟙_ C, M.X) (𝟙_ C, M.X) ≫ ((λ_ (𝟙_ C)).hom ⊗ 𝟙 (M.X ⊗ M.X)) ≫ (𝟙 …
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  -- ⊢ tensor_μ C (𝟙_ C, M.X) (𝟙_ C, M.X) ≫ ((λ_ (𝟙_ C)).hom ⊗ 𝟙 (M.X ⊗ M.X)) ≫ (λ_ …
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  -- ⊢ ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ M.mul = ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ 𝟙 (M …
  simp only [Category.assoc, Category.id_comp]
  -- 🎉 no goals
#align Mon_.mul_left_unitor Mon_.mul_leftUnitor

theorem mul_rightUnitor {M : Mon_ C} :
    (tensor_μ C (M.X, 𝟙_ C) (M.X, 𝟙_ C) ≫ (M.mul ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M.X).hom =
      ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ M.mul := by
  rw [← Category.id_comp M.mul, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  -- ⊢ (tensor_μ C (M.X, 𝟙_ C) (M.X, 𝟙_ C) ≫ (𝟙 (M.X ⊗ M.X) ⊗ (λ_ (𝟙_ C)).hom) ≫ (M …
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  -- ⊢ tensor_μ C (M.X, 𝟙_ C) (M.X, 𝟙_ C) ≫ (𝟙 (M.X ⊗ M.X) ⊗ (λ_ (𝟙_ C)).hom) ≫ (ρ_ …
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  -- ⊢ ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ M.mul = ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ 𝟙 (M …
  simp only [Category.assoc, Category.id_comp]
  -- 🎉 no goals
#align Mon_.mul_right_unitor Mon_.mul_rightUnitor

instance monMonoidal : MonoidalCategory (Mon_ C) := .ofTensorHom
  (tensorObj := fun M N ↦
    { X := M.X ⊗ N.X
      one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)
      mul := tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
      one_mul := Mon_tensor_one_mul M N
      mul_one := Mon_tensor_mul_one M N
      mul_assoc := Mon_tensor_mul_assoc M N })
  (tensorHom := fun f g ↦
    { hom := f.hom ⊗ g.hom
      one_hom := by
        dsimp
        -- ⊢ ((λ_ (𝟙_ C)).inv ≫ (X₁✝.one ⊗ X₂✝.one)) ≫ (f.hom ⊗ g.hom) = (λ_ (𝟙_ C)).inv  …
        slice_lhs 2 3 => rw [← tensor_comp, Hom.one_hom f, Hom.one_hom g]
        -- 🎉 no goals
      mul_hom := by
        dsimp
        -- ⊢ (tensor_μ C (X₁✝.X, X₂✝.X) (X₁✝.X, X₂✝.X) ≫ (X₁✝.mul ⊗ X₂✝.mul)) ≫ (f.hom ⊗  …
        slice_rhs 1 2 => rw [tensor_μ_natural]
        -- ⊢ (tensor_μ C (X₁✝.X, X₂✝.X) (X₁✝.X, X₂✝.X) ≫ (X₁✝.mul ⊗ X₂✝.mul)) ≫ (f.hom ⊗  …
        slice_lhs 2 3 => rw [← tensor_comp, Hom.mul_hom f, Hom.mul_hom g, tensor_comp]
        -- ⊢ tensor_μ C (X₁✝.X, X₂✝.X) (X₁✝.X, X₂✝.X) ≫ ((f.hom ⊗ f.hom) ⊗ g.hom ⊗ g.hom) …
        simp only [Category.assoc] })
        -- 🎉 no goals
  (tensor_id := by intros; ext; apply tensor_id)
                   -- ⊢ (fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) (𝟙 X₁✝) (𝟙 X₂✝) = 𝟙 ((fun  …
                           -- ⊢ ((fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) (𝟙 X₁✝) (𝟙 X₂✝)).hom = (𝟙 …
                                -- 🎉 no goals
  (tensor_comp := by intros; ext; apply tensor_comp)
                     -- ⊢ (fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) (f₁✝ ≫ g₁✝) (f₂✝ ≫ g₂✝) =  …
                             -- ⊢ ((fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) (f₁✝ ≫ g₁✝) (f₂✝ ≫ g₂✝)). …
                                  -- 🎉 no goals
  (tensorUnit' := trivial C)
  (associator := fun M N P ↦ isoOfIso (α_ M.X N.X P.X) one_associator mul_associator)
  (associator_naturality := by intros; ext; dsimp; apply associator_naturality)
                               -- ⊢ (fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) ((fun {X₁ Y₁ X₂ Y₂} f g => …
                                       -- ⊢ ((fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) ((fun {X₁ Y₁ X₂ Y₂} f g = …
                                            -- ⊢ ((f₁✝.hom ⊗ f₂✝.hom) ⊗ f₃✝.hom) ≫ (isoOfIso (α_ Y₁✝.X Y₂✝.X Y₃✝.X) (_ : ((λ_ …
                                                   -- 🎉 no goals
  (leftUnitor := fun M ↦ isoOfIso (λ_ M.X) one_leftUnitor mul_leftUnitor)
  (leftUnitor_naturality := by intros; ext; dsimp; apply leftUnitor_naturality)
                               -- ⊢ (fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) (𝟙 (trivial C)) f✝ ≫ ((fun …
                                       -- ⊢ ((fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) (𝟙 (trivial C)) f✝ ≫ ((fu …
                                            -- ⊢ (𝟙 (𝟙_ C) ⊗ f✝.hom) ≫ (isoOfIso (λ_ Y✝.X) (_ : ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C)  …
                                                   -- 🎉 no goals
  (rightUnitor := fun M ↦ isoOfIso (ρ_ M.X) one_rightUnitor mul_rightUnitor)
  (rightUnitor_naturality := by intros; ext; dsimp; apply rightUnitor_naturality)
                                -- ⊢ (fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) f✝ (𝟙 (trivial C)) ≫ ((fun …
                                        -- ⊢ ((fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) f✝ (𝟙 (trivial C)) ≫ ((fu …
                                             -- ⊢ (f✝.hom ⊗ 𝟙 (𝟙_ C)) ≫ (isoOfIso (ρ_ Y✝.X) (_ : ((λ_ (𝟙_ C)).inv ≫ (Y✝.one ⊗  …
                                                    -- 🎉 no goals
  (pentagon := by intros; ext; dsimp; apply pentagon)
                  -- ⊢ (fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) ((fun M N P => isoOfIso (α …
                          -- ⊢ ((fun {X₁ Y₁ X₂ Y₂} f g => Hom.mk (f.hom ⊗ g.hom)) ((fun M N P => isoOfIso ( …
                               -- ⊢ ((isoOfIso (α_ W✝.X X✝.X Y✝.X) (_ : ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (W …
                                      -- 🎉 no goals
  (triangle := by intros; ext; dsimp; apply triangle)
                  -- ⊢ ((fun M N P => isoOfIso (α_ M.X N.X P.X) (_ : ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C) …
                          -- ⊢ (((fun M N P => isoOfIso (α_ M.X N.X P.X) (_ : ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C …
                               -- ⊢ (isoOfIso (α_ X✝.X (𝟙_ C) Y✝.X) (_ : ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ ( …
                                      -- 🎉 no goals
#align Mon_.Mon_monoidal Mon_.monMonoidal

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
* Show that when `C` is braided, the forgetful functor `Mon_ C ⥤ C` is monoidal.
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor `map_Mon F : Mon_ C ⥤ Mon_ D`
  is lax monoidal.
-/
