/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Algebra.PUnitInstances.Algebra

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class Mon_ (X : C) where
  /-- The unit morphism of a monoid object. -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  mul : X ⊗ X ⟶ X
  one_mul' : (one ▷ X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one' : (X ◁ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc' : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

namespace Mon_

@[inherit_doc] scoped notation "μ" => Mon_.mul
@[inherit_doc] scoped notation "η" => Mon_.one

@[reassoc, simp]
theorem one_mul (X : C) [Mon_ X] : (η ▷ X) ≫ μ = (λ_ X).hom := one_mul'

@[reassoc, simp]
theorem mul_one (X : C) [Mon_ X] : (X ◁ η) ≫ μ = (ρ_ X).hom := mul_one'

-- We prove a more general `@[simp]` lemma below.
@[reassoc (attr := simp)]
theorem mul_assoc (X : C) [Mon_ X] : (μ ▷ X) ≫ μ = (α_ X X X).hom ≫ (X ◁ μ) ≫ μ := mul_assoc'

/-- The trivial monoid object. We later show this is initial in `Mon_Cat C`.
-/
@[simps]
instance trivial (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : Mon_ (𝟙_ C) where
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc' := by coherence
  mul_one' := by coherence

instance : Inhabited (Mon_ (𝟙_ C)) :=
  ⟨trivial C⟩

variable {M : C}
variable [Mon_ M]

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M) : (η ⊗ f) ≫ μ = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, one_mul, leftUnitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M) : (f ⊗ η) ≫ μ = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, mul_one, rightUnitor_naturality]

theorem mul_assoc_flip :
    (M ◁ μ) ≫ μ = (α_ M M M).inv ≫ (μ ▷ M) ≫ μ := by simp

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : C) [Mon_ M] [Mon_ N] where
  hom : M ⟶ N
  one_hom : η ≫ hom = η := by aesop_cat
  mul_hom : μ ≫ hom = (hom ⊗ hom) ≫ μ := by aesop_cat

class HomClass {M N : C} [Mon_ M] [Mon_ N] (f : M ⟶ N) : Prop where
  one_hom : η ≫ f = η
  mul_hom : μ ≫ f = (f ⊗ f) ≫ μ

attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def Hom.id (M : C) [Mon_ M] : Hom M M where
  hom := 𝟙 M

instance homInhabited (M : C) [Mon_ M] : Inhabited (Hom M M) :=
  ⟨.id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def Hom.comp {M N O : C} [Mon_ M] [Mon_ N] [Mon_ O] (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

@[ext]
structure Iso (M N : C) [Mon_ M] [Mon_ N] where
  hom : Hom M N
  inv : Hom N M
  hom_inv_id : hom.hom ≫ inv.hom = 𝟙 M := by aesop_cat
  inv_hom_id : inv.hom ≫ hom.hom = 𝟙 N := by aesop_cat

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id

end Mon_

structure Mon_Cat (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] where
  X : C
  [isMon_ : Mon_ X]

namespace Mon_Cat

open Mon_

attribute [instance] Mon_Cat.isMon_

instance : Inhabited (Mon_Cat C) :=
  ⟨⟨𝟙_ C⟩⟩

initialize_simps_projections Mon_Cat (-isMon_)

instance : Category.{v₁} (Mon_Cat C) where
  Hom M N := Mon_.Hom M.X N.X
  id M := Mon_.Hom.id M.X
  comp f g := Mon_.Hom.comp f g

def mkHom {X Y : C} [Mon_ X] [Mon_ Y] (f : Mon_.Hom X Y) :
    mk X ⟶ mk Y :=
  f

@[simp]
theorem mkHom_hom {X Y : C} [Mon_ X] [Mon_ Y] (f : Hom X Y) : (mkHom f).hom = f.hom :=
  rfl

-- Porting note: added, as `Hom.ext` does not apply to a morphism.
@[ext]
lemma Hom.ext' {X Y : Mon_Cat C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext _ _ w

@[simp]
theorem id_hom' {M : Mon_Cat C} : (𝟙 M : Hom M.X M.X).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon_Cat C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
def mkIso {X Y : C} [Mon_ X] [Mon_ Y] (f : Mon_.Iso X Y) :
    mk X ≅ mk Y where
  hom := f.hom
  inv := f.inv

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_Cat C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : C} [Mon_ A] [Mon_ B] (f : Hom A B) [e : IsIso ((forget C).map (Mon_Cat.mkHom f))] :
    IsIso f.hom :=
  e

instance {A B : Mon_Cat C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] :
    IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

instance uniqueHomFromTrivial (A : Mon_Cat C) : Unique (Mon_Cat.mk (𝟙_ C) ⟶ A) where
  default :=
  { hom := η
    mul_hom := by dsimp; simp [Mon_.one_mul, unitors_equal] }
  uniq f := by
    ext
    dsimp only [trivial_mul]
    rw [← Category.id_comp f.hom, ← trivial_one, f.one_hom]

open CategoryTheory.Limits

instance : HasInitial (Mon_Cat C) :=
  hasInitial_of_unique (mk (𝟙_ C))

end Mon_Cat

namespace Mon_

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : C} [Mon_ M] [Mon_ N] (f : M ≅ N) (one_f : η ≫ f.hom = η)
    (mul_f : μ ≫ f.hom = (f.hom ⊗ f.hom) ≫ μ) :
    Iso M N where
  hom := { hom := f.hom }
  inv := {
    hom := f.inv
    one_hom := by rw [← one_f]; simp
    mul_hom := by
      rw [← cancel_mono f.hom]
      slice_rhs 2 3 => rw [mul_f]
      simp }

end Mon_

open Mon_

namespace CategoryTheory.LaxMonoidalFunctor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

@[simps!?]
instance (F : LaxMonoidalFunctor C D) {A : C} [Mon_ A] : Mon_ (F.obj A) where
  one := F.ε ≫ F.map η
  mul := F.μ _ _ ≫ F.map μ
  one_mul' := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, left_unitality]
    slice_lhs 3 4 => rw [← F.toFunctor.map_comp, Mon_.one_mul]
  mul_one' := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
      right_unitality]
    slice_lhs 3 4 => rw [← F.toFunctor.map_comp, Mon_.mul_one]
  mul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.toFunctor.map_comp, Mon_.mul_assoc]
    simp

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMon A)
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_Cat C ⥤ Mon_ D`.
-/
@[simps]
def mapMon (F : LaxMonoidalFunctor C D) : Mon_Cat C ⥤ Mon_Cat D where
  obj A := Mon_Cat.mk (F.obj A.X)
  map {A B} f := Mon_Cat.mkHom
    { hom := F.map f.hom
      one_hom := by dsimp; rw [Category.assoc, ← F.toFunctor.map_comp, f.one_hom]
      mul_hom := by
        dsimp
        rw [Category.assoc, F.μ_natural_assoc, ← F.toFunctor.map_comp, ← F.toFunctor.map_comp,
          f.mul_hom] }

variable (C D)

/-- `mapMon` is functorial in the lax monoidal functor. -/
@[simps] -- Porting note: added this, not sure how it worked previously without.
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_Cat C ⥤ Mon_Cat D where
  obj := mapMon
  map α := { app := fun A => { hom := α.app A.X } }

@[simp]
theorem mapMon_obj_one (F : LaxMonoidalFunctor C D)
    (A : Mon_Cat C) : η = F.ε ≫ F.map (η : _ ⟶ A.X) := by
  simp only [instMon_Obj_one]

end CategoryTheory.LaxMonoidalFunctor

namespace Mon_Cat

open CategoryTheory.LaxMonoidalFunctor

namespace EquivLaxMonoidalFunctorPUnit

variable (C)

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_Cat C where
  obj F := (F.mapMon : Mon_Cat _ ⥤ Mon_Cat C).obj (.mk (𝟙_ (Discrete PUnit)))
  map α := ((mapMonFunctor (Discrete PUnit) C).map α).app _

@[simps]
def monToLaxMonoidalObj (A : C) [Mon_ A] : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj := fun _ => A
  map := fun _ => 𝟙 _
  ε := η
  «μ» := fun _ _ => μ

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : Mon_Cat C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A := monToLaxMonoidalObj _ A.X
  map f :=
  { app := fun _ => f.hom }

-- attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
--   CategoryTheory.Discrete.discreteCases

attribute [local simp] eqToIso_map

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F =>
      MonoidalNatIso.ofComponents (fun _ => F.toFunctor.mapIso (eqToIso (by ext))))

attribute [-simp] monToLaxMonoidalObj_toFunctor_obj in
/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_Cat C) :=
  NatIso.ofComponents (fun F => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } })

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_Cat C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end Mon_Cat

namespace Mon_

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the multiplication on the tensor product `M ⊗ N` is defined in the obvious way:
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


-- variable {C}

-- The proofs that associators and unitors preserve monoid units don't require braiding.
theorem one_associator {M N P : C} [Mon_ M] [Mon_ N] [Mon_ P] :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (η ⊗ η) ⊗ η)) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ C)).inv ≫ (η ⊗ (λ_ (𝟙_ C)).inv ≫ (η ⊗ η)) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), tensor_comp]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, tensor_comp]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp

theorem one_leftUnitor {M : C} [Mon_ M] :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ η)) ≫ (λ_ M).hom = η := by
  simp

theorem one_rightUnitor {M : C} [Mon_ M] :
    ((λ_ (𝟙_ C)).inv ≫ (η ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

theorem Mon_tensor_one_mul (M N : C) [Mon_ M] [Mon_ N] :
    (((λ_ (𝟙_ C)).inv ≫ (η ⊗ η)) ▷ (M ⊗ N)) ≫
        tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ) =
      (λ_ (M ⊗ N : C)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensor_μ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul, one_mul]
  symm
  exact tensor_left_unitality C M N

theorem Mon_tensor_mul_one (M N : C) [Mon_ M] [Mon_ N] :
    (M ⊗ N : C) ◁ ((λ_ (𝟙_ C)).inv ≫ (η ⊗ η)) ≫
        tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ) =
      (ρ_ (M ⊗ N : C)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensor_μ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one, mul_one]
  symm
  exact tensor_right_unitality C M N

theorem Mon_tensor_mul_assoc (M N : C) [Mon_ M] [Mon_ N] :
    ((tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ)) ▷ (M ⊗ N)) ≫
        tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ))) ≫
          tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ) := by
  simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensor_μ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc, mul_assoc, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensor_μ_natural_right]
  simp

theorem mul_associator {M N P : C} [Mon_ M] [Mon_ N] [Mon_ P] :
    (tensor_μ C (M ⊗ N, P) (M ⊗ N, P) ≫
          (tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ) ⊗ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ (α_ M N P).hom) ≫
        tensor_μ C (M, N ⊗ P) (M, N ⊗ P) ≫
          (μ ⊗ tensor_μ C (N, P) (N, P) ≫ (μ ⊗ μ)) := by
  simp only [tensor_obj, prodMonoidal_tensorObj, Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp (μ : _ ⟶ P), tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

theorem mul_leftUnitor {M : C} [Mon_ M] :
    (tensor_μ C (𝟙_ C, M) (𝟙_ C, M) ≫ ((λ_ (𝟙_ C)).hom ⊗ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

theorem mul_rightUnitor {M : C} [Mon_ M] :
    (tensor_μ C (M, 𝟙_ C) (M, 𝟙_ C) ≫ (μ ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

@[simps]
instance {M N : C} [Mon_ M] [Mon_ N] : Mon_ (M ⊗ N : C) where
  one := (λ_ (𝟙_ C)).inv ≫ (η ⊗ η)
  mul := tensor_μ C (M, N) (M, N) ≫ (μ ⊗ μ)
  one_mul' := Mon_tensor_one_mul M N
  mul_one' := Mon_tensor_mul_one M N
  mul_assoc' := Mon_tensor_mul_assoc M N

@[simps]
def tensorHom {X₁ Y₁ X₂ Y₂ : C} [Mon_ X₁] [Mon_ Y₁] [Mon_ X₂] [Mon_ Y₂]
    (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) :
     Hom (X₁ ⊗ X₂ : C) (Y₁ ⊗ Y₂) :=
  { hom := f.hom ⊗ g.hom
    one_hom := by
      dsimp
      slice_lhs 2 3 => rw [← tensor_comp, f.one_hom, g.one_hom]
    mul_hom := by
      dsimp
      slice_rhs 1 2 => rw [tensor_μ_natural]
      slice_lhs 2 3 => rw [← tensor_comp, f.mul_hom, g.mul_hom, tensor_comp]
      simp only [Category.assoc] }

@[simps!]
def whiskerLeft (X : C) [Mon_ X] {Y Z : C} [Mon_ Y] [Mon_ Z] (f : Hom Y Z) :
    Hom (X ⊗ Y : C) (X ⊗ Z) :=
  tensorHom (.id X) f

@[simps!]
def whiskerRight {X Y : C} [Mon_ X] [Mon_ Y] (f : Hom X Y) (Z : C) [Mon_ Z] :
    Hom (X ⊗ Z : C) (Y ⊗ Z) :=
  tensorHom f (.id Z)

@[simps!]
def associator (X Y Z : C) [Mon_ X] [Mon_ Y] [Mon_ Z] :
    Iso ((X ⊗ Y) ⊗ Z : C) (X ⊗ (Y ⊗ Z)) :=
  mkIso (α_ (X : C) Y Z) one_associator mul_associator

@[simps!]
def leftUnitor (X : C) [Mon_ X] :
    Iso (𝟙_ C ⊗ X : C) X :=
  mkIso (λ_ X) one_leftUnitor mul_leftUnitor

@[simps!]
def rightUnitor (X : C) [Mon_ X] :
    Iso (X ⊗ 𝟙_ C : C) X :=
  mkIso (ρ_ X) one_rightUnitor mul_rightUnitor

theorem one_braiding (X Y : C) [Mon_ X] [Mon_ Y] : η ≫ (β_ X Y).hom = η := by
  -- simp only [monMonoidalStruct_tensorObj_X, tensor_one, Category.assoc,
  --   BraidedCategory.braiding_naturality, braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  simp only [instTensorObj_one, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  coherence

end BraidedCategory

end Mon_

namespace Mon_Cat

section BraidedCategory

variable [BraidedCategory C]

@[simps!]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_Cat C) where
  tensorObj := fun M N ↦ Mon_Cat.mk (M.X ⊗ N.X)
  tensorHom := tensorHom
  whiskerRight := fun f Y => whiskerRight f Y.X
  whiskerLeft := fun X _ _ g => whiskerLeft X.X g
  tensorUnit := Mon_Cat.mk (𝟙_ C)
  associator := fun M N P ↦ Mon_Cat.mkIso <| associator M.X N.X P.X
  leftUnitor := fun M ↦ Mon_Cat.mkIso <| leftUnitor M.X
  rightUnitor := fun M ↦ Mon_Cat.mkIso <| rightUnitor M.X

instance monMonoidal : MonoidalCategory (Mon_Cat C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

variable (C)

/-- The forgetful functor from `Mon_Cat C` to `C` is monoidal when `C` is braided monoidal. -/
@[simps!]
def forgetMonoidal : MonoidalFunctor (Mon_Cat C) C :=
  { forget C with
    ε := 𝟙 _
    «μ» := fun X Y => 𝟙 _ }

-- @[simp]
theorem forgetMonoidal_toFunctor : (forgetMonoidal C).toFunctor = forget C := rfl
@[simp] theorem forgetMonoidal_ε : (forgetMonoidal C).ε = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forgetMonoidal_μ (X Y : Mon_Cat C) : (forgetMonoidal C).μ X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory

end Mon_Cat

/-!
We next show that if `C` is symmetric, then `Mon_Cat C` is braided, and indeed symmetric.

Note that `Mon_Cat C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

namespace Mon_

theorem mul_braiding (X Y : C) [Mon_ X] [Mon_ Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom ⊗ (β_ X Y).hom) ≫ μ := by
  dsimp [tensor_μ]
  simp only [tensor_μ, Category.assoc,
    BraidedCategory.braiding_naturality, BraidedCategory.braiding_tensor_right,
    BraidedCategory.braiding_tensor_left, comp_whiskerRight, whisker_assoc,
    MonoidalCategory.whiskerLeft_comp, pentagon_assoc, pentagon_inv_hom_hom_hom_inv_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
    pentagon_inv_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [CategoryTheory.Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

instance : SymmetricCategory (Mon_Cat C) where
  braiding := fun X Y =>
    Mon_Cat.mkIso <| mkIso (β_ X.X Y.X) (one_braiding X.X Y.X) (mul_braiding X.X Y.X)
  symmetry := fun X Y => by
    ext
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]

end Mon_

end SymmetricCategory

/-!
Projects:
* Check that `Mon_Cat MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `MonCat` first,
  available in mathlib3#3463)
* More generally, check that `Mon_Cat (Mon_Cat C) ≌ CommMon_Cat C` when `C` is braided.
* Check that `Mon_Cat TopCat ≌ [bundled topological monoids]`.
* Check that `Mon_Cat AddCommGrp ≌ RingCat`.
  (We've already got `Mon_Cat (ModuleCat R) ≌ AlgebraCat R`,
  in `Mathlib.CategoryTheory.Monoidal.Internal.Module`.)
* Can you transport this monoidal structure to `RingCat` or `AlgebraCat R`?
  How does it compare to the "native" one?
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor
  `map_Mon F : Mon_Cat C ⥤ Mon_Cat D` is lax monoidal.
-/
