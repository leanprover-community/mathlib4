/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class Mon_Class (X : C) where
  /-- The unit morphism of a monoid object. -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  mul : X ⊗ X ⟶ X
  /- For the names of the conditions below, the unprimed names are reserved for the version where
  the argument `X` is explicit. -/
  one_mul' : one ▷ X ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one' : X ◁ one ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc' : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

namespace Mon_Class

@[inherit_doc] scoped notation "μ" => Mon_Class.mul
@[inherit_doc] scoped notation "μ["M"]" => Mon_Class.mul (X := M)
@[inherit_doc] scoped notation "η" => Mon_Class.one
@[inherit_doc] scoped notation "η["M"]" => Mon_Class.one (X := M)

/- The simp attribute is reserved for the unprimed versions. -/
attribute [reassoc] one_mul' mul_one' mul_assoc'

@[reassoc (attr := simp)]
theorem one_mul (X : C) [Mon_Class X] : η ▷ X ≫ μ = (λ_ X).hom := one_mul'

@[reassoc (attr := simp)]
theorem mul_one (X : C) [Mon_Class X] : X ◁ η ≫ μ = (ρ_ X).hom := mul_one'

@[reassoc (attr := simp)]
theorem mul_assoc (X : C) [Mon_Class X] : μ ▷ X ≫ μ = (α_ X X X).hom ≫ X ◁ μ ≫ μ := mul_assoc'

@[ext]
theorem ext {X : C} (h₁ h₂ : Mon_Class X) (H : h₁.mul = h₂.mul) : h₁ = h₂ := by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (λ_ _).inv ≫ (h₁.one ⊗ h₂.one) ≫ h₁.mul
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

end Mon_Class

open scoped Mon_Class

variable {M N : C} [Mon_Class M] [Mon_Class N]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsMon_Hom (f : M ⟶ N) : Prop where
  one_hom (f) : η ≫ f = η := by aesop_cat
  mul_hom (f) : μ ≫ f = (f ⊗ f) ≫ μ := by aesop_cat

attribute [reassoc (attr := simp)] IsMon_Hom.one_hom IsMon_Hom.mul_hom

variable (C)

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  /-- The unit morphism of the monoid object -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object -/
  mul : X ⊗ X ⟶ X
  one_mul : (one ▷ X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat

attribute [reassoc] Mon_.one_mul Mon_.mul_one

attribute [simp] Mon_.one_mul Mon_.mul_one

-- We prove a more general `@[simp]` lemma below.
attribute [reassoc (attr := simp)] Mon_.mul_assoc

namespace Mon_

variable {C}

/-- Construct an object of `Mon_ C` from an object `X : C` and `Mon_Class X` instance. -/
abbrev mk' (X : C) [Mon_Class X] : Mon_ C where
  X := X
  one := η
  mul := μ

instance X.instMon_Class {M : Mon_ C} : Mon_Class M.X where
  one := M.one
  mul := M.mul
  one_mul' := M.one_mul
  mul_one' := M.mul_one
  mul_assoc' := M.mul_assoc

variable (C)

/-- The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps]
def trivial : Mon_ C where
  X := 𝟙_ C
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩

variable {C}
variable {M : Mon_ C}

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, M.one_mul, leftUnitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, M.mul_one, rightUnitor_naturality]

theorem mul_assoc_flip :
    (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul := by simp

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mon_ C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  one_hom : M.one ≫ hom = N.one := by aesop_cat
  mul_hom : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul := by aesop_cat

/-- Construct a morphism `M ⟶ N` of `Mon_ C` from a map `f : M ⟶ N` and a `IsMon_Hom f` instance. -/
abbrev Hom.mk' {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    Hom (.mk' M) (.mk' N) := .mk f

attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : Hom M M where
  hom := 𝟙 M.X

instance homInhabited (M : Mon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Mon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Mon_ C} (f : M ⟶ N) : IsMon_Hom f.hom := ⟨f.2, f.3⟩

@[ext]
lemma ext {X Y : Mon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : Mon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
    (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat) : M ≅ N where
  hom := { hom := f.hom }
  inv :=
  { hom := f.inv
    one_hom := by rw [← one_f]; simp
    mul_hom := by
      rw [← cancel_mono f.hom]
      slice_rhs 2 3 => rw [mul_f]
      simp }

@[simps]
instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A) where
  default :=
  { hom := A.one
    mul_hom := by simp [A.one_mul, unitors_equal] }
  uniq f := by
    ext
    simp only [trivial_X]
    rw [← Category.id_comp f.hom]
    erw [f.one_hom]

open CategoryTheory.Limits

instance : HasInitial (Mon_ C) :=
  hasInitial_of_unique (trivial C)

end Mon_

namespace CategoryTheory.Functor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] (F : C ⥤ D)

section LaxMonoidal
variable [F.LaxMonoidal] (X Y : C) [Mon_Class X] [Mon_Class Y] (f : X ⟶ Y) [IsMon_Hom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev obj.instMon_Class : Mon_Class (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul' := by simp [← F.map_comp]
  mul_one' := by simp [← F.map_comp]
  mul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, Mon_Class.mul_assoc]
    simp

attribute [local instance] obj.instMon_Class

@[reassoc, simp] lemma obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[reassoc, simp] lemma obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

instance map.instIsMon_Hom : IsMon_Hom (F.map f) where
  one_hom := by simp [← map_comp]
  mul_hom := by simp [← map_comp]

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMon A)
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
@[simps]
def mapMon (F : C ⥤ D) [F.LaxMonoidal] : Mon_ C ⥤ Mon_ D where
  -- TODO: The following could be, but it leads to weird `erw`s later down the file
  -- obj A := .mk' (F.obj A.X)
  obj A :=
    { X := F.obj A.X
      one := ε F ≫ F.map A.one
      mul := «μ» F _ _ ≫ F.map A.mul
      one_mul := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          LaxMonoidal.left_unitality]
        slice_lhs 3 4 => rw [← F.map_comp, A.one_mul]
      mul_one := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
          LaxMonoidal.right_unitality]
        slice_lhs 3 4 => rw [← F.map_comp, A.mul_one]
      mul_assoc := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
        slice_lhs 3 4 => rw [← F.map_comp, A.mul_assoc]
        simp }
  map f := .mk' (F.map f.hom)

protected instance Faithful.mapMon [F.Faithful] : F.mapMon.Faithful where
  map_injective {_X _Y} _f _g hfg := Mon_.Hom.ext <| map_injective congr(($hfg).hom)

end LaxMonoidal

section Monoidal
variable [F.Monoidal]

attribute [local instance] obj.instMon_Class

protected instance Full.mapMon [F.Full] [F.Faithful] : F.mapMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      one_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.one_hom
      mul_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.mul_hom
    }, Mon_.Hom.ext hg⟩

instance FullyFaithful.isMon_Hom_preimage (hF : F.FullyFaithful) {X Y : C}
    [Mon_Class X] [Mon_Class Y] (f : F.obj X ⟶ F.obj Y) [IsMon_Hom f] :
    IsMon_Hom (hF.preimage f) where
  one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : Mon C ⥤ Mon D` is fully
faithful too. -/
protected def FullyFaithful.mapMon (hF : F.FullyFaithful) : F.mapMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

end Monoidal

variable (C D)

/-- `mapMon` is functorial in the lax monoidal functor. -/
@[simps] -- Porting note: added this, not sure how it worked previously without.
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_ C ⥤ Mon_ D where
  obj F := F.mapMon
  map α := { app := fun A => { hom := α.hom.app A.X } }
  map_comp _ _ := rfl



end CategoryTheory.Functor

namespace Mon_

namespace EquivLaxMonoidalFunctorPUnit

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_ C where
  obj F := (F.mapMon : Mon_ _ ⥤ Mon_ C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

variable {C}

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def monToLaxMonoidalObj (A : Mon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : Mon_ C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε' := A.one
  μ' := fun _ _ => A.mul

@[simp]
lemma monToLaxMonoidalObj_ε (A : Mon_ C) :
    ε (monToLaxMonoidalObj A) = A.one := rfl

@[simp]
lemma monToLaxMonoidalObj_μ (A : Mon_ C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = A.mul := rfl

variable (C)
/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : Mon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))

/-- Implementation of `Mon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents fun F ↦ mkIso (Iso.refl _)

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
The strength `tensorμ` of the tensor product functor has been defined in
`Mathlib.CategoryTheory.Monoidal.Braided`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapMon`,
but we chose to give a more explicit definition directly in terms of `tensorμ`.

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

theorem one_leftUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ M.one)) ≫ (λ_ M.X).hom = M.one := by
  simp

theorem one_rightUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M.X).hom = M.one := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

theorem Mon_tensor_one_mul (M N : Mon_ C) :
    (((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ▷ (M.X ⊗ N.X)) ≫
        tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) =
      (λ_ (M.X ⊗ N.X)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul M, one_mul N]
  symm
  exact tensor_left_unitality M.X N.X

theorem Mon_tensor_mul_one (M N : Mon_ C) :
    (M.X ⊗ N.X) ◁ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
        tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) =
      (ρ_ (M.X ⊗ N.X)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one M, mul_one N]
  symm
  exact tensor_right_unitality M.X N.X

theorem Mon_tensor_mul_assoc (M N : Mon_ C) :
    ((tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul)) ▷ (M.X ⊗ N.X)) ≫
        tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) =
      (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫
        ((M.X ⊗ N.X) ◁ (tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul))) ≫
          tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) := by
  simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc M, mul_assoc N, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

theorem mul_associator {M N P : Mon_ C} :
    (tensorμ (M.X ⊗ N.X) P.X (M.X ⊗ N.X) P.X ≫
          (tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) ⊗ P.mul)) ≫
        (α_ M.X N.X P.X).hom =
      ((α_ M.X N.X P.X).hom ⊗ (α_ M.X N.X P.X).hom) ≫
        tensorμ M.X (N.X ⊗ P.X) M.X (N.X ⊗ P.X) ≫
          (M.mul ⊗ tensorμ N.X P.X N.X P.X ≫ (N.mul ⊗ P.mul)) := by
  simp only [tensor_obj, prodMonoidal_tensorObj, Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp P.mul, tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp M.mul, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

theorem mul_leftUnitor {M : Mon_ C} :
    (tensorμ (𝟙_ C) M.X (𝟙_ C) M.X ≫ ((λ_ (𝟙_ C)).hom ⊗ M.mul)) ≫ (λ_ M.X).hom =
      ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ M.mul := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp M.mul, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

theorem mul_rightUnitor {M : Mon_ C} :
    (tensorμ M.X (𝟙_ C) M.X (𝟙_ C) ≫ (M.mul ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M.X).hom =
      ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ M.mul := by
  rw [← Category.id_comp M.mul, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

@[simps tensorObj_X tensorHom_hom]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_ C) :=
  let tensorObj (M N : Mon_ C) : Mon_ C :=
    { X := M.X ⊗ N.X
      one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)
      mul := tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul)
      one_mul := Mon_tensor_one_mul M N
      mul_one := Mon_tensor_mul_one M N
      mul_assoc := Mon_tensor_mul_assoc M N }
  let tensorHom {X₁ Y₁ X₂ Y₂ : Mon_ C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
      tensorObj _ _ ⟶ tensorObj _ _ :=
    { hom := f.hom ⊗ g.hom
      one_hom := by
        dsimp [tensorObj]
        slice_lhs 2 3 => rw [← tensor_comp, Hom.one_hom f, Hom.one_hom g]
      mul_hom := by
        dsimp [tensorObj]
        slice_rhs 1 2 => rw [tensorμ_natural]
        slice_lhs 2 3 => rw [← tensor_comp, Hom.mul_hom f, Hom.mul_hom g, tensor_comp]
        simp only [Category.assoc] }
  { tensorObj := tensorObj
    tensorHom := tensorHom
    whiskerRight := fun f Y => tensorHom f (𝟙 Y)
    whiskerLeft := fun X _ _ g => tensorHom (𝟙 X) g
    tensorUnit := trivial C
    associator := fun M N P ↦ mkIso (α_ M.X N.X P.X) one_associator mul_associator
    leftUnitor := fun M ↦ mkIso (λ_ M.X) one_leftUnitor mul_leftUnitor
    rightUnitor := fun M ↦ mkIso (ρ_ M.X) one_rightUnitor mul_rightUnitor }

@[simp]
theorem tensorUnit_X : (𝟙_ (Mon_ C)).X = 𝟙_ C := rfl

@[simp]
theorem tensorUnit_one : (𝟙_ (Mon_ C)).one = 𝟙 (𝟙_ C) := rfl

@[simp]
theorem tensorUnit_mul : (𝟙_ (Mon_ C)).mul = (λ_ (𝟙_ C)).hom := rfl

@[simp]
theorem tensorObj_one (X Y : Mon_ C) : (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl

@[simp]
theorem tensorObj_mul (X Y : Mon_ C) :
    (X ⊗ Y).mul = tensorμ X.X Y.X X.X Y.X ≫ (X.mul ⊗ Y.mul) := rfl

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

@[simp]
theorem tensor_one (M N : Mon_ C) : (M ⊗ N).one = (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) := rfl

@[simp]
theorem tensor_mul (M N : Mon_ C) : (M ⊗ N).mul =
    tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) := rfl

instance monMonoidal : MonoidalCategory (Mon_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

@[simps!]
instance {M N : C} [Mon_Class M] [Mon_Class N] : Mon_Class (M ⊗ N) :=
  inferInstanceAs <| Mon_Class (Mon_.mk' M ⊗ Mon_.mk' N).X

variable (C)

/-- The forgetful functor from `Mon_ C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

@[simp] theorem forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Mon_ C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Mon_ C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

variable {C}

theorem one_braiding {X Y : Mon_ C} : (X ⊗ Y).one ≫ (β_ X.X Y.X).hom = (Y ⊗ X).one := by
  simp only [monMonoidalStruct_tensorObj_X, tensor_one, Category.assoc,
    BraidedCategory.braiding_naturality, braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

/-!
We next show that if `C` is symmetric, then `Mon_ C` is braided, and indeed symmetric.

Note that `Mon_ C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

theorem mul_braiding {X Y : Mon_ C} :
    (X ⊗ Y).mul ≫ (β_ X.X Y.X).hom = ((β_ X.X Y.X).hom ⊗ (β_ X.X Y.X).hom) ≫ (Y ⊗ X).mul := by
  dsimp
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right, BraidedCategory.braiding_tensor_left,
    comp_whiskerRight, whisker_assoc, MonoidalCategory.whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
    pentagon_inv_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

instance : SymmetricCategory (Mon_ C) where
  braiding := fun X Y => mkIso (β_ X.X Y.X) one_braiding mul_braiding
  symmetry := fun X Y => by
    ext
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]

end SymmetricCategory

end Mon_

section

variable {C} [BraidedCategory.{v₁} C]

/-- Predicate for a monoid object to be commutative. -/
class IsCommMon (X : C) [Mon_Class X] where
  mul_comm' : (β_ X X).hom ≫ μ = μ := by aesop_cat

open scoped Mon_Class

namespace IsCommMon

@[reassoc (attr := simp)]
theorem mul_comm (X : C) [Mon_Class X] [IsCommMon X] : (β_ X X).hom ≫ μ = μ := mul_comm'

end IsCommMon

end

/-!
Projects:
* Check that `Mon_ MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `MonCat` first,
  available in https://github.com/leanprover-community/mathlib3/pull/3463)
* More generally, check that `Mon_ (Mon_ C) ≌ CommMon_ C` when `C` is braided.
* Check that `Mon_ TopCat ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGrp ≌ RingCat`.
  (We've already got `Mon_ (ModuleCat R) ≌ AlgebraCat R`,
  in `Mathlib.CategoryTheory.Monoidal.Internal.Module`.)
* Can you transport this monoidal structure to `RingCat` or `AlgebraCat R`?
  How does it compare to the "native" one?
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor `map_Mon F : Mon_ C ⥤ Mon_ D`
  is lax monoidal.
-/
