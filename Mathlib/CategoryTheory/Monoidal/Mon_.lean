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

## Simp set for monoid object tautologies

In this file, we also provide a simp set called `mon_tauto` whose goal is to prove all tautologies
about morphisms from some (tensor) power of `M` to `M`, where `M` is a (commutative) monoid object
in a (braided) monoidal category.

Please read the documentation in `Mathlib/Tactic/Attr/Register.lean` for full details.
-/

universe w v₁ v₂ v₃ u₁ u₂ u₃ u

open Function CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class MonObj (X : C) where
  /-- The unit morphism of a monoid object. -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  mul : X ⊗ X ⟶ X
  one_mul (X) : one ▷ X ≫ mul = (λ_ X).hom := by cat_disch
  mul_one (X) : X ◁ one ≫ mul = (ρ_ X).hom := by cat_disch
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `Monoid.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc (X) : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by cat_disch

@[deprecated (since := "2025-09-09")] alias Mon_Class := MonObj

namespace MonObj
variable {M X Y : C} [MonObj M]

@[inherit_doc] scoped notation "μ" => MonObj.mul
@[inherit_doc] scoped notation "μ["M"]" => MonObj.mul (X := M)
@[inherit_doc] scoped notation "η" => MonObj.one
@[inherit_doc] scoped notation "η["M"]" => MonObj.one (X := M)

attribute [reassoc (attr := simp)] one_mul mul_one mul_assoc

/-- Transfer `MonObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[simps! -isSimp]
def ofIso (e : M ≅ X) : MonObj X where
  one := η[M] ≫ e.hom
  mul := (e.inv ⊗ₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (λ_ X).inv]
    simp only [comp_whiskerRight, tensorHom_def, Category.assoc,
      hom_inv_whiskerRight_assoc]
    simp [← tensorHom_def_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv]
    simp only [MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
      whiskerLeft_hom_inv_assoc, Iso.inv_hom_id]
    simp [← tensorHom_def'_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  mul_assoc := by simpa [← id_tensorHom, ← tensorHom_id,
      -associator_conjugation, associator_naturality_assoc] using
      congr(((e.inv ⊗ₘ e.inv) ⊗ₘ e.inv) ≫ $(MonObj.mul_assoc M) ≫ e.hom)

@[simps]
instance : MonObj (𝟙_ C) where
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

@[ext]
theorem ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul) : h₁ = h₂ := by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (λ_ _).inv ≫ (h₁.one ⊗ₘ h₂.one) ≫ h₁.mul
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

end MonObj

open scoped MonObj

namespace Mathlib.Tactic.MonTauto
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {M W X X₁ X₂ X₃ Y Y₁ Y₂ Y₃ Z Z₁ Z₂ : C} [MonObj M]

attribute [mon_tauto] Category.id_comp Category.comp_id Category.assoc
  id_tensorHom_id tensorμ tensorδ
  tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc
  leftUnitor_tensor_hom leftUnitor_tensor_hom_assoc
  leftUnitor_tensor_inv leftUnitor_tensor_inv_assoc
  rightUnitor_tensor_hom rightUnitor_tensor_hom_assoc
  rightUnitor_tensor_inv rightUnitor_tensor_inv_assoc

attribute [mon_tauto ←] tensorHom_id id_tensorHom

@[reassoc (attr := mon_tauto)]
lemma associator_hom_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f ⊗ₘ g ⊗ₘ h) = ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).hom := by simp

@[reassoc (attr := mon_tauto)]
lemma associator_inv_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) = (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).inv := by simp

@[reassoc (attr := mon_tauto)]
lemma associator_hom_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (gh : Y₂ ⊗ Z₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ gh)) =
      ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).hom ≫ (𝟙 _ ⊗ₘ gh) := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
lemma associator_inv_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (fg : X₂ ⊗ Y₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).inv ≫ (((f ⊗ₘ g) ≫ fg) ⊗ₘ h) =
      (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).inv ≫ (fg ⊗ₘ 𝟙 _) := by simp [tensorHom_def']

@[mon_tauto] lemma eq_one_mul : (λ_ M).hom = (η ⊗ₘ 𝟙 M) ≫ μ := by simp
@[mon_tauto] lemma eq_mul_one : (ρ_ M).hom = (𝟙 M ⊗ₘ η) ≫ μ := by simp

@[reassoc (attr := mon_tauto)] lemma leftUnitor_inv_one_tensor_mul (f : X₁ ⟶ M) :
    (λ_ _).inv ≫ (η ⊗ₘ f) ≫ μ = f := by simp [tensorHom_def']

@[reassoc (attr := mon_tauto)] lemma rightUnitor_inv_tensor_one_mul (f : X₁ ⟶ M) :
    (ρ_ _).inv ≫ (f ⊗ₘ η) ≫ μ = f := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
lemma mul_assoc_hom (f : X ⟶ M) :
    (α_ X M M).hom ≫ (f ⊗ₘ μ) ≫ μ = ((f ⊗ₘ 𝟙 M) ≫ μ ⊗ₘ 𝟙 M) ≫ μ := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
lemma mul_assoc_inv (f : X ⟶ M) :
    (α_ M M X).inv ≫ (μ ⊗ₘ f) ≫ μ = (𝟙 M ⊗ₘ (𝟙 M ⊗ₘ f) ≫ μ) ≫ μ  := by simp [tensorHom_def']

end Mathlib.Tactic.MonTauto

variable {M N O X : C} [MonObj M] [MonObj N] [MonObj O]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsMonHom (f : M ⟶ N) : Prop where
  one_hom (f) : η ≫ f = η := by cat_disch
  mul_hom (f) : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch

@[deprecated (since := "2025-09-15")] alias IsMon_Hom := IsMonHom

attribute [reassoc (attr := simp)] IsMonHom.one_hom IsMonHom.mul_hom

instance : IsMonHom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g] : IsMonHom (f ≫ g) where

attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
instance isMonHom_ofIso (e : M ≅ X) : letI := MonObj.ofIso e; IsMonHom e.hom := by
  letI := MonObj.ofIso e; exact { }

instance (f : M ≅ N) [IsMonHom f.hom] : IsMonHom f.inv where
  one_hom := by simp [Iso.comp_inv_eq]
  mul_hom := by simp [Iso.comp_inv_eq]

instance {f : M ⟶ N} [IsIso f] [IsMonHom f] : IsMonHom (asIso f).hom := ‹_›

variable (C) in
/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]

@[deprecated (since := "2025-09-15")] alias Mon_ := Mon

attribute [instance] Mon.mon

namespace Mon

variable (C) in
/-- The trivial monoid object. We later show this is initial in `Mon C`.
-/
@[simps!]
def trivial : Mon C := mk (𝟙_ C)

instance : Inhabited (Mon C) :=
  ⟨trivial C⟩

end Mon

namespace MonObj

variable {M : C} [MonObj M]

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M) : (η[M] ⊗ₘ f) ≫ μ[M] = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, one_mul, leftUnitor_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M) : (f ⊗ₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, mul_one, rightUnitor_naturality]

variable (M) in
@[reassoc]
theorem mul_assoc_flip : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ := by
  simp

end MonObj

namespace MonObj

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
`Mathlib/CategoryTheory/Monoidal/Braided.lean`.
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
which have also been proved in `Mathlib/CategoryTheory/Monoidal/Braided.lean`.

-/

-- The proofs that associators and unitors preserve monoid units don't require braiding.
lemma one_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N]) ⊗ₘ η[P])) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ (λ_ (𝟙_ C)).inv ≫ (η[N] ⊗ₘ η[P])) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), ← tensorHom_comp_tensorHom]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, ← tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp

lemma one_leftUnitor {M : C} [MonObj M] :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[M])) ≫ (λ_ M).hom = η := by
  simp

lemma one_rightUnitor {M : C} [MonObj M] :
    ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

lemma Mon_tensor_one_mul (M N : C) [MonObj M] [MonObj N] :
    (((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (λ_ (M ⊗ N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

lemma Mon_tensor_mul_one (M N : C) [MonObj M] [MonObj N] :
    (M ⊗ N) ◁ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] ⊗ₘ μ[N]) =
      (ρ_ (M ⊗ N)).hom := by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

lemma Mon_tensor_mul_assoc (M N : C) [MonObj M] [MonObj N] :
    ((tensorμ M N M N ≫ (μ ⊗ₘ μ)) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensorμ M N M N ≫ (μ ⊗ₘ μ))) ≫
          tensorμ M N M N ≫ (μ ⊗ₘ μ) := by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_assoc, mul_assoc, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

lemma mul_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] :
    (tensorμ (M ⊗ N) P (M ⊗ N) P ≫
          (tensorμ M N M N ≫ (μ ⊗ₘ μ) ⊗ₘ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ₘ (α_ M N P).hom) ≫
        tensorμ M (N ⊗ P) M (N ⊗ P) ≫
          (μ ⊗ₘ tensorμ N P N P ≫ (μ ⊗ₘ μ)) := by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

lemma mul_leftUnitor {M : C} [MonObj M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ₘ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

lemma mul_rightUnitor {M : C} [MonObj M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ₘ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

namespace tensorObj

-- We don't want `tensorObj.one_def` to be simp as it would loop with `IsMonHom.one_hom` applied
-- to `(λ_ N.X).inv`.
@[simps -isSimp]
instance {M N : C} [MonObj M] [MonObj N] : MonObj (M ⊗ N) where
  one := (λ_ (𝟙_ C)).inv ≫ (η ⊗ₘ η)
  mul := tensorμ M N M N ≫ (μ ⊗ₘ μ)
  one_mul := Mon_tensor_one_mul M N
  mul_one := Mon_tensor_mul_one M N
  mul_assoc := Mon_tensor_mul_assoc M N

end tensorObj

open IsMonHom

variable {X Y Z W : C} [MonObj X] [MonObj Y] [MonObj Z] [MonObj W]

instance {f : X ⟶ Y} {g : Z ⟶ W} [IsMonHom f] [IsMonHom g] : IsMonHom (f ⊗ₘ g) where
  one_hom := by
    dsimp [tensorObj.one_def]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, one_hom, one_hom]
  mul_hom := by
    dsimp [tensorObj.mul_def]
    slice_rhs 1 2 => rw [tensorμ_natural]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, mul_hom, mul_hom, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]

instance : IsMonHom (𝟙 X) where

instance {f : Y ⟶ Z} [IsMonHom f] : IsMonHom (X ◁ f) where
  one_hom := by simpa using (inferInstanceAs <| IsMonHom (𝟙 X ⊗ₘ f)).one_hom
  mul_hom := by simpa using (inferInstanceAs <| IsMonHom (𝟙 X ⊗ₘ f)).mul_hom

instance {f : X ⟶ Y} [IsMonHom f] : IsMonHom (f ▷ Z) where
  one_hom := by simpa using (inferInstanceAs <| IsMonHom (f ⊗ₘ (𝟙 Z))).one_hom
  mul_hom := by simpa using (inferInstanceAs <| IsMonHom (f ⊗ₘ (𝟙 Z))).mul_hom

instance : IsMonHom (α_ X Y Z).hom :=
  ⟨one_associator, mul_associator⟩

instance : IsMonHom (λ_ X).hom :=
  ⟨one_leftUnitor, mul_leftUnitor⟩

instance : IsMonHom (ρ_ X).hom :=
  ⟨one_rightUnitor, mul_rightUnitor⟩

lemma one_braiding (X Y : C) [MonObj X] [MonObj Y] : η ≫ (β_ X Y).hom = η := by
  simp only [tensorObj.one_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

end MonObj

namespace Mon

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mon C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isMonHom_hom : IsMonHom hom]

attribute [instance] Hom.isMonHom_hom

/-- Construct a morphism `M ⟶ N` of `Mon C` from a map `f : M ⟶ N` and a `IsMonHom f` instance. -/
abbrev Hom.mk' {M N : Mon C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch) : Hom M N :=
  have : IsMonHom f := ⟨one_f, mul_f⟩
  .mk f

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : Mon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Mon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Mon C} (f : M ⟶ N) : IsMonHom f.hom := f.isMonHom_hom

@[ext]
lemma Hom.ext' {M N : Mon C} {f g : M ⟶ N} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

lemma hom_injective {M N : Mon C} : Injective (Hom.hom : (M ⟶ N) → (M.X ⟶ N.X)) :=
  fun _ _ ↦ Hom.ext

@[simp]
theorem id_hom' (M : Mon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Mon C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : Mon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨.mk' (inv f.hom), by cat_disch⟩⟩

instance {M N : Mon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

/-- Construct an isomorphism of monoid objects by giving a monoid isomorphism between the underlying
objects. -/
@[simps]
def mkIso' {M N : C} [MonObj M] [MonObj N] (e : M ≅ N) [IsMonHom e.hom] : mk M ≅ mk N where
  hom := Hom.mk e.hom
  inv := Hom.mk e.inv

/-- Construct an isomorphism of monoid objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
@[simps!]
abbrev mkIso {M N : Mon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[simps]
instance uniqueHomFromTrivial (A : Mon C) : Unique (trivial C ⟶ A) where
  default.hom := η[A.X]
  default.isMonHom_hom.mul_hom := by simp [unitors_equal]
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_one, IsMonHom.one_hom]

open CategoryTheory.Limits

instance : HasInitial (Mon C) :=
  hasInitial_of_unique (Mon.trivial C)

section BraidedCategory
variable [BraidedCategory C]

@[simps! tensorObj_X tensorHom_hom]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon C) where
  tensorObj M N := ⟨M.X ⊗ N.X⟩
  tensorHom f g := Hom.mk (f.hom ⊗ₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator M N P := mkIso' <| associator M.X N.X P.X
  leftUnitor M := mkIso' <| leftUnitor M.X
  rightUnitor M := mkIso' <| rightUnitor M.X

@[simp] lemma tensorUnit_X : (𝟙_ (Mon C)).X = 𝟙_ C := rfl
@[simp] lemma tensorUnit_one : η[(𝟙_ (Mon C)).X] = 𝟙 (𝟙_ C) := rfl
@[simp] lemma tensorUnit_mul : μ[(𝟙_ (Mon C)).X] = (λ_ (𝟙_ C)).hom := rfl

@[simp]
lemma tensorObj_one (X Y : Mon C) : η[(X ⊗ Y).X] = (λ_ (𝟙_ C)).inv ≫ (η[X.X] ⊗ₘ η[Y.X]) := rfl

@[simp] lemma tensorObj_mul (X Y : Mon C) :
    μ[(X ⊗ Y).X] = tensorμ X.X Y.X X.X Y.X ≫ (μ[X.X] ⊗ₘ μ[Y.X]) := rfl

@[simp]
lemma whiskerLeft_hom {X Y : Mon C} (f : X ⟶ Y) (Z : Mon C) : (f ▷ Z).hom = f.hom ▷ Z.X := rfl

@[simp]
lemma whiskerRight_hom (X : Mon C) {Y Z : Mon C} (f : Y ⟶ Z) : (X ◁ f).hom = X.X ◁ f.hom := rfl

@[simp] lemma leftUnitor_hom_hom (X : Mon C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl
@[simp] lemma leftUnitor_inv_hom (X : Mon C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl
@[simp] lemma rightUnitor_hom_hom (X : Mon C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl
@[simp] lemma rightUnitor_inv_hom (X : Mon C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[simp] lemma associator_hom_hom (X Y Z : Mon C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl
@[simp] lemma associator_inv_hom (X Y Z : Mon C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[simp] lemma tensor_one (M N : Mon C) : η[(M ⊗ N).X] = (λ_ (𝟙_ C)).inv ≫ (η[M.X] ⊗ₘ η[N.X]) := rfl

@[simp]
lemma tensor_mul (M N : Mon C) : μ[(M ⊗ N).X] = tensorμ M.X N.X M.X N.X ≫ (μ[M.X] ⊗ₘ μ[N.X]) := rfl

instance monMonoidal : MonoidalCategory (Mon C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

-- We don't want `tensorObj.one_def` to be simp as it would loop with `IsMonHom.one_hom` applied
-- to `(λ_ N.X).inv`.
@[simps! -isSimp]
instance {M N : C} [MonObj M] [MonObj N] : MonObj (M ⊗ N) :=
  inferInstanceAs <| MonObj (Mon.mk M ⊗ Mon.mk N).X

variable (C)

/-- The forgetful functor from `Mon C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[simp] lemma forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] lemma forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] lemma forget_μ (X Y : Mon C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] lemma forget_δ (X Y : Mon C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory
end Mon

/-!
We next show that if `C` is symmetric, then `Mon C` is braided, and indeed symmetric.

Note that `Mon C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

namespace MonObj

lemma mul_braiding (X Y : C) [MonObj X] [MonObj Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom ⊗ₘ (β_ X Y).hom) ≫ μ := by
  dsimp [tensorObj.mul_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc, pentagon_inv_assoc,
    Iso.hom_inv_id_assoc]
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

instance {X Y : C} [MonObj X] [MonObj Y] : IsMonHom (β_ X Y).hom :=
  ⟨one_braiding X Y, mul_braiding X Y⟩

end MonObj

namespace Mon

instance : SymmetricCategory (Mon C) where
  braiding X Y := mkIso' (β_ X.X Y.X)

@[simp] lemma braiding_hom_hom (M N : Mon C) : (β_ M N).hom.hom = (β_ M.X N.X).hom := rfl
@[simp] lemma braiding_inv_hom (M N : Mon C) : (β_ M N).inv.hom = (β_ M.X N.X).inv := rfl

end Mon
end SymmetricCategory

namespace CategoryTheory
variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor

section LaxMonoidal
variable [F.LaxMonoidal] [F'.LaxMonoidal] [G.LaxMonoidal] (X Y : C) [MonObj X] [MonObj Y]
  (f : X ⟶ Y) [IsMonHom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev monObjObj : MonObj (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul := by simp [← F.map_comp]
  mul_one := by simp [← F.map_comp]
  mul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, MonObj.mul_assoc]
    simp

@[deprecated (since := "2025-09-09")] alias mon_ClassObj := monObjObj

scoped[Obj] attribute [instance] CategoryTheory.Functor.monObjObj

open scoped Obj

@[reassoc, simp] lemma obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[reassoc, simp] lemma obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

instance map.instIsMonHom : IsMonHom (F.map f) where
  one_hom := by simp [← map_comp]
  mul_hom := by simp [← map_comp]

open MonObj

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMon A)
variable (F) in
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon C ⥤ Mon D`.
-/
@[simps]
def mapMon : Mon C ⥤ Mon D where
  obj A := .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[simp]
theorem id_mapMon_one (X : Mon C) : η[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ η[X.X] := rfl

@[simp]
theorem id_mapMon_mul (X : Mon C) : μ[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ μ[X.X] := rfl

@[simp]
theorem comp_mapMon_one (X : Mon C) :
    η[((F ⋙ G).mapMon.obj X).X] = ε (F ⋙ G) ≫ (F ⋙ G).map η[X.X] :=
  rfl

@[simp]
theorem comp_mapMon_mul (X : Mon C) :
    μ[((F ⋙ G).mapMon.obj X).X] = «μ» (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[X.X] :=
  rfl

/-- The identity functor is also the identity on monoid objects. -/
@[simps!]
def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon C) :=
  NatIso.ofComponents fun X ↦ Mon.mkIso (.refl _)

/-- The composition functor is also the composition on monoid objects. -/
@[simps!]
def mapMonCompIso : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X ↦ Mon.mkIso (.refl _)

protected instance Faithful.mapMon [F.Faithful] : F.mapMon.Faithful where
  map_injective {_X _Y} _f _g hfg := Mon.Hom.ext <| map_injective congr(($hfg).hom)

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
def mapMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapMon ⟶ F'.mapMon where
  app X := .mk' (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
def mapMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapMon ≅ F'.mapMon :=
  NatIso.ofComponents fun X ↦ Mon.mkIso (e.app _)

end LaxMonoidal

section OplaxMonoidal
variable [F.OplaxMonoidal]

open scoped MonObj in
/-- Pullback a monoid object along a fully faithful oplax monoidal functor. -/
@[simps]
abbrev FullyFaithful.monObj (hF : F.FullyFaithful) (X : C) [MonObj (F.obj X)] : MonObj X where
  one := hF.preimage <| OplaxMonoidal.η F ≫ η[F.obj X]
  mul := hF.preimage <| OplaxMonoidal.δ F X X ≫ μ[F.obj X]
  one_mul := hF.map_injective <| by simp [← δ_natural_left_assoc]
  mul_one := hF.map_injective <| by simp [← δ_natural_right_assoc]
  mul_assoc := hF.map_injective <| by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

@[deprecated (since := "2025-09-09")] alias FullyFaithful.mon_Class := FullyFaithful.monObj

end OplaxMonoidal

section Monoidal
variable [F.Monoidal]

open scoped Obj

protected instance Full.mapMon [F.Full] [F.Faithful] : F.mapMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      isMonHom_hom.one_hom :=
        F.map_injective <| by simpa [← hg, cancel_epi] using IsMonHom.one_hom f.hom
      isMonHom_hom.mul_hom :=
        F.map_injective <| by simpa [← hg, cancel_epi] using IsMonHom.mul_hom f.hom },
      Mon.Hom.ext hg⟩

instance FullyFaithful.isMonHom_preimage (hF : F.FullyFaithful) {X Y : C}
    [MonObj X] [MonObj Y] (f : F.obj X ⟶ F.obj Y) [IsMonHom f] :
    IsMonHom (hF.preimage f) where
  one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : Mon C ⥤ Mon D` is fully
faithful too. -/
@[simps]
protected def FullyFaithful.mapMon (hF : F.FullyFaithful) : F.mapMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
open Monoidal in
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on monoid objects as on objects. -/
@[simp] lemma essImage_mapMon [F.Full] [F.Faithful] {M : Mon D} :
    F.mapMon.essImage M ↔ F.essImage M.X where
  mp := by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(Mon.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    let : MonObj (F.obj N) := .ofIso e.symm
    let : MonObj N := (FullyFaithful.ofFullyFaithful F).monObj N
    refine ⟨.mk N, ⟨Mon.mkIso e ?_ ?_⟩⟩ <;> simp

end Monoidal

variable (C D) in
/-- `mapMon` is functorial in the lax monoidal functor. -/
@[simps]
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon C ⥤ Mon D where
  obj F := F.mapMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [a.IsMonoidal]

/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to monoid objects. -/
@[simps] def mapMon : F.mapMon ⊣ G.mapMon where
  unit := mapMonIdIso.inv ≫ mapMonNatTrans a.unit ≫ mapMonCompIso.hom
  counit := mapMonCompIso.inv ≫ mapMonNatTrans a.counit ≫ mapMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their monoid objects. -/
@[simps]
def mapMon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    Mon C ≌ Mon D where
  functor := e.functor.mapMon
  inverse := e.inverse.mapMon
  unitIso := mapMonIdIso.symm ≪≫ mapMonNatIso e.unitIso ≪≫ mapMonCompIso
  counitIso := mapMonCompIso.symm ≪≫ mapMonNatIso e.counitIso ≪≫ mapMonIdIso

end CategoryTheory.Equivalence

namespace Mon

namespace EquivLaxMonoidalFunctorPUnit

variable (C) in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ⥤ Mon C where
  obj F := (F.mapMon : Mon _ ⥤ Mon C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def monToLaxMonoidalObj (A : Mon C) :
    Discrete PUnit.{w + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : Mon C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

@[simp]
lemma monToLaxMonoidalObj_ε (A : Mon C) :
    ε (monToLaxMonoidalObj A) = η[A.X] := rfl

@[simp]
lemma monToLaxMonoidalObj_μ (A : Mon C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = μ[A.X] := rfl

variable (C)
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : Mon C ⥤ LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))

/-- Auxiliary definition for `counitIso`. -/
@[simps!]
def counitIsoAux (F : Mon C) :
    ((monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C).obj F).X ≅ ((𝟭 (Mon C)).obj F).X :=
  Iso.refl _

@[simp]
theorem monToLaxMonoidal_laxMonoidalToMon_obj_one (F : Mon C) :
    η[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = η[F.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem monToLaxMonoidal_laxMonoidalToMon_obj_mul (F : Mon C) :
    μ[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = μ[F.X] ≫ 𝟙 _ :=
  rfl

theorem isMonHom_counitIsoAux (F : Mon C) :
    IsMonHom (counitIsoAux C F).hom where

@[deprecated (since := "2025-09-15")] alias counitIsoAux_IsMon_Hom := isMonHom_counitIsoAux

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon C) :=
  NatIso.ofComponents fun F ↦
    letI : IsMonHom (counitIsoAux.{w} C F).hom := isMonHom_counitIsoAux C F
    mkIso (counitIsoAux.{w} C F)

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ≌ Mon C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end Mon

section

variable [BraidedCategory.{v₁} C]

/-- Predicate for a monoid object to be commutative. -/
class IsCommMonObj (X : C) [MonObj X] where
  mul_comm (X) : (β_ X X).hom ≫ μ = μ := by cat_disch

@[deprecated (since := "2025-09-14")] alias IsCommMon := IsCommMonObj

open scoped MonObj

namespace IsCommMonObj

attribute [reassoc (attr := simp, mon_tauto)] mul_comm

variable (M) in
@[reassoc (attr := simp, mon_tauto)]
lemma mul_comm' [IsCommMonObj M] : (β_ M M).inv ≫ μ = μ := by simp [← cancel_epi (β_ M M).hom]

instance : IsCommMonObj (𝟙_ C) where
  mul_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal]

end IsCommMonObj

variable (M) in
@[reassoc (attr := simp)]
lemma MonObj.mul_mul_mul_comm [IsCommMonObj M] :
    tensorμ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]

@[deprecated (since := "2025-09-09")] alias Mon_Class.mul_mul_mul_comm := MonObj.mul_mul_mul_comm

variable (M) in
@[reassoc (attr := simp)]
lemma MonObj.mul_mul_mul_comm' [IsCommMonObj M] :
    tensorδ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]

@[deprecated (since := "2025-09-09")] alias Mon_Class.mul_mul_mul_comm' := MonObj.mul_mul_mul_comm'

end

section SymmetricCategory
variable [SymmetricCategory C] {M N W X Y Z : C} [MonObj M] [MonObj N]

instance [IsCommMonObj M] [IsCommMonObj N] : IsCommMonObj (M ⊗ N) where
  mul_comm := by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft,
      MonObj.tensorObj.mul_def, ← whiskerLeft_comp_assoc, -whiskerLeft_comp]

end SymmetricCategory

/-!
Projects:
* Check that `Mon MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the Cartesian monoidal structure on `MonCat` first,
  available in https://github.com/leanprover-community/mathlib3/pull/3463)
* More generally, check that `Mon (Mon C) ≌ CommMon C` when `C` is braided.
* Check that `Mon TopCat ≌ [bundled topological monoids]`.
* Check that `Mon AddCommGrpCat ≌ RingCat`.
  (We've already got `Mon (ModuleCat R) ≌ AlgCat R`,
  in `Mathlib/CategoryTheory/Monoidal/Internal/Module.lean`.)
* Can you transport this monoidal structure to `RingCat` or `AlgCat R`?
  How does it compare to the "native" one?
* Show that when `F` is a lax braided functor `C ⥤ D`, the functor `map_Mon F : Mon C ⥤ Mon D`
  is lax monoidal.
-/
