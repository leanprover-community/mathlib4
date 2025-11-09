/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Categories with classes of fibrations, cofibrations, weak equivalences

We introduce typeclasses `CategoryWithFibrations`, `CategoryWithCofibrations` and
`CategoryWithWeakEquivalences` to express that a category `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" or "weak equivalences".

-/

universe v u

namespace HomotopicalAlgebra

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category with fibrations is a category equipped with
a class of morphisms named "fibrations". -/
class CategoryWithFibrations where
  /-- the class of fibrations -/
  fibrations : MorphismProperty C

/-- A category with cofibrations is a category equipped with
a class of morphisms named "cofibrations". -/
class CategoryWithCofibrations where
  /-- the class of cofibrations -/
  cofibrations : MorphismProperty C

/-- A category with weak equivalences is a category equipped with
a class of morphisms named "weak equivalences". -/
class CategoryWithWeakEquivalences where
  /-- the class of weak equivalences -/
  weakEquivalences : MorphismProperty C

variable {X Y : C} (f : X ⟶ Y)

section Fib

variable [CategoryWithFibrations C]

/-- The class of fibrations in a category with fibrations. -/
def fibrations : MorphismProperty C := CategoryWithFibrations.fibrations

variable {C}

/-- A morphism `f` satisfies `[Fibration f]` if it belongs to `fibrations C`. -/
@[mk_iff]
class Fibration : Prop where
  mem : fibrations C f

lemma mem_fibrations [Fibration f] : fibrations C f := Fibration.mem

end Fib

section Cof

variable [CategoryWithCofibrations C]

/-- The class of cofibrations in a category with cofibrations. -/
def cofibrations : MorphismProperty C := CategoryWithCofibrations.cofibrations

variable {C}

/-- A morphism `f` satisfies `[Cofibration f]` if it belongs to `cofibrations C`. -/
@[mk_iff]
class Cofibration : Prop where
  mem : cofibrations C f

lemma mem_cofibrations [Cofibration f] : cofibrations C f := Cofibration.mem

end Cof

section W

variable [CategoryWithWeakEquivalences C]

/-- The class of weak equivalences in a category with weak equivalences. -/
def weakEquivalences : MorphismProperty C := CategoryWithWeakEquivalences.weakEquivalences

variable {C}

/-- A morphism `f` satisfies `[WeakEquivalence f]` if it belongs to `weakEquivalences C`. -/
@[mk_iff]
class WeakEquivalence : Prop where
  mem : weakEquivalences C f

lemma mem_weakEquivalences [WeakEquivalence f] : weakEquivalences C f := WeakEquivalence.mem

end W

section TrivFib

variable [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]

/-- A trivial fibration is a morphism that is both a fibration and a weak equivalence. -/
def trivialFibrations : MorphismProperty C := fibrations C ⊓ weakEquivalences C

lemma trivialFibrations_sub_fibrations : trivialFibrations C ≤ fibrations C :=
  fun _ _ _ hf ↦ hf.1

lemma trivialFibrations_sub_weakEquivalences : trivialFibrations C ≤ weakEquivalences C :=
  fun _ _ _ hf ↦ hf.2

variable {C}

lemma mem_trivialFibrations [Fibration f] [WeakEquivalence f] :
    trivialFibrations C f :=
  ⟨mem_fibrations f, mem_weakEquivalences f⟩

lemma mem_trivialFibrations_iff :
    trivialFibrations C f ↔ Fibration f ∧ WeakEquivalence f := by
  rw [fibration_iff, weakEquivalence_iff]
  rfl

end TrivFib

section TrivCof

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- A trivial cofibration is a morphism that is both a cofibration and a weak equivalence. -/
def trivialCofibrations : MorphismProperty C := cofibrations C ⊓ weakEquivalences C

lemma trivialCofibrations_sub_cofibrations : trivialCofibrations C ≤ cofibrations C :=
  fun _ _ _ hf ↦ hf.1

lemma trivialCofibrations_sub_weakEquivalences : trivialCofibrations C ≤ weakEquivalences C :=
  fun _ _ _ hf ↦ hf.2


variable {C}

lemma mem_trivialCofibrations [Cofibration f] [WeakEquivalence f] :
    trivialCofibrations C f :=
  ⟨mem_cofibrations f, mem_weakEquivalences f⟩

lemma mem_trivialCofibrations_iff :
    trivialCofibrations C f ↔ Cofibration f ∧ WeakEquivalence f := by
  rw [cofibration_iff, weakEquivalence_iff]
  rfl

end TrivCof

section

variable [CategoryWithCofibrations C]

instance : CategoryWithFibrations Cᵒᵖ where
  fibrations := (cofibrations C).op

lemma fibrations_op : fibrations Cᵒᵖ = (cofibrations C).op := rfl
lemma cofibrations_eq_unop : cofibrations C = (fibrations Cᵒᵖ).unop := rfl

variable {C}

lemma fibration_op_iff : Fibration f.op ↔ Cofibration f := by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

lemma cofibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Cofibration f.unop ↔ Fibration f := by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

instance [Cofibration f] : Fibration f.op := by
  rwa [fibration_op_iff]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [Fibration f] : Cofibration f.unop := by
  rwa [cofibration_unop_iff]

end

section

variable [CategoryWithFibrations C]

instance : CategoryWithCofibrations Cᵒᵖ where
  cofibrations := (fibrations C).op

lemma cofibrations_op : cofibrations Cᵒᵖ = (fibrations C).op := rfl
lemma fibrations_eq_unop : fibrations C = (cofibrations Cᵒᵖ).unop := rfl

variable {C}

lemma cofibration_op_iff : Cofibration f.op ↔ Fibration f := by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

lemma fibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Fibration f.unop ↔ Cofibration f := by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

instance [Fibration f] : Cofibration f.op := by
  rwa [cofibration_op_iff]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [Cofibration f] : Fibration f.unop := by
  rwa [fibration_unop_iff]

end

section

variable [CategoryWithWeakEquivalences C]

instance : CategoryWithWeakEquivalences Cᵒᵖ where
  weakEquivalences := (weakEquivalences C).op

lemma weakEquivalences_op : weakEquivalences Cᵒᵖ = (weakEquivalences C).op := rfl
lemma weakEquivalences_eq_unop : weakEquivalences C = (weakEquivalences Cᵒᵖ).unop := rfl

variable {C}

lemma weakEquivalences_op_iff : WeakEquivalence f.op ↔ WeakEquivalence f := by
  simp [weakEquivalence_iff, weakEquivalences_op]

lemma weakEquivalences_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    WeakEquivalence f.unop ↔ WeakEquivalence f :=
  (weakEquivalences_op_iff f.unop).symm

instance [WeakEquivalence f] : WeakEquivalence f.op := by
  rwa [weakEquivalences_op_iff]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.unop := by
  rwa [weakEquivalences_unop_iff]

end

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]

lemma trivialFibrations_op : trivialFibrations Cᵒᵖ = (trivialCofibrations C).op := rfl
lemma trivialCofibrations_eq_unop : trivialCofibrations C = (trivialFibrations Cᵒᵖ).unop := rfl

end

section

variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]

lemma trivialCofibrations_op : trivialCofibrations Cᵒᵖ = (trivialFibrations C).op := rfl
lemma trivialFibrations_eq_unop : trivialFibrations C = (trivialCofibrations Cᵒᵖ).unop := rfl

end

end HomotopicalAlgebra
