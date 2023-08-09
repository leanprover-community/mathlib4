/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.LanguageMap
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Field.MinimalAxioms

namespace FirstOrder

open FirstOrder

inductive FieldFunctions : ℕ → Type
  | add : FieldFunctions 2
  | mul : FieldFunctions 2
  | neg : FieldFunctions 1
  | inv : FieldFunctions 1
  | zero : FieldFunctions 0
  | one : FieldFunctions 0
  deriving DecidableEq

protected def Language.field : Language :=
  { Functions := FieldFunctions
    Relations := fun _ => Empty }

namespace Language

namespace field

open FieldFunctions

instance (n : ℕ) : DecidableEq (Language.field.Functions n) := by
  dsimp [Language.field]; infer_instance

instance (n : ℕ) : DecidableEq (Language.field.Relations n) := by
  dsimp [Language.field]; infer_instance

abbrev zeroFunction : Language.field.Functions 0 := zero

abbrev oneFunction : Language.field.Functions 0 := one

abbrev addFunction : Language.field.Functions 2 := add

abbrev mulFunction : Language.field.Functions 2 := mul

abbrev negFunction : Language.field.Functions 1 := neg

abbrev invFunction : Language.field.Functions 1 := inv

instance (α : Type _) : Zero (Language.field.Term α) :=
{ zero := Constants.term zeroFunction }

theorem zero_def (α : Type _) : (0 : Language.field.Term α) = Constants.term zeroFunction := rfl

instance (α : Type _) : One (Language.field.Term α) :=
{ one := Constants.term oneFunction }

theorem one_def (α : Type _) : (1 : Language.field.Term α) = Constants.term oneFunction := rfl

instance (α : Type _) : Add (Language.field.Term α) :=
{ add := addFunction.apply₂ }

theorem add_def (α : Type _) (t₁ t₂ : Language.field.Term α) :
    t₁ + t₂ = addFunction.apply₂ t₁ t₂ := rfl

instance (α : Type _) : Mul (Language.field.Term α) :=
{ mul := mulFunction.apply₂ }

theorem mul_def (α : Type _) (t₁ t₂ : Language.field.Term α) :
    t₁ * t₂ = mulFunction.apply₂ t₁ t₂ := rfl

instance (α : Type _) : Neg (Language.field.Term α) :=
{ neg := negFunction.apply₁ }

theorem neg_def (α : Type _) (t : Language.field.Term α) :
    -t = negFunction.apply₁ t := rfl

instance (α : Type _) : Inv (Language.field.Term α) :=
{ inv := invFunction.apply₁ }

theorem inv_def (α : Type _) (t : Language.field.Term α) :
    t⁻¹ = invFunction.apply₁ t := rfl

@[simp]
instance : Language.ring.Structure (Language.field.Term α) :=
  { RelMap := Empty.elim,
    funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .neg => fun x => -x 0
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1 }

instance : Fintype Language.field.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .add⟩,
       Sum.inl ⟨2, .mul⟩,
       Sum.inl ⟨1, .inv⟩,
       Sum.inl ⟨1, .neg⟩,
       Sum.inl ⟨0, .zero⟩,
       Sum.inl ⟨0, .one⟩], by
    dsimp [Language.Symbols]; decide⟩, by
    intro x
    dsimp [Language.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    . cases f <;> decide
    . cases f ⟩

@[simp]
theorem card_field : card Language.field = 6 := by
  have : Fintype.card Language.field.Symbols = 6 := rfl
  simp [Language.card, this]

end field

end Language

open Language field Structure BoundedFormula

inductive FieldAxiom : Type
  | addAssoc : FieldAxiom
  | zeroAdd : FieldAxiom
  | addLeftNeg : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | mulInvCancel : FieldAxiom
  | invZero : FieldAxiom
  | leftDistrib : FieldAxiom
  | existsPairNe : FieldAxiom
  deriving DecidableEq

@[simp]
def FieldAxiom.toSentence : FieldAxiom → Language.field.Sentence
  | .addAssoc => ∀' ∀' ∀' (((&0 + &1) + &2) =' (&0 + (&1 + &2)))
  | .zeroAdd => ∀' (((0 : Language.field.Term _) + &0) =' &0)
  | .addLeftNeg => ∀' ∀' ((-&0 + &0) =' 0)
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .mulComm => ∀' ∀' ((&0 * &1) =' (&1 * &0))
  | .oneMul => ∀' (((1 : Language.field.Term _) * &0) =' &0)
  | .mulInvCancel => ∀' (∼(&0 =' 0) ⟹ ((&0 * (&0)⁻¹) =' 1))
  | .invZero => ((0 : Language.field.Term _)⁻¹ =' 0)
  | .leftDistrib => ∀' ∀' ∀' ((&0 * (&1 + &2)) =' ((&0 * &1) + (&0 * &2)))
  | .existsPairNe => ∃' ∃' (∼(&0 =' &1))

@[simp, reducible]
def FieldAxiom.toProp (M : Type _) [Add M] [Mul M] [Neg M] [Inv M] [Zero M] [One M] :
    FieldAxiom → Prop
  | .addAssoc => ∀ x y z : M, (x + y) + z = x + (y + z)
  | .zeroAdd => ∀ x : M, 0 + x = x
  | .addLeftNeg => ∀ x : M, -x + x = 0
  | .mulAssoc => ∀ x y z : M, (x * y) * z = x * (y * z)
  | .mulComm => ∀ x y : M, x * y = y * x
  | .oneMul => ∀ x : M, 1 * x = x
  | .mulInvCancel => ∀ x : M, x ≠ 0 → x * x⁻¹ = 1
  | .invZero => (0 : M)⁻¹ = 0
  | .leftDistrib => ∀ x y z : M, x * (y + z) = x * y + x * z
  | .existsPairNe => ∃ x y : M, x ≠ y

theorem FieldAxiom.realize_toSentence_iff_toProp {K : Type _}
  [Add K] [Mul K] [Neg K] [Inv K] [Zero K] [One K] [Language.field.Structure K]
  (ax : FieldAxiom)
  (funMap_add : ∀ x : Fin 2 → K, funMap addFunction x = x 0 + x 1 := by assumption)
  (funMap_mul : ∀ x : Fin 2 → K, funMap mulFunction x = x 0 * x 1 := by assumption)
  (funMap_neg : ∀ x : Fin 1 → K, funMap negFunction x = -x 0 := by assumption)
  (funMap_inv : ∀ x : Fin 1 → K, funMap invFunction x = (x 0)⁻¹ := by assumption)
  (funMap_zero : ∀ x : Fin 0 → K, funMap (zeroFunction : Language.field.Constants) x = 0
    := by assumption)
  (funMap_one : ∀ x : Fin 0 → K, funMap (oneFunction : Language.field.Constants) x = 1
    := by assumption) :
  (K ⊨ (ax.toSentence : Sentence Language.field)) ↔ ax.toProp K := by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, toProp, Fin.snoc, constantMap,
    add_def, mul_def, neg_def, inv_def, zero_def, one_def,
    funMap_add, funMap_mul, funMap_neg, funMap_inv, funMap_zero, funMap_one]

def Theory.field : Language.field.Theory :=
  Set.range FieldAxiom.toSentence

class CompatibleField (K : Type _) extends Field K,
    Language.field.Structure K where
  ( funMap_add : ∀ x, funMap addFunction x = x 0 + x 1 )
  ( funMap_mul : ∀ x, funMap mulFunction x = x 0 * x 1 )
  ( funMap_neg : ∀ x, funMap negFunction x = -x 0 )
  ( funMap_inv : ∀ x, funMap invFunction x = (x 0)⁻¹ )
  ( funMap_zero : ∀ x, funMap (zeroFunction : Language.field.Constants) x = 0 )
  ( funMap_one : ∀ x, funMap (oneFunction : Language.field.Constants) x = 1 )

open FieldAxiom

attribute [simp] CompatibleField.funMap_add
attribute [simp] CompatibleField.funMap_mul
attribute [simp] CompatibleField.funMap_neg
attribute [simp] CompatibleField.funMap_inv
attribute [simp] CompatibleField.funMap_zero
attribute [simp] CompatibleField.funMap_one

set_option maxHeartbeats 1000000 in
def compatibleFieldOfFieldStructure (K : Type _) [Language.field.Structure K]
    [Theory.field.Model K] : CompatibleField K :=
  letI : Add K := ⟨fun x y => funMap addFunction ![x, y]⟩
  letI : Mul K := ⟨fun x y => funMap mulFunction ![x, y]⟩
  letI : Neg K := ⟨fun x => funMap negFunction ![x]⟩
  letI : Inv K := ⟨fun x => funMap invFunction ![x]⟩
  letI : Zero K := ⟨funMap zeroFunction ![]⟩
  letI : One K := ⟨funMap oneFunction ![]⟩
  have funMap_add : ∀ x : Fin 2 → K, funMap addFunction x = x 0 + x 1 := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  have funMap_mul : ∀ x : Fin 2 → K, funMap mulFunction x = x 0 * x 1 := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  have funMap_neg : ∀ x : Fin 1 → K, funMap negFunction x = -x 0 := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  have funMap_inv : ∀ x : Fin 1 → K, funMap invFunction x = (x 0)⁻¹ := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  have funMap_zero : ∀ x : Fin 0 → K, funMap (zeroFunction : Language.field.Constants) x = 0 := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  have funMap_one : ∀ x : Fin 0 → K, funMap (oneFunction : Language.field.Constants) x = 1 := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  letI : Field K :=
    Field.ofMinimalAxioms K
      (FieldAxiom.addAssoc.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.addAssoc)))
      (FieldAxiom.zeroAdd.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.zeroAdd)))
      (FieldAxiom.addLeftNeg.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.addLeftNeg)))
      (FieldAxiom.mulAssoc.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.mulAssoc)))
      (FieldAxiom.mulComm.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.mulComm)))
      (FieldAxiom.oneMul.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.oneMul)))
      (FieldAxiom.mulInvCancel.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.mulInvCancel)))
      (FieldAxiom.invZero.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.invZero)))
      (FieldAxiom.leftDistrib.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.leftDistrib)))
      (FieldAxiom.existsPairNe.realize_toSentence_iff_toProp.1
        (Theory.realize_sentence_of_mem Theory.field (Set.mem_range_self FieldAxiom.existsPairNe)))
  { funMap_add := funMap_add
    funMap_mul := funMap_mul
    funMap_neg := funMap_neg
    funMap_inv := funMap_inv
    funMap_zero := funMap_zero
    funMap_one := funMap_one }

open FieldFunctions

@[simps, reducible]
def structureFieldOfField {K : Type _} [Field K] : Language.field.Structure K :=
  { funMap := fun {n} f =>
      match n, f with
      | _, add => fun x => x 0 + x 1
      | _, mul => fun x => x 0 * x 1
      | _, neg => fun x => - x 0
      | _, inv => fun x => (x 0)⁻¹
      | _, zero => fun _ => 0
      | _, one => fun _ => 1,
    RelMap := Empty.elim }

def compatibleFieldOfField (K : Type _) [Field K] : CompatibleField K :=
  { structureFieldOfField with
    funMap_add := by intros; rfl
    funMap_mul := by intros; rfl
    funMap_neg := by intros; rfl
    funMap_inv := by intros; rfl
    funMap_zero := by intros; rfl
    funMap_one := by intros; rfl }

instance {K : Type _} [CompatibleField K] : Theory.field.Model K :=
  { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)
        CompatibleField.funMap_add
        CompatibleField.funMap_mul
        CompatibleField.funMap_neg
        CompatibleField.funMap_inv
        CompatibleField.funMap_zero
        CompatibleField.funMap_one]
      cases a with
      | existsPairNe => exact ⟨0, 1, zero_ne_one⟩
      | mulInvCancel => exact fun x => mul_inv_cancel
      | addAssoc => exact add_assoc
      | zeroAdd => exact zero_add
      | addLeftNeg => exact add_left_neg
      | mulAssoc => exact mul_assoc
      | mulComm => exact mul_comm
      | oneMul => exact one_mul
      | invZero => exact inv_zero
      | leftDistrib => exact fun x y z => left_distrib x y z }

@[simps]
def languageHomEquivRingHom {K L : Type _} [CompatibleField K] [CompatibleField L] :
    (K →+* L) ≃ (Language.field.Hom K L) :=
  { toFun := fun f =>
    { f with
      map_fun' := fun {n} f => by
        cases f <;> simp
      map_rel' := fun {n} f => by cases f },
    invFun := fun f =>
      { f with
        map_add' := by
          intro x y
          simpa using f.map_fun addFunction ![x, y]
        map_mul' := by
          intro x y
          simpa using f.map_fun mulFunction ![x, y],
        map_zero' := by
          simpa using f.map_fun zeroFunction ![],
        map_one' := by
          simpa using f.map_fun oneFunction ![], }
    left_inv := fun f => by ext; rfl
    right_inv := fun f => by ext; rfl }

def languageEquivEquivRingEquiv {K L : Type _} [CompatibleField K] [CompatibleField L] :
    (K ≃+* L) ≃ (Language.field.Equiv K L) :=
  { toFun := fun f =>
    { f with
      map_fun' := fun {n} f => by
        cases f <;> simp
      map_rel' := fun {n} f => by cases f },
    invFun := fun f =>
    { f with
      map_add' := by
        intro x y
        simpa using f.map_fun addFunction ![x, y]
      map_mul' := by
        intro x y
        simpa using f.map_fun mulFunction ![x, y] }
    left_inv := fun f => by ext; rfl
    right_inv := fun f => by ext; rfl }

end FirstOrder
