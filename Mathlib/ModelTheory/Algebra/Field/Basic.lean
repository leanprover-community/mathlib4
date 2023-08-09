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
  | addComm : FieldAxiom
  | zeroAdd : FieldAxiom
  | addZero : FieldAxiom
  | addLeftNeg : FieldAxiom
  | addRightNeg : FieldAxiom
  | mulLeftDistrib : FieldAxiom
  | mulRightDistrib : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | mulOne : FieldAxiom
  | mulRightInv : FieldAxiom
  | invZero : FieldAxiom
  | zeroNeOne : FieldAxiom

@[simp]
def FieldAxiom.toSentence : FieldAxiom → Language.field.Sentence
  | .addAssoc => addFunction.assoc
  | .addComm => addFunction.comm
  | .zeroAdd => addFunction.leftId zeroFunction
  | .addZero => addFunction.rightId zeroFunction
  | .addLeftNeg => addFunction.leftInv negFunction zeroFunction
  | .addRightNeg => addFunction.rightInv negFunction zeroFunction
  | .mulLeftDistrib => mulFunction.leftDistrib addFunction
  | .mulRightDistrib => mulFunction.rightDistrib addFunction
  | .mulAssoc => mulFunction.assoc
  | .mulComm => mulFunction.comm
  | .oneMul => mulFunction.leftId oneFunction
  | .mulOne => mulFunction.rightId oneFunction
  | .mulRightInv => mulFunction.rightNeZeroInv invFunction zeroFunction oneFunction
  | .invZero => invFunction.apply₁ 0 =' 0
  | .zeroNeOne => (Term.equal 0 1).not

def Theory.field : Language.field.Theory :=
  Set.range FieldAxiom.toSentence

class ModelField (K : Type _) extends Field K,
    Language.field.Structure K where
  ( funMap_add : ∀ x, funMap addFunction x = x 0 + x 1 )
  ( funMap_mul : ∀ x, funMap mulFunction x = x 0 * x 1 )
  ( funMap_neg : ∀ x, funMap negFunction x = -x 0 )
  ( funMap_inv : ∀ x, funMap invFunction x = (x 0)⁻¹ )
  ( funMap_zero : ∀ x, funMap (zeroFunction : Language.field.Constants) x = 0 )
  ( funMap_one : ∀ x, funMap (oneFunction : Language.field.Constants) x = 1 )

open FieldAxiom

attribute [simp] ModelField.funMap_add ModelField.funMap_mul
  ModelField.funMap_neg ModelField.funMap_inv
  ModelField.funMap_zero ModelField.funMap_one

set_option maxHeartbeats 1000000 in
def modelFieldOfFieldStructure (K : Type _) [Language.field.Structure K]
    [Theory.field.Model K] : ModelField K :=
{ add := fun x y => funMap addFunction ![x, y],
  zero := constantMap (L := Language.field) (M := K) zeroFunction,
  one := constantMap (L := Language.field) (M := K) oneFunction,
  mul := fun x y => funMap mulFunction ![x, y],
  inv := fun x => funMap invFunction ![x],
  neg := fun x => funMap negFunction ![x],
  add_assoc := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .addAssoc)
    rwa [toSentence, Functions.realize_assoc] at h
  add_comm := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .addComm)
    rwa [toSentence, Functions.realize_comm] at h
  add_zero := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .addZero)
    rwa [toSentence, Functions.realize_rightId] at h
  add_left_neg := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .addLeftNeg)
    rwa [toSentence, Functions.realize_leftInv] at h
  left_distrib := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .mulLeftDistrib)
    rwa [toSentence, Functions.realize_leftDistrib] at h
  right_distrib := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .mulRightDistrib)
    rwa [toSentence, Functions.realize_rightDistrib] at h
  mul_assoc := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .mulAssoc)
    rwa [toSentence, Functions.realize_assoc] at h
  mul_comm := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .mulComm)
    rwa [toSentence, Functions.realize_comm] at h
  mul_one := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .mulOne)
    rwa [toSentence, Functions.realize_rightId] at h
  zero_add := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .zeroAdd)
    rwa [toSentence, Functions.realize_leftId] at h
  zero_mul := sorry,
  mul_zero := sorry,
  one_mul := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .oneMul)
    rwa [toSentence, Functions.realize_leftId] at h
  exists_pair_ne := ⟨
    constantMap (L := Language.field) (M := K) zeroFunction,
    constantMap (L := Language.field) (M := K) oneFunction, by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .zeroNeOne)
    simpa [Sentence.Realize, zero_def, one_def] using h⟩
  mul_inv_cancel := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .mulRightInv)
    rwa [toSentence, Functions.realize_rightNeZeroInv] at h
  inv_zero := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (Set.mem_range_self (f := toSentence) .invZero)
    simpa [Sentence.Realize, zero_def, funMap, Formula.Realize] using h,
  funMap_add := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  funMap_mul := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  funMap_neg := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  funMap_inv := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  funMap_zero := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl
  funMap_one := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
    intros; rfl }

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

def modelFieldOfField (K : Type _) [Field K] : ModelField K :=
  { structureFieldOfField with
    funMap_add := by intros; rfl
    funMap_mul := by intros; rfl
    funMap_neg := by intros; rfl
    funMap_inv := by intros; rfl
    funMap_zero := by intros; rfl
    funMap_one := by intros; rfl }

instance {K : Type _} [ModelField K] : Theory.field.Model K :=
  { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      have := @mul_inv_cancel (G₀ := K) _
      cases a <;>
      simp [toSentence, add_assoc, add_comm, constantMap, mul_comm,
        mul_assoc, add_left_comm, mul_left_comm, mul_add, add_mul] <;>
      simp [Sentence.Realize, Formula.Realize, zero_def, one_def,
        constantMap, Term.equal];
      assumption }

@[simps]
def languageHomEquivRingHom {K L : Type _} [ModelField K] [ModelField L] :
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

def languageEquivEquivRingEquiv {K L : Type _} [ModelField K] [ModelField L] :
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
