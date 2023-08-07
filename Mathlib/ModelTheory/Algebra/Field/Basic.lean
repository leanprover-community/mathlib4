import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Algebra.Ring.Basic

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

inductive FieldFunctions : ℕ → Type
  | add : FieldFunctions 2
  | mul : FieldFunctions 2
  | neg : FieldFunctions 1
  | inv : FieldFunctions 1
  | zero : FieldFunctions 0
  | one : FieldFunctions 0

protected def field : Language :=
  { Functions := FieldFunctions
    Relations := fun _ => Empty }

namespace field

open FieldFunctions

instance : Zero Language.field.Constants := ⟨zero⟩

instance : One Language.field.Constants := ⟨one⟩

abbrev addFunction : Language.field.Functions 2 := add

abbrev mulFunction : Language.field.Functions 2 := mul

abbrev negFunction : Language.field.Functions 1 := neg

abbrev invFunction : Language.field.Functions 1 := inv

instance (α : Type _) : Zero (Language.field.Term α) :=
{ zero := Constants.term 0 }

theorem zero_def (α : Type _) : (0 : Language.field.Term α) = Constants.term 0 := rfl

instance (α : Type _) : One (Language.field.Term α) :=
{ one := Constants.term 1 }

theorem one_def (α : Type _) : (1 : Language.field.Term α) = Constants.term 1 := rfl

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

end field

open field

open BoundedFormula

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

def FieldAxiom.toSentence : FieldAxiom → Language.field.Sentence
  | .addAssoc => addFunction.assoc
  | .addComm => addFunction.comm
  | .zeroAdd => addFunction.leftId 0
  | .addZero => addFunction.rightId 0
  | .addLeftNeg => addFunction.leftInv negFunction 0
  | .addRightNeg => addFunction.rightInv negFunction 0
  | .mulLeftDistrib => mulFunction.leftDistrib addFunction
  | .mulRightDistrib => mulFunction.rightDistrib addFunction
  | .mulAssoc => mulFunction.assoc
  | .mulComm => mulFunction.comm
  | .oneMul => mulFunction.leftId 1
  | .mulOne => mulFunction.rightId 1
  | .mulRightInv => mulFunction.rightNeZeroInv invFunction 0 1
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
  ( funMap_zero : ∀ x, funMap (0 : Language.field.Constants) x = 0 )
  ( funMap_one : ∀ x, funMap (1 : Language.field.Constants) x = 1 )

open FieldAxiom
attribute [simp] ModelField.funMap_add ModelField.funMap_mul
  ModelField.funMap_neg ModelField.funMap_inv
  ModelField.funMap_zero ModelField.funMap_one

set_option maxHeartbeats 1000000 in
def ModelFieldOfFieldStructure (K : Type _) [Language.field.Structure K]
    [Theory.field.Model K] : ModelField K :=
{ add := fun x y => funMap addFunction ![x, y],
  zero := constantMap (L := Language.field) (M := K) 0,
  one := constantMap (L := Language.field) (M := K) 1,
  mul := fun x y => funMap mulFunction ![x, y],
  inv := fun x => funMap invFunction ![x],
  neg := fun x => funMap negFunction ![x],
  add_assoc := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.assoc ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .addAssoc)
    rwa [Functions.realize_assoc] at h
  add_comm := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.comm ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .addComm)
    rwa [Functions.realize_comm] at h
  add_zero := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.rightId 0 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .addZero)
    rwa [Functions.realize_rightId] at h
  add_left_neg := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.leftInv negFunction 0 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .addLeftNeg)
    rwa [Functions.realize_leftInv] at h
  left_distrib := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.leftDistrib addFunction ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .mulLeftDistrib)
    rwa [Functions.realize_leftDistrib] at h
  right_distrib := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.rightDistrib addFunction ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .mulRightDistrib)
    rwa [Functions.realize_rightDistrib] at h
  mul_assoc := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.assoc ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .mulAssoc)
    rwa [Functions.realize_assoc] at h
  mul_comm := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.comm ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .mulComm)
    rwa [Functions.realize_comm] at h
  mul_one := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.rightId 1 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .mulOne)
    rwa [Functions.realize_rightId] at h
  zero_add := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.leftId 0 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .zeroAdd)
    rwa [Functions.realize_leftId] at h
  zero_mul := sorry,
  mul_zero := sorry,
  one_mul := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.leftId 1 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .oneMul)
    rwa [Functions.realize_leftId] at h
  exists_pair_ne := ⟨
    constantMap (L := Language.field) (M := K) 0,
    constantMap (L := Language.field) (M := K) 1, by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show (Term.equal 0 1).not ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .zeroNeOne)
    simpa [Sentence.Realize, zero_def, one_def] using h⟩
  mul_inv_cancel := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.rightNeZeroInv invFunction 0 1 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .mulRightInv)
    rwa [Functions.realize_rightNeZeroInv] at h
  inv_zero := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show invFunction.apply₁ 0 =' 0 ∈ Theory.field from
        Set.mem_range_self (f := toSentence) .invZero)
    simpa [Sentence.Realize, zero_def, funMap, Formula.Realize] using h,
  funMap_add := by
    simp [Fin.forall_fin_succ_pi, HAdd.hAdd, Matrix.vecCons];
    intros; rfl
  funMap_mul := by
    simp [Fin.forall_fin_succ_pi, HAdd.hAdd, Matrix.vecCons];
    intros; rfl
  funMap_neg := by
    simp [Fin.forall_fin_succ_pi, HAdd.hAdd, Matrix.vecCons];
    intros; rfl
  funMap_inv := by
    simp [Fin.forall_fin_succ_pi, HAdd.hAdd, Matrix.vecCons];
    intros; rfl
  funMap_zero := by
    simp [Fin.forall_fin_succ_pi, HAdd.hAdd, Matrix.vecCons];
    intros; rfl
  funMap_one := by
    simp [Fin.forall_fin_succ_pi, HAdd.hAdd, Matrix.vecCons];
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

def ModelFieldOfField {K : Type _} [Field K] : ModelField K :=
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

end Language

end FirstOrder
