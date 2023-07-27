import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

protected def field : Language :=
Language.mk₂ Bool Bool Bool Empty Empty

namespace field

instance : Zero Language.field.Constants := ⟨false⟩

instance : One Language.field.Constants := ⟨true⟩

def addFunction : Language.field.Functions 2 := false

def mulFunction : Language.field.Functions 2 := true

def negFunction : Language.field.Functions 1 := false

def invFunction : Language.field.Functions 1 := true

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

open BoundedFormula

def Theory.field : Language.field.Theory :=
show Set Language.field.Sentence from
{ addFunction.assoc,
  addFunction.comm,
  addFunction.leftId 0,
  addFunction.rightId 0,
  addFunction.leftInv negFunction 0,
  addFunction.rightInv negFunction 0,
  mulFunction.leftDistrib addFunction,
  mulFunction.rightDistrib addFunction,
  mulFunction.assoc,
  mulFunction.comm,
  mulFunction.leftId 1,
  mulFunction.rightId 1,
  mulFunction.leftNeZeroInv invFunction 0 1,
  mulFunction.rightNeZeroInv invFunction 0 1,
  invFunction.apply₁ 0 =' 0,
  (Term.equal 0 1).not}

set_option maxHeartbeats 20000000 in
def fieldOfModelField {K : Type _} [Language.field.Structure K]
    [Theory.field.Model K] : Field K :=
{ add := fun x y => funMap addFunction ![x, y],
  zero := constantMap (L := Language.field) (M := K) 0,
  one := constantMap (L := Language.field) (M := K) 1,
  mul := fun x y => funMap mulFunction ![x, y],
  inv := fun x => funMap invFunction ![x],
  neg := fun x => funMap negFunction ![x],
  add_assoc := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.assoc ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_assoc] at h
  add_comm := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.comm ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_comm] at h
  add_zero := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.rightId 0 ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_rightId] at h
  add_left_neg := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.leftInv negFunction 0 ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_leftInv] at h
  left_distrib := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.leftDistrib addFunction ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_leftDistrib] at h
  right_distrib := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.rightDistrib addFunction ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_rightDistrib] at h
  mul_assoc := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.assoc ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_assoc] at h
  mul_comm := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.comm ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_comm] at h
  mul_one := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.rightId 1 ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_rightId] at h
  zero_add := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show addFunction.leftId 0 ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_leftId] at h
  zero_mul := sorry,
  mul_zero := sorry,
  one_mul := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.leftId 1 ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_leftId] at h
  exists_pair_ne := ⟨
    constantMap (L := Language.field) (M := K) 0,
    constantMap (L := Language.field) (M := K) 1, by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show (Term.equal 0 1).not ∈ Theory.field by simp [Theory.field])
    simpa [Sentence.Realize, zero_def, one_def] using h⟩
  mul_inv_cancel := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show mulFunction.rightNeZeroInv invFunction 0 1 ∈ Theory.field by simp [Theory.field])
    rwa [Functions.realize_rightNeZeroInv] at h
  inv_zero := by
    have h := Theory.field.realize_sentence_of_mem (M := K)
      (show invFunction.apply₁ 0 =' 0 ∈ Theory.field by simp [Theory.field])
    simpa [Sentence.Realize, zero_def, funMap, Formula.Realize] using h }

end field

end Language

end FirstOrder
