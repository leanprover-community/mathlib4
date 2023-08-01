import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

inductive RingFunctions : ℕ → Type
  | add : RingFunctions 2
  | mul : RingFunctions 2
  | neg : RingFunctions 1
  | zero : RingFunctions 0
  | one : RingFunctions 0

protected def ring : Language :=
  { Functions := RingFunctions
    Relations := fun _ => Empty }

namespace ring

open RingFunctions

instance : Zero Language.ring.Constants := ⟨zero⟩

instance : One Language.ring.Constants := ⟨one⟩

abbrev addFunction : Language.ring.Functions 2 := add

abbrev mulFunction : Language.ring.Functions 2 := mul

abbrev negFunction : Language.ring.Functions 1 := neg

instance (α : Type _) : Zero (Language.ring.Term α) :=
{ zero := Constants.term 0 }

theorem zero_def (α : Type _) : (0 : Language.ring.Term α) = Constants.term 0 := rfl

instance (α : Type _) : One (Language.ring.Term α) :=
{ one := Constants.term 1 }

theorem one_def (α : Type _) : (1 : Language.ring.Term α) = Constants.term 1 := rfl

instance (α : Type _) : Add (Language.ring.Term α) :=
{ add := addFunction.apply₂ }

theorem add_def (α : Type _) (t₁ t₂ : Language.ring.Term α) :
    t₁ + t₂ = addFunction.apply₂ t₁ t₂ := rfl

instance (α : Type _) : Mul (Language.ring.Term α) :=
{ mul := mulFunction.apply₂ }

theorem mul_def (α : Type _) (t₁ t₂ : Language.ring.Term α) :
    t₁ * t₂ = mulFunction.apply₂ t₁ t₂ := rfl

instance (α : Type _) : Neg (Language.ring.Term α) :=
{ neg := negFunction.apply₁ }

theorem neg_def (α : Type _) (t : Language.ring.Term α) :
    -t = negFunction.apply₁ t := rfl

end ring
