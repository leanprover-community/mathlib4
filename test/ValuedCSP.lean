import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Curry

/-!
# VCSP examples

This file shows two simple examples of General-Valued Constraint Satisfaction Problems (see
[ValuedCSP definition](Mathlib/Combinatorics/Optimization/ValuedCSP.lean)).
The first example is an optimization problem. The second example is a decision problem.
-/

def ValuedCSP.unaryTerm {D C : Type} [OrderedAddCommMonoid C]
    {Γ : ValuedCSP D C} {ι : Type*} {f : D → C}
    (ok : ⟨1, Function.OfArity.uncurry f⟩ ∈ Γ) (i : ι) : Γ.Term ι :=
  ⟨1, Function.OfArity.uncurry f, ok, ![i]⟩

def ValuedCSP.binaryTerm {D C : Type} [OrderedAddCommMonoid C]
    {Γ : ValuedCSP D C} {ι : Type*} {f : D → D → C}
    (ok : ⟨2, Function.OfArity.uncurry f⟩ ∈ Γ) (i j : ι) : Γ.Term ι :=
  ⟨2, Function.OfArity.uncurry f, ok, ![i, j]⟩

-- ## Example: minimize `|x| + |y|` where `x` and `y` are rational numbers

private def absRat : (Fin 1 → ℚ) → ℚ := Function.OfArity.uncurry abs

private def exampleAbs : Σ (n : ℕ), (Fin n → ℚ) → ℚ := ⟨1, absRat⟩

private def exampleFiniteValuedCSP : ValuedCSP ℚ ℚ := {exampleAbs}

private lemma abs_in : ⟨1, absRat⟩ ∈ exampleFiniteValuedCSP := rfl

private def exampleFiniteValuedInstance : exampleFiniteValuedCSP.Instance (Fin 2) :=
  Multiset.ofList [ValuedCSP.unaryTerm abs_in 0, ValuedCSP.unaryTerm abs_in 1]

example : exampleFiniteValuedInstance.IsOptimumSolution ![(0 : ℚ), (0 : ℚ)] := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  unfold exampleFiniteValuedCSP
  intro s
  convert_to 0 ≤ exampleFiniteValuedInstance.evalSolution s
  rw [ValuedCSP.Instance.evalSolution, exampleFiniteValuedInstance]
  convert_to 0 ≤ |s 0| + |s 1|
  · simp [ValuedCSP.unaryTerm, ValuedCSP.Term.evalSolution, Function.OfArity.uncurry]
  positivity

-- ## Example: `B ≠ A ≠ C ≠ D ≠ B ≠ C` with three available labels (i.e., 3-coloring of K₄⁻)

private def Bool_add_le_add_left (a b : Bool) :
  (a ≤ b) → ∀ (c : Bool), ((c || a) ≤ (c || b)) :=
by
  intro hab c
  cases a <;> cases b <;> cases c <;> trivial

-- For simpler implementation, we treat `false` as "satisfied" and `true` as "wrong" here.
instance crispCodomain : LinearOrderedAddCommMonoid Bool where
  __ := Bool.linearOrder
  add (a b : Bool) := a || b
  add_assoc := Bool.or_assoc
  zero := false
  zero_add (_ : Bool) := rfl
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  add_le_add_left := Bool_add_le_add_left

private def beqBool : (Fin 2 → Fin 3) → Bool := Function.OfArity.uncurry BEq.beq

private def exampleEquality : Σ (n : ℕ), (Fin n → Fin 3) → Bool := ⟨2, beqBool⟩

private def exampleCrispCsp : ValuedCSP (Fin 3) Bool := {exampleEquality}

private lemma beq_in : ⟨2, beqBool⟩ ∈ exampleCrispCsp := rfl

private def exampleTermAB : exampleCrispCsp.Term (Fin 4) :=
  ValuedCSP.binaryTerm beq_in 0 1

private def exampleTermBC : exampleCrispCsp.Term (Fin 4) :=
  ValuedCSP.binaryTerm beq_in 1 2

private def exampleTermCA : exampleCrispCsp.Term (Fin 4) :=
  ValuedCSP.binaryTerm beq_in 2 0

private def exampleTermBD : exampleCrispCsp.Term (Fin 4) :=
  ValuedCSP.binaryTerm beq_in 1 3

private def exampleTermCD : exampleCrispCsp.Term (Fin 4) :=
  ValuedCSP.binaryTerm beq_in 2 3

private def exampleCrispCspInstance : exampleCrispCsp.Instance (Fin 4) :=
  Multiset.ofList [exampleTermAB, exampleTermBC, exampleTermCA, exampleTermBD, exampleTermCD]

private def exampleSolutionCorrect0 : Fin 4 → Fin 3 :=   ![0, 1, 2, 0]
private def exampleSolutionCorrect1 : Fin 4 → Fin 3 :=   ![1, 2, 3, 1]
private def exampleSolutionCorrect2 : Fin 4 → Fin 3 :=   ![2, 0, 1, 2]
private def exampleSolutionCorrect3 : Fin 4 → Fin 3 :=   ![0, 2, 1, 0]
private def exampleSolutionCorrect4 : Fin 4 → Fin 3 :=   ![1, 0, 2, 1]
private def exampleSolutionCorrect5 : Fin 4 → Fin 3 :=   ![1, 0, 2, 1]
private def exampleSolutionIncorrect0 : Fin 4 → Fin 3 := ![0, 0, 0, 0]
private def exampleSolutionIncorrect1 : Fin 4 → Fin 3 := ![1, 0, 0, 0]
private def exampleSolutionIncorrect2 : Fin 4 → Fin 3 := ![0, 2, 0, 0]
private def exampleSolutionIncorrect3 : Fin 4 → Fin 3 := ![0, 1, 0, 2]
private def exampleSolutionIncorrect4 : Fin 4 → Fin 3 := ![2, 2, 0, 1]
private def exampleSolutionIncorrect5 : Fin 4 → Fin 3 := ![0, 1, 2, 1]
private def exampleSolutionIncorrect6 : Fin 4 → Fin 3 := ![1, 0, 0, 1]
private def exampleSolutionIncorrect7 : Fin 4 → Fin 3 := ![2, 2, 0, 2]

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect0 :=
  fun _ => Bool.false_le _

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect1 :=
  fun _ => Bool.false_le _

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect2 :=
  fun _ => Bool.false_le _

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect3 :=
  fun _ => Bool.false_le _

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect4 :=
  fun _ => Bool.false_le _

example : exampleCrispCspInstance.IsOptimumSolution exampleSolutionCorrect5 :=
  fun _ => Bool.false_le _

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect0 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect1 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect2 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect3 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect4 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect5 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect6 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl

example : ¬exampleCrispCspInstance.IsOptimumSolution exampleSolutionIncorrect7 := by
  unfold ValuedCSP.Instance.IsOptimumSolution
  push_neg
  use exampleSolutionCorrect0
  rfl
