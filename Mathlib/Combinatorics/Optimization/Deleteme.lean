import Mathlib.Combinatorics.Optimization.ValuedCSP
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Cases
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Tuple.Curry



def valuedCspTermOfUnary {D C : Type} [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate D C} {ι : Type*} {f : D → C}
    (ok : ⟨1, Function.OfArity.uncurry f⟩ ∈ Γ) (i : ι) : ValuedCspTerm Γ ι :=
  ⟨1, Function.OfArity.uncurry f, ok, ![i]⟩

def valuedCspTermOfBinary {D C : Type} [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate D C} {ι : Type*} {f : D → D → C}
    (ok : ⟨2, Function.OfArity.uncurry f⟩ ∈ Γ) (i j : ι) : ValuedCspTerm Γ ι :=
  ⟨2, Function.OfArity.uncurry f, ok, ![i, j]⟩




-- Example: minimize |x| + |y| where x and y are rational numbers

private def absRat : (Fin 1 → ℚ) → ℚ := Function.OfArity.uncurry Abs.abs

private def exampleAbs : Σ (n : ℕ), (Fin n → ℚ) → ℚ := ⟨1, absRat⟩

private def exampleFiniteValuedCsp : ValuedCspTemplate ℚ ℚ := {exampleAbs}

private lemma abs_in : ⟨1, absRat⟩ ∈ exampleFiniteValuedCsp := rfl

private def exampleFiniteValuedInstance : ValuedCspInstance exampleFiniteValuedCsp (Fin 2) :=
  [valuedCspTermOfUnary abs_in 0, valuedCspTermOfUnary abs_in 1]

#eval exampleFiniteValuedInstance.evalSolution ![(3 : ℚ), (-2 : ℚ)]

example : exampleFiniteValuedInstance.OptimumSolution ![(0 : ℚ), (0 : ℚ)] := by
  unfold ValuedCspInstance.OptimumSolution
  unfold exampleFiniteValuedCsp
  intro s
  convert_to 0 ≤ ValuedCspInstance.evalSolution exampleFiniteValuedInstance s
  rw [ValuedCspInstance.evalSolution, exampleFiniteValuedInstance,
      List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons, List.sum_nil,
      add_zero]
  show 0 ≤ |s 0| + |s 1|
  positivity



private def Bool_add_le_add_left (a b : Bool) :
  (a = false ∨ b = true) → ∀ (c : Bool), (((c || a) = false) ∨ ((c || b) = true)) :=
by simp

-- Upside down !!
instance crispCodomain : LinearOrderedAddCommMonoid Bool where
  __ := Bool.linearOrder
  add (a b : Bool) := a || b
  add_assoc := Bool.or_assoc
  zero := false
  zero_add (_ : Bool) := rfl
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  add_le_add_left := Bool_add_le_add_left

-- Example: B ≠ A ≠ C ≠ D ≠ B ≠ C with three available labels (i.e., 3-coloring of K₄⁻)

private def beqBool : (Fin 2 → Fin 3) → Bool := Function.OfArity.uncurry BEq.beq

private def exampleEquality : Σ (n : ℕ), (Fin n → Fin 3) → Bool := ⟨2, beqBool⟩

private def exampleCrispCsp : ValuedCspTemplate (Fin 3) Bool := {exampleEquality}

private lemma beq_in : ⟨2, beqBool⟩ ∈ exampleCrispCsp := rfl

private def exampleTermAB : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTermOfBinary beq_in 0 1

private def exampleTermBC : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTermOfBinary beq_in 1 2

private def exampleTermCA : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTermOfBinary beq_in 2 0

private def exampleTermBD : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTermOfBinary beq_in 1 3

private def exampleTermCD : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTermOfBinary beq_in 2 3

private def exampleCrispCspInstance : ValuedCspInstance exampleCrispCsp (Fin 4) :=
  [exampleTermAB, exampleTermBC, exampleTermCA, exampleTermBD, exampleTermCD]

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

#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect0 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect1 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect2 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect3 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect4 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect5 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect0 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect1 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect2 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect3 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect4 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect5 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect6 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect7 -- `true` means WRONG here

example : exampleCrispCspInstance.OptimumSolution exampleSolutionCorrect0 := by
  intro _
  apply Bool.false_le





-- What kind of infinite sets of functions can appear in `Γ.F` ...
example : Set ((Fin 5 → Fin 2) → ℕ) :=
  { f | ∃ (m n k : ℕ),
        f = (fun x => 10 * m + 8 * n + (if x 0 = x 1 then 1 else 0) * k) }
