/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Order -- will be trimmed after deleting examples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Mathlib.Data.Bool.Basic

/-!

# General-Valued Constraint Satisfaction Problems

General-Valued CSP is a very broad class of problems in discrete optimization.
General-Valued CSP subsumes Min-Cost-Hom (including 3-SAT for example) and Finite-Valued CSP.

## Main definitions
* `ValuedCspTemplate`: A VCSP template; specifies domain, codomain, and allowed cost functions.
* `ValuedCspTerm`: One summand in a VCSP instance; calls a concrete function from given template.
* `ValuedCspTerm.evalSolution`: An evaluation of the VCSP term for given solution.
* `ValuedCspInstance`: An instance of a VCSP problem over given template.
* `ValuedCspInstance.evalSolution`: An evaluation of the VCSP instance for given solution.
* `ValuedCspInstance.optimumSolution`: Is given solution a minimum of the VCSP instance?

## References
* [D. A. Cohen, M. C. Cooper, P. Creed, P. G. Jeavons, S. Živný,
   *An Algebraic Theory of Complexity for Discrete Optimisation*][cohen2012]

-/

def n1ary_of_unary {α β : Type _} (f : α → β) : (Fin 1 → α) → β :=
  fun a => f (a 0)

def n2ary_of_binary {α β : Type _} (f : α → α → β) : (Fin 2 → α) → β :=
  fun a => f (a 0) (a 1)

/-- A template for a valued CSP problem with costs in `C`. -/
structure ValuedCspTemplate (C : Type _) [LinearOrderedAddCommMonoid C] where
  /-- Domain of "labels" -/
  D : Type
  /-- Cost functions from `D^k` to `C` for any `k` -/
  F : Set (Σ (k : ℕ), (Fin k → D) → C)

variable {C : Type _} [LinearOrderedAddCommMonoid C]

/-- A term in a valued CSP instance over the template `Γ`. -/
structure ValuedCspTerm (Γ : ValuedCspTemplate C) (ι : Type _) where
  /-- Arity of the function -/
  k : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin k → Γ.D) → C
  /-- The cost function comes from the template -/
  inΓ : ⟨k, f⟩ ∈ Γ.F
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin k → ι

def valuedCspTerm_of_unary {Γ : ValuedCspTemplate C} {ι : Type _} {f₁ : Γ.D → C}
    (ok : ⟨1, n1ary_of_unary f₁⟩ ∈ Γ.F) (i : ι) : ValuedCspTerm Γ ι :=
  ⟨1, n1ary_of_unary f₁, ok, ![i]⟩

def valuedCspTerm_of_binary {Γ : ValuedCspTemplate C} {ι : Type _} {f₂ : Γ.D → Γ.D → C}
    (ok : ⟨2, n2ary_of_binary f₂⟩ ∈ Γ.F) (i j : ι) : ValuedCspTerm Γ ι :=
  ⟨2, n2ary_of_binary f₂, ok, ![i, j]⟩

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
def ValuedCspTerm.evalSolution {Γ : ValuedCspTemplate C} {ι : Type _}
    (t : ValuedCspTerm Γ ι) (x : ι → Γ.D) : C :=
  t.f (x ∘ t.app)

/-- A valued CSP instance over the template `Γ` with variables indexed by `ι`.-/
def ValuedCspInstance (Γ : ValuedCspTemplate C) (ι : Type _) : Type :=
  List (ValuedCspTerm Γ ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def ValuedCspInstance.evalSolution {Γ : ValuedCspTemplate C} {ι : Type _}
    (I : ValuedCspInstance Γ ι) (x : ι → Γ.D) : C :=
  (I.map (fun t => t.evalSolution x)).sum

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`.-/
def ValuedCspInstance.optimumSolution {Γ : ValuedCspTemplate C} {ι : Type _}
    (I : ValuedCspInstance Γ ι) (x : ι → Γ.D) : Prop :=
  ∀ y : ι → Γ.D, I.evalSolution x ≤ I.evalSolution y











-- Example: minimize |x| + |y| where x and y are rational numbers

private def absRat : (Fin 1 → ℚ) → ℚ := @n1ary_of_unary ℚ ℚ Abs.abs

private def exampleAbs : Σ (k : ℕ), (Fin k → ℚ) → ℚ := ⟨1, absRat⟩

private def exampleFiniteValuedCsp : ValuedCspTemplate ℚ :=
  ValuedCspTemplate.mk ℚ {exampleAbs}

private lemma abs_in : ⟨1, absRat⟩ ∈ exampleFiniteValuedCsp.F := rfl

private def exampleFiniteValuedInstance : ValuedCspInstance exampleFiniteValuedCsp (Fin 2) :=
  [valuedCspTerm_of_unary abs_in 0, valuedCspTerm_of_unary abs_in 1]

#eval exampleFiniteValuedInstance.evalSolution ![(3 : ℚ), (-2 : ℚ)]

example : exampleFiniteValuedInstance.optimumSolution ![(0 : ℚ), (0 : ℚ)] := by
  unfold ValuedCspInstance.optimumSolution
  unfold exampleFiniteValuedCsp
  intro s
  convert_to 0 ≤ ValuedCspInstance.evalSolution exampleFiniteValuedInstance s
  rw [ValuedCspInstance.evalSolution, exampleFiniteValuedInstance,
      List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons, List.sum_nil,
      add_zero]
  show 0 ≤ |s 0| + |s 1|
  have s0nn : 0 ≤ |s 0|
  · exact abs_nonneg (s 0)
  have s1nn : 0 ≤ |s 1|
  · exact abs_nonneg (s 1)
  linarith



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

private def beqBool : (Fin 2 → Fin 3) → Bool := n2ary_of_binary BEq.beq

private def exampleEquality : Σ (k : ℕ), (Fin k → Fin 3) → Bool := ⟨2, beqBool⟩

private def exampleCrispCsp : ValuedCspTemplate Bool :=
  ValuedCspTemplate.mk (Fin 3) {exampleEquality}

private lemma beq_in : ⟨2, beqBool⟩ ∈ exampleCrispCsp.F := rfl

private def exampleTermAB : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTerm_of_binary beq_in 0 1

private def exampleTermBC : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTerm_of_binary beq_in 1 2

private def exampleTermCA : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTerm_of_binary beq_in 2 0

private def exampleTermBD : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTerm_of_binary beq_in 1 3

private def exampleTermCD : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  valuedCspTerm_of_binary beq_in 2 3

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

example : exampleCrispCspInstance.optimumSolution exampleSolutionCorrect0 := by
  intro _
  apply Bool.false_le





-- What kind of infinite sets of functions can appear in `Γ.F` ...
example : Set ((Fin 5 → Fin 2) → ℕ) :=
  { f | ∃ (m n k : ℕ),
        f = (fun x => 10 * m + 8 * n + (if x 0 = x 1 then 1 else 0) * k) }
