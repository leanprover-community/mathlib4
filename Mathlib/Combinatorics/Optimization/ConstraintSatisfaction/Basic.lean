/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.BigOperators.Fin

/-!

# General-Valued Constraint Satisfaction Problems

General-Valued CSP is a very broad class of problems in discrete optimization.
General-Valued CSP subsumes Min-Cost-Hom (including 3-SAT for example) and Finite-Valued CSP.

## Main definitions
* `ValuedCSP`: A VCSP template; fixes a domain, a codomain, and allowed cost functions.
* `ValuedCSP.Term`: One summand in a VCSP instance; calls a concrete function from given template.
* `ValuedCSP.Term.evalSolution`: An evaluation of the VCSP term for given solution.
* `ValuedCSP.Instance`: An instance of a VCSP problem over given template.
* `ValuedCSP.Instance.evalSolution`: An evaluation of the VCSP instance for given solution.
* `ValuedCSP.Instance.IsOptimumSolution`: Is given solution a minimum of the VCSP instance?
* `Function.HasMaxCutProperty`: Can given binary function express the Max-Cut problem?
* `FractionalOperation`: Multiset of operations on given domain of the same arity.
* `FractionalOperation.IsSymmetricFractionalPolymorphismFor`: Is given fractional operation a
   symmetric fractional polymorphism for given VCSP template?

## References
* [D. A. Cohen, M. C. Cooper, P. Creed, P. G. Jeavons, S. Živný,
   *An Algebraic Theory of Complexity for Discrete Optimisation*][cohen2012]

-/

/-- A template for a valued CSP problem over a domain `D` with costs in `C`.
Regarding `C` we want to support `Bool`, `Nat`, `ENat`, `Int`, `Rat`, `NNRat`,
`Real`, `NNReal`, `EReal`, `ENNReal`, and tuples made of any of those types. -/
@[nolint unusedArguments]
abbrev ValuedCSP (D C : Type*) [OrderedAddCommMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → C) -- Cost functions `D^n → C` for any `n`

variable {D C : Type*} [OrderedAddCommMonoid C]

/-- A term in a valued CSP instance over the template `Γ`. -/
structure ValuedCSP.Term (Γ : ValuedCSP D C) (ι : Type*) where
  /-- Arity of the function -/
  n : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin n → D) → C
  /-- The cost function comes from the template -/
  inΓ : ⟨n, f⟩ ∈ Γ
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin n → ι

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
def ValuedCSP.Term.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (t : Γ.Term ι) (x : ι → D) : C :=
  t.f (x ∘ t.app)

/-- A valued CSP instance over the template `Γ` with variables indexed by `ι`. -/
abbrev ValuedCSP.Instance (Γ : ValuedCSP D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def ValuedCSP.Instance.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : C :=
  (I.map (·.evalSolution x)).sum

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`. -/
def ValuedCSP.Instance.IsOptimumSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Prop :=
  ∀ y : ι → D, I.evalSolution x ≤ I.evalSolution y

/-- Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exactly
`{ ![a, b] , ![b, a] }`. -/
def Function.HasMaxCutPropertyAt (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
    ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

/-- Fractional operation is a finite unordered collection of D^m → D possibly with duplicates. -/
abbrev FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset ((Fin m → D) → D)

variable {m : ℕ}

/-- Arity of the "output" of the fractional operation. -/
@[simp]
def FractionalOperation.size (ω : FractionalOperation D m) : ℕ :=
  Multiset.card.toFun ω

/-- Fractional operation is valid iff nonempty. -/
def FractionalOperation.IsValid (ω : FractionalOperation D m) : Prop :=
  ω ≠ ∅

/-- Valid fractional operation contains an operation. -/
lemma FractionalOperation.IsValid.contains {ω : FractionalOperation D m} (valid : ω.IsValid) :
    ∃ g : (Fin m → D) → D, g ∈ ω :=
  Multiset.exists_mem_of_ne_zero valid

/-- Fractional operation applied to a transposed table of values. -/
def FractionalOperation.tt {ι : Type*} (ω : FractionalOperation D m) (x : Fin m → ι → D) :
    Multiset (ι → D) :=
  ω.map (fun (g : (Fin m → D) → D) (i : ι) => g ((Function.swap x) i))

/-- Cost function admits given fractional operation, i.e., `ω` improves `f` in the `≤` sense. -/
def Function.AdmitsFractional {n : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map f).sum ≤ ω.size • Finset.univ.sum (fun i => f (x i))

/-- Fractional operation is a fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- Fractional operation is symmetric. -/
def FractionalOperation.IsSymmetric (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.Perm (List.ofFn x) (List.ofFn y) → ∀ g ∈ ω, g x = g y

/-- Fractional operation is a symmetric fractional polymorphism for given VCSP template. -/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric
