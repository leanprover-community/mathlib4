/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators

/-!

# General-Valued Constraint Satisfaction Problems

General-Valued CSP is a very broad class of problems in discrete optimization.
General-Valued CSP subsumes Min-Cost-Hom (including 3-SAT for example) and Finite-Valued CSP.

## Main definitions
* `ValuedCsp`: A VCSP template; fixes a domain, a codomain, and allowed cost functions.
* `ValuedCsp.Term`: One summand in a VCSP instance; calls a concrete function from given template.
* `ValuedCsp.Term.evalSolution`: An evaluation of the VCSP term for given solution.
* `ValuedCsp.Instance`: An instance of a VCSP problem over given template.
* `ValuedCsp.Instance.evalSolution`: An evaluation of the VCSP instance for given solution.
* `ValuedCsp.Instance.IsOptimumSolution`: Is given solution a minimum of the VCSP instance?

## References
* [D. A. Cohen, M. C. Cooper, P. Creed, P. G. Jeavons, S. Živný,
   *An Algebraic Theory of Complexity for Discrete Optimisation*][cohen2012]

-/

/-- A template for a valued CSP problem over a domain `D` with costs in `C`.
Regarding `C` we want to support `Bool`, `Nat`, `ENat`, `Int`, `Rat`, `NNRat`,
`Real`, `NNReal`, `EReal`, `ENNReal`, and tuples made of any of those types. -/
@[reducible, nolint unusedArguments]
def ValuedCsp (D C : Type*) [OrderedAddCommMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → C) -- Cost functions `D^n → C` for any `n`

variable {D C : Type*} [OrderedAddCommMonoid C]

/-- A term in a valued CSP instance over the template `Γ`. -/
structure ValuedCsp.Term (Γ : ValuedCsp D C) (ι : Type*) where
  /-- Arity of the function -/
  n : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin n → D) → C
  /-- The cost function comes from the template -/
  inΓ : ⟨n, f⟩ ∈ Γ
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin n → ι

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
def ValuedCsp.Term.evalSolution {Γ : ValuedCsp D C} {ι : Type*}
    (t : Γ.Term ι) (x : ι → D) : C :=
  t.f (x ∘ t.app)

/-- A valued CSP instance over the template `Γ` with variables indexed by `ι`.-/
def ValuedCsp.Instance (Γ : ValuedCsp D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
def ValuedCsp.Instance.evalSolution {Γ : ValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : C :=
  (I.map (·.evalSolution x)).sum

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`.-/
def ValuedCsp.Instance.IsOptimumSolution {Γ : ValuedCsp D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Prop :=
  ∀ y : ι → D, I.evalSolution x ≤ I.evalSolution y

/-- Function `f` has Max-Cut property at labels `a` and `b` if and only if `argmin f` is exactly
`{ ![a, b] , ![b, a] }` -/
def Function.HasMaxCutPropertyAt (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
    ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
def Function.HasMaxCutProperty (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

/-- TODO description -/
def FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  List (((Fin m → D) → D) × ℕ)

/-- TODO description -/
def FractionalOperation.IsValid {m : ℕ} (ω : FractionalOperation D m) : Prop :=
  ω ≠ [] ∧ ω.Forall (·.snd ≠ 0)

/-- TODO description -/
def function_weigth_tt_aux {m n : ℕ} (g : ((Fin m → D) → D) × ℕ) (x' : Fin n → Fin m → D) :
    (Fin n → D) × ℕ :=
  ⟨fun i => g.fst (x' i), g.snd⟩

/-- TODO description -/
def FractionalOperation.tt {m n : ℕ} (ω : FractionalOperation D m) (x : Fin m → Fin n → D) :
    List ((Fin n → D) × ℕ) :=
  ω.map (fun g => function_weigth_tt_aux g (Function.swap x))

/-- TODO description -/
def Function.AdmitsFractional {n m : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) :
    Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map (fun r => r.snd • f r.fst)).sum ≤
    (ω.map Prod.snd).sum • ((List.finRange m).map (fun i => f (x i))).sum

/-- TODO description -/
def FractionalOperation.IsFractionalPolymorphismFor {m : ℕ}
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- TODO description -/
def FractionalOperation.IsSymmetric {m : ℕ} (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → ω.Forall (fun g => g.fst x = g.fst y)

/-- TODO description -/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor {m : ℕ}
    (ω : FractionalOperation D m) (Γ : ValuedCsp D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

attribute [pp_dot] Nat.succ List.length List.get List.sum

lemma Function.HasMaxCutProperty.forbids_commutative {D C : Type*}
    [LinearOrderedAddCommMonoid C] [IsLeftCancelAdd C]
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  rcases mcf with ⟨a, b, hab, mcfab⟩
  have cclass : CovariantClass C C (· + ·) (· < ·) -- TODO see whether necessary
  · constructor
    intro x y z hyz
    show x + y < x + z
    have hle : x + y ≤ x + z
    · exact add_le_add_left (le_of_lt hyz) x
    have hne : x + y ≠ x + z
    · intro contr
      apply LT.lt.ne hyz
      apply add_left_cancel
      exact contr
    exact Ne.lt_of_le hne hle
  intro contr
  specialize contr ![![a, b], ![b, a]]
  -- on each row `r` we have `f r.fst > f a b = f b a`
  have triv : (List.finRange 2).map (fun i => f (![![a, b], ![b, a]] i)) = [f ![a, b], f ![b, a]]
  · rfl
  have hfba : f ![b, a] = f ![a, b]
  · symm
    apply mcfab.left
  have sum_same : List.sum [f ![a, b], f ![a, b]] = 2 • f ![a, b]
  · convert_to 1 • f ![a, b] + 1 • f ![a, b] = (1 + 1) • f ![a, b]
    · simp
    symm
    apply add_nsmul
  rw [triv, hfba, sum_same] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun r => r.snd • f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun r => r.snd • f r.fst)).sum
  · sorry -- TODO utilize `symmega` with `valid` and `mcfab.right` with `hab` here
  have hlt := lt_of_lt_of_le sharp contr
  simp only [FractionalOperation.tt, function_weigth_tt_aux, List.map_map] at hlt
  have impos : 2 • (ω.map (fun r => r.snd • f ![a, b])).sum < (ω.map Prod.snd).sum • 2 • f ![a, b]
  · exact hlt
  have rhs_swap : (ω.map Prod.snd).sum • 2 • f ![a, b] = 2 • (ω.map Prod.snd).sum • f ![a, b]
  · apply nsmul_left_comm
  rw [rhs_swap] at impos
  have key : (ω.map (fun r => r.snd • f ![a, b])).sum = (ω.map Prod.snd).sum • f ![a, b]
  · sorry -- TODO some transitivity
  rw [key] at impos
  apply false_of_ne (ne_of_lt impos)
