/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation

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

@[expose] public section

/-- A template for a valued CSP problem over a domain `D` with costs in `C`.
Regarding `C` we want to support `Bool`, `Nat`, `ENat`, `Int`, `Rat`, `NNRat`,
`Real`, `NNReal`, `EReal`, `ENNReal`, and tuples made of any of those types. -/
@[nolint unusedArguments]
abbrev ValuedCSP (D C : Type*) [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → C) -- Cost functions `D^n → C` for any `n`

variable {D C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C]

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
`{ ![a, b], ![b, a] }`. -/
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
def FractionalOperation.size (ω : FractionalOperation D m) : ℕ := ω.card

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

lemma Function.HasMaxCutPropertyAt.rows_lt_aux {C : Type*} [PartialOrder C]
    {f : (Fin 2 → D) → C} {a b : D} (mcf : f.HasMaxCutPropertyAt a b) (hab : a ≠ b)
    {ω : FractionalOperation D 2} (symmega : ω.IsSymmetric)
    {r : Fin 2 → D} (rin : r ∈ (ω.tt ![![a, b], ![b, a]])) :
    f ![a, b] < f r := by
  rw [FractionalOperation.tt, Multiset.mem_map] at rin
  rw [show r = ![r 0, r 1] by simp [← List.ofFn_inj]]
  apply lt_of_le_of_ne (mcf.right (r 0) (r 1)).left
  intro equ
  have asymm : r 0 ≠ r 1 := by
    rcases (mcf.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw [ha0, hb1] at hab
      exact hab
    · rw [ha1, hb0] at hab
      exact hab.symm
  apply asymm
  obtain ⟨o, in_omega, rfl⟩ := rin
  change o (fun j => ![![a, b], ![b, a]] j 0) = o (fun j => ![![a, b], ![b, a]] j 1)
  convert! symmega ![a, b] ![b, a] (by simp [List.Perm.swap]) o in_omega using 2 <;>
    simp [Matrix.const_fin1_eq]

variable {C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedCancelAddMonoid C]

lemma Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  obtain ⟨a, b, hab, mcfab⟩ := mcf
  specialize contr ![![a, b], ![b, a]]
  rw [Fin.sum_univ_two', ← mcfab.left, ← two_nsmul] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
    have half_sharp :
      ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
      ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
      apply Multiset.sum_lt_sum
      · intro r rin
        exact le_of_lt (mcfab.rows_lt_aux hab symmega rin)
      · obtain ⟨g, _⟩ := valid.contains
        have : (fun i => g ((Function.swap ![![a, b], ![b, a]]) i)) ∈ ω.tt ![![a, b], ![b, a]] := by
          simp only [FractionalOperation.tt, Multiset.mem_map]
          use g
        exact ⟨_, this, mcfab.rows_lt_aux hab symmega this⟩
    rw [two_nsmul, two_nsmul]
    exact add_lt_add half_sharp half_sharp
  have impos : 2 • (ω.map (fun _ => f ![a, b])).sum < ω.size • 2 • f ![a, b] := by
    convert! lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, Multiset.map_map]
  have rhs_swap : ω.size • 2 • f ![a, b] = 2 • ω.size • f ![a, b] := nsmul_left_comm ..
  have distrib : (ω.map (fun _ => f ![a, b])).sum = ω.size • f ![a, b] := by simp
  rw [rhs_swap, distrib] at impos
  exact ne_of_lt impos rfl
