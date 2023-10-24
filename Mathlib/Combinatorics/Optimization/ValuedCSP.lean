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
* `ValuedCsp.Instance.OptimumSolution`: Is given solution a minimum of the VCSP instance?

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

def Function.HasMaxCutPropertyAt (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧  -- `argmin f` is exactly `{ ![a, b] , ![b, a] }`
    ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

def Function.HasMaxCutProperty (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

def FractionalOperation (D : Type _) (m k : ℕ) : Type :=
  (Fin m → D) → (Fin k → D)

/-
For documentation purposes, here is a "less compact" version of the upcoming two definitions:

[import Mathlib.Data.Matrix.Basic]

def FractionalOperation.tt {D : Type} {m k n : ℕ}
    (ω : FractionalOperation D m k) (x : (Fin m → (Fin n → D))) :
    (Fin k → (Fin n → D)) :=
  Matrix.transpose (fun (i : Fin n) => ω ((Matrix.transpose x) i))

def Function.AdmitsFractional {D C : Type} [OrderedAddCommMonoid C] {n m k : ℕ}
    (f : (Fin n → D) → C) (ω : FractionalOperation D m k) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • List.sum (List.map (fun i => f ((ω.tt x) i)) (List.finRange k)) ≤
    k • List.sum (List.map (fun i => f (      x  i)) (List.finRange m))

They should be defeq to the definitions below.
-/

def FractionalOperation.tt {D : Type _} {m k n : ℕ}
    (ω : FractionalOperation D m k) (x : (Fin m → (Fin n → D)))
    (a : Fin k) (b : Fin n) : D :=
  (ω (fun (i : Fin m) => x i b)) a

def Function.AdmitsFractional {D C : Type _} [OrderedAddCommMonoid C] {n m k : ℕ}
    (f : (Fin n → D) → C) (ω : FractionalOperation D m k) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • List.sum (List.map (f ∘ (ω.tt x)) (List.finRange k)) ≤
    k • List.sum (List.map (f ∘ x) (List.finRange m))

def FractionalOperation.IsFractionalPolymorphismFor
    {D C : Type _} [OrderedAddCommMonoid C] {m k : ℕ}
    (ω : FractionalOperation D m k) (Γ : ValuedCsp D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

def FractionalOperation.IsSymmetric {D : Type _} {m k : ℕ}
    (ω : FractionalOperation D m k) : Prop :=
  ∀ x y : (Fin m → D), List.ofFn x ~ List.ofFn y → ω x = ω y

def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    {D C : Type _} [OrderedAddCommMonoid C] {m k : ℕ}
    (ω : FractionalOperation D m k) (Γ : ValuedCsp D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

lemma apply222tt {D : Type _} (ω : FractionalOperation D 2 2) (a b c d : D) :
    ω.tt ![ ![a, b] , ![c, d] ] =
    ![ ![ ω ![a, c] 0 , ω ![b, d] 0 ] , ![ ω ![a, c] 1 , ω ![b, d] 1 ] ] := by
  ext i j
  match j with
  | 0 =>
    have h0 : ∀ k : Fin 2, ![ ![a, b] , ![c, d] ] k 0 = ![ a , c ] k
    · intro k
      match k with
      | 0 => rfl
      | 1 => rfl
    match i with
    | 0 => simp [FractionalOperation.tt, h0]
    | 1 => simp [FractionalOperation.tt, h0]
  | 1 =>
    have h1 : ∀ k : Fin 2, ![ ![a, b] , ![c, d] ] k 1 = ![ b , d ] k
    · intro k
      match k with
      | 0 => rfl
      | 1 => rfl
    match i with
    | 0 => simp [FractionalOperation.tt, h1]
    | 1 => simp [FractionalOperation.tt, h1]

private lemma two_nsmul_le_two_nsmul {C : Type _} [LinearOrderedAddCommMonoid C] {x y : C}
    [CovariantClass C C (· + ·) (· < ·)]
    (hyp : 2 • x ≤ 2 • y) : x ≤ y :=
  le_of_nsmul_le_nsmul (by decide) hyp

private lemma todo_name {C : Type*} [OrderedAddCommMonoid C] [IsLeftCancelAdd C] {x x' y y' : C}
    (hxy : x + y ≤ x' + y') (hx : x > x') (hy : y > y') : False := by
  have impossible : x + y < x + y
  · apply hxy.trans_lt
    apply (OrderedAddCommMonoid.add_le_add_left y' y (le_of_lt hy) x').trans_lt
    rw [add_comm x', add_comm x]
    apply lt_of_le_of_ne
    · exact add_le_add (le_of_eq rfl) (le_of_lt hx)
    rw [add_ne_add_right]
    exact ne_of_lt hx
  exact LT.lt.false impossible

lemma Function.HasMaxCutProperty.forbids_commutative {D C : Type _}
    [LinearOrderedAddCommMonoid C] [IsLeftCancelAdd C]
    {f : (Fin 2 → D) → C} {ω : FractionalOperation D 2 2}
    (mcf : f.HasMaxCutProperty) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  rcases mcf with ⟨a, b, hab, mcfab⟩
  have cclass : CovariantClass C C (· + ·) (· < ·)
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
  have tt_le := two_nsmul_le_two_nsmul (contr ![ ![a, b] , ![b, a] ])
  clear contr
  rw [
    show
      List.map (f ∘ ![ ![a, b] , ![b, a] ]) (List.finRange 2) =
      [ f ![a, b] , f ![b, a] ] by
      rfl,
    show
      List.sum [ f ![a, b] , f ![b, a] ] =
      f ![a, b] + f ![b, a] by
      simp,
    apply222tt,
    show ω ![b, a] = ω ![a, b] by
      apply symmega
      apply List.Perm.swap,
    show
      List.map (f ∘ ![ ![ ω ![a, b] 0 , ω ![a, b] 0 ], ![ ω ![a, b] 1 , ω ![a, b] 1 ]]) (List.finRange 2) =
      [ f ![ ω ![a, b] 0 , ω ![a, b] 0 ] , f ![ ω ![a, b] 1 , ω ![a, b] 1 ] ] by
      rfl,
    show
      List.sum [ f ![ ω ![a, b] 0 , ω ![a, b] 0 ] , f ![ ω ![a, b] 1 , ω ![a, b] 1 ] ] =
      f ![ ω ![a, b] 0, ω ![a, b] 0 ] + f ![ ω ![a, b] 1, ω ![a, b] 1 ] by
      simp
  ] at tt_le
  have wrong0 : f ![ω ![a, b] 0, ω ![a, b] 0] > f ![a, b]
  · obtain ⟨fle, fne⟩ := mcfab.right (ω ![a, b] 0) (ω ![a, b] 0)
    refine Ne.lt_of_le ?_neq0 fle
    intro equ
    rcases fne equ with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ <;>
    · rw [← hb0] at ha0
      exact hab ha0
  have wrong1 : f ![ω ![a, b] 1, ω ![a, b] 1] > f ![b, a]
  · obtain ⟨fle, fne⟩ := mcfab.right (ω ![a, b] 1) (ω ![a, b] 1)
    rw [← mcfab.left]
    refine Ne.lt_of_le ?_neq1 fle
    intro equ
    rcases fne equ with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ <;>
    · rw [← hb0] at ha0
      exact hab ha0
  exact todo_name tt_le wrong0 wrong1
