/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ByContra
public import Lean.ToExpr

@[expose] public section

open Lean hiding Literal
open Std (HashMap)

namespace Sat

/-- A literal is a positive or negative occurrence of an atomic propositional variable.
  Note that unlike DIMACS, 0 is a valid variable index. -/
inductive Literal
  | pos : Nat → Literal
  | neg : Nat → Literal

/-- Construct a literal. Positive numbers are translated to positive literals,
  and negative numbers become negative literals. The input is assumed to be nonzero. -/
def Literal.ofInt (i : Int) : Literal :=
  if i < 0 then Literal.neg (-i-1).toNat else Literal.pos (i-1).toNat

/-- Swap the polarity of a literal. -/
def Literal.negate : Literal → Literal
  | pos i => neg i
  | neg i => pos i

meta instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr
  | Literal.pos i => mkApp (mkConst ``Literal.pos) (mkRawNatLit i)
  | Literal.neg i => mkApp (mkConst ``Literal.neg) (mkRawNatLit i)

/-- A clause is a list of literals, thought of as a disjunction like `a ∨ b ∨ ¬c`. -/
@[expose] def Clause := List Literal

/-- The empty clause -/
def Clause.nil : Clause := []

/-- Append a literal to a clause. -/
def Clause.cons : Literal → Clause → Clause := List.cons

/-- A formula is a list of clauses, thought of as a conjunction like `(a ∨ b) ∧ c ∧ (¬c ∨ ¬d)`. -/
abbrev Fmla := List Clause

/-- A single clause as a formula. -/
def Fmla.one (c : Clause) : Fmla := [c]

/-- A conjunction of formulas. -/
def Fmla.and (a b : Fmla) : Fmla := a ++ b

/-- Formula `f` subsumes `f'` if all the clauses in `f'` are in `f`.
We use this to prove that all clauses in the formula are subsumed by it. -/
structure Fmla.subsumes (f f' : Fmla) : Prop where
  prop : ∀ x, x ∈ f' → x ∈ f

theorem Fmla.subsumes_self (f : Fmla) : f.subsumes f := ⟨fun _ h ↦ h⟩
theorem Fmla.subsumes_left (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂)) : f.subsumes f₁ :=
  ⟨fun _ h ↦ H.1 _ <| List.mem_append.2 <| Or.inl h⟩
theorem Fmla.subsumes_right (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂)) : f.subsumes f₂ :=
  ⟨fun _ h ↦ H.1 _ <| List.mem_append.2 <| Or.inr h⟩

/-- A valuation is an assignment of values to all the propositional variables. -/
@[expose] def Valuation := Nat → Prop

/-- `v.neg lit` asserts that literal `lit` is falsified in the valuation. -/
def Valuation.neg (v : Valuation) : Literal → Prop
  | Literal.pos i => ¬ v i
  | Literal.neg i => v i

/-- `v.satisfies c` asserts that clause `c` satisfied by the valuation.
It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as
`¬a → b → ¬c → False`, so we are asserting that it is not the case that
all literals in the clause are falsified. -/
def Valuation.satisfies (v : Valuation) : Clause → Prop
  | [] => False
  | l::c => v.neg l → v.satisfies c

/-- `v.satisfies_fmla f` asserts that formula `f` is satisfied by the valuation.
A formula is satisfied if all clauses in it are satisfied. -/
structure Valuation.satisfies_fmla (v : Valuation) (f : Fmla) : Prop where
  prop : ∀ c, c ∈ f → v.satisfies c

/-- `f.proof c` asserts that `c` is derivable from `f`. -/
def Fmla.proof (f : Fmla) (c : Clause) : Prop :=
  ∀ v : Valuation, v.satisfies_fmla f → v.satisfies c

/-- If `f` subsumes `c` (i.e. `c ∈ f`), then `f.proof c`. -/
theorem Fmla.proof_of_subsumes {f : Fmla} {c : Clause}
    (H : Fmla.subsumes f (Fmla.one c)) : f.proof c :=
  fun _ h ↦ h.1 _ <| H.1 _ <| List.Mem.head ..

/-- The core unit-propagation step.

We have a local context of assumptions `¬l'` (sometimes called an assignment)
and we wish to add `¬l` to the context, that is, we want to prove `l` is also falsified.
This is because there is a clause `a ∨ b ∨ ¬l` in the global context
such that all literals in the clause are falsified except for `¬l`;
so in the context `h₁` where we suppose that `¬l` is falsified,
the clause itself is falsified so we can prove `False`.
We continue the proof in `h₂`, with the assumption that `l` is falsified. -/
theorem Valuation.by_cases {v : Valuation} {l}
    (h₁ : v.neg l.negate → False) (h₂ : v.neg l → False) : False :=
match l with
| Literal.pos _ => h₂ h₁
| Literal.neg _ => h₁ h₂

/-- `v.implies p [a, b, c] 0` definitionally unfolds to `(v 0 ↔ a) → (v 1 ↔ b) → (v 2 ↔ c) → p`.
This is used to introduce assumptions about the first `n` values of `v` during reification. -/
def Valuation.implies (v : Valuation) (p : Prop) : List Prop → Nat → Prop
  | [], _ => p
  | a::as, n => (v n ↔ a) → v.implies p as (n + 1)

/-- `Valuation.mk [a, b, c]` is a valuation which is `a` at 0, `b` at 1 and `c` at 2, and false
everywhere else. -/
def Valuation.mk : List Prop → Valuation
  | [], _ => False
  | a::_, 0 => a
  | _::as, n + 1 => mk as n

/-- The fundamental relationship between `mk` and `implies`:
`(mk ps).implies p ps 0` is equivalent to `p`. -/
theorem Valuation.mk_implies {p} {as ps} (as₁) : as = List.reverseAux as₁ ps →
    (Valuation.mk as).implies p ps as₁.length → p := by
  induction ps generalizing as₁ with
  | nil => exact fun _ ↦ id
  | cons a as ih =>
    refine fun e H ↦ @ih (a::as₁) e (H ?_)
    subst e; clear ih H
    suffices ∀ n n', n' = List.length as₁ + n →
      ∀ bs, mk (as₁.reverseAux bs) n' ↔ mk bs n from this 0 _ rfl (a::as)
    induction as₁ with
    | nil => simp
    | cons b as₁ ih => simpa using fun n bs ↦ ih (n + 1) _ (Nat.succ_add ..) _

/-- Asserts that `¬⟦f⟧_v` implies `p`. -/
structure Fmla.reify (v : Valuation) (f : Fmla) (p : Prop) : Prop where
  prop : ¬ v.satisfies_fmla f → p

variable {v : Valuation}

/-- If `f` is unsatisfiable, and every `v` which agrees with `ps` implies `¬⟦f⟧_v → p`, then `p`.
Equivalently, there exists a valuation `v` which agrees with `ps`,
and every such valuation yields `¬⟦f⟧_v` because `f` is unsatisfiable. -/
theorem Fmla.refute {p : Prop} {ps} (f : Fmla) (hf : f.proof [])
    (hv : ∀ v, Valuation.implies v (Fmla.reify v f p) ps 0) : p :=
  (Valuation.mk_implies [] rfl (hv _)).1 (hf _)

/-- Negation turns AND into OR, so `¬⟦f₁ ∧ f₂⟧_v ≡ ¬⟦f₁⟧_v ∨ ¬⟦f₂⟧_v`. -/
theorem Fmla.reify_or {f₁ : Fmla} {a : Prop} {f₂ : Fmla} {b : Prop}
    (h₁ : Fmla.reify v f₁ a) (h₂ : Fmla.reify v f₂ b) : Fmla.reify v (f₁.and f₂) (a ∨ b) := by
  refine ⟨fun H ↦ by_contra fun hn ↦ H ⟨fun c h ↦ by_contra fun hn' ↦ ?_⟩⟩
  rcases List.mem_append.1 h with h | h
  · exact hn <| Or.inl <| h₁.1 fun Hc ↦ hn' <| Hc.1 _ h
  · exact hn <| Or.inr <| h₂.1 fun Hc ↦ hn' <| Hc.1 _ h

/-- Asserts that `¬⟦c⟧_v` implies `p`. -/
structure Clause.reify (v : Valuation) (c : Clause) (p : Prop) : Prop where
  prop : ¬ v.satisfies c → p

/-- Reification of a single clause formula. -/
theorem Fmla.reify_one {c : Clause} {a : Prop} (h : Clause.reify v c a) :
    Fmla.reify v (Fmla.one c) a :=
  ⟨fun H ↦ h.1 fun h ↦ H ⟨fun | _, List.Mem.head .. => h⟩⟩

/-- Asserts that `¬⟦l⟧_v` implies `p`. -/
structure Literal.reify (v : Valuation) (l : Literal) (p : Prop) : Prop where
  prop : v.neg l → p

/-- Negation turns OR into AND, so `¬⟦l ∨ c⟧_v ≡ ¬⟦l⟧_v ∧ ¬⟦c⟧_v`. -/
theorem Clause.reify_and {l : Literal} {a : Prop} {c : Clause} {b : Prop}
    (h₁ : Literal.reify v l a) (h₂ : Clause.reify v c b) :
    Clause.reify v (Clause.cons l c) (a ∧ b) :=
  ⟨fun H ↦ ⟨h₁.1 (by_contra fun hn ↦ H hn.elim), h₂.1 fun h ↦ H fun _ ↦ h⟩⟩

/-- The reification of the empty clause is `True`: `¬⟦⊥⟧_v ≡ True`. -/
theorem Clause.reify_zero : Clause.reify v Clause.nil True := ⟨fun _ ↦ trivial⟩

/-- The reification of a singleton clause `¬⟦l⟧_v ≡ ¬⟦l⟧_v`. -/
theorem Clause.reify_one {l : Literal} {a : Prop}
    (h₁ : Literal.reify v l a) : Clause.reify v (Clause.nil.cons l) a :=
  ⟨fun H ↦ ((Clause.reify_and h₁ Clause.reify_zero).1 H).1⟩

/-- The reification of a positive literal `¬⟦a⟧_v ≡ ¬a`. -/
theorem Literal.reify_pos {a : Prop} {n : ℕ} (h : v n ↔ a) : (Literal.pos n).reify v ¬a := ⟨mt h.2⟩

/-- The reification of a negative literal `¬⟦¬a⟧_v ≡ a`. -/
theorem Literal.reify_neg {a : Prop} {n : ℕ} (h : v n ↔ a) : (Literal.neg n).reify v a := ⟨h.1⟩

end Sat
