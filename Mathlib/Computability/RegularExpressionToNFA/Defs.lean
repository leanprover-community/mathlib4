/-
Copyright (c) 2022 Russell Emerine, 2024 Tom Kranz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine, Tom Kranz
-/
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.NFA
import Mathlib.Data.FinEnum
import Mathlib.Data.FinEnum.Option

#align_import computability.regular_expression_to_NFA.defs

/-!
# Definitions for Converting Regular Expressions to NFA's

Definitions of the state types of NFA's corresponding to regular expressions, and some required
instances for those state types. Then, definitions of NFA's corresponding to regular expressions,
and some required instances for those NFA's.

This is based on the referenced link. The link uses ε-NFA's, but it was hard to deal with
ε-closures when proving things, so I used equivalent one-character transition NFA's instead.

## References

* <https://courses.engr.illinois.edu/cs373/sp2013/Lectures/lec07.pdf>
-/


universe u

variable {α : Type u}

namespace RegularExpression

/-- A recursor for regular expressions, since the code generator doesn't want to implement it for
us. -/
def rec' {α : Type u} {motive : RegularExpression α → Type _}
    (zero : motive zero)
    (epsilon : motive epsilon)
    (char : (a : α) → motive (char a))
    (plus : (a a_1 : RegularExpression α) → motive a → motive a_1 → motive (plus a a_1))
    (comp : (a a_1 : RegularExpression α) → motive a → motive a_1 → motive (comp a a_1))
    (star : (a : RegularExpression α) → motive a → motive (star a)) :
    (t : RegularExpression α) → motive t
  | .zero => zero
  | .epsilon => epsilon
  | .char a => char a
  | .plus l r =>
      plus l r (rec' zero epsilon char plus comp star l) (rec' zero epsilon char plus comp star r)
  | .comp l r =>
      comp l r (rec' zero epsilon char plus comp star l) (rec' zero epsilon char plus comp star r)
  | .star r => star r (rec' zero epsilon char plus comp star r)

/-- A recursor for regular expressions with the expression as the first argument, since the code
generator doesn't want to implement it for us. -/
def recOn' {α : Type u} {motive : RegularExpression α → Type _}
    (t : RegularExpression α)
    (zero : motive zero)
    (epsilon : motive epsilon)
    (char : (a : α) → motive (char a))
    (plus : (a a_1 : RegularExpression α) → motive a → motive a_1 → motive (plus a a_1))
    (comp : (a a_1 : RegularExpression α) → motive a → motive a_1 → motive (comp a a_1))
    (star : (a : RegularExpression α) → motive a → motive (star a)) :
    motive t := rec' zero epsilon char plus comp star t

/-- The state space of the resulting NFA depends on the regular expression's structure. -/
def State : RegularExpression α → Type _
  | zero => Unit
  | epsilon => Unit
  | char _ => Bool
  | plus r₁ r₂ => Sum (State r₁) (State r₂)
  | comp r₁ r₂ => Sum (State r₁) (State r₂)
  | star r => Option (State r)

instance {r : RegularExpression α} : Inhabited r.State :=
  r.recOn'
    (instInhabitedPUnit)
    (instInhabitedPUnit)
    (fun _ ↦ instInhabitedBool)
    (fun r₁ r₂ hr₁ _ ↦ @Sum.inhabitedLeft r₁.State r₂.State hr₁)
    (fun r₁ r₂ hr₁ _ ↦ @Sum.inhabitedLeft r₁.State r₂.State hr₁)
    (fun _ _ ↦ instInhabitedOption)

/-- Recursively converts a regular expression to its corresponding NFA.
-/
def toNFA : ∀ r : RegularExpression α, NFA α r.State
  | zero => ⟨fun _ _ _ ↦ False, fun _ ↦ False, fun _ ↦ False⟩
  | epsilon => ⟨fun _ _ _ ↦ False, fun _ ↦ True, fun _ ↦ True⟩
  | char a => ⟨fun p c q ↦ p = false ∧ a = c ∧ q = true, fun q ↦ q = false, fun q ↦ q = true⟩
  | plus r₁ r₂ =>
    let P₁ := r₁.toNFA
    let P₂ := r₂.toNFA
    ⟨fun p c q ↦
      match (p, q) with
      | (Sum.inl p, Sum.inl q) => P₁.step p c q
      | (Sum.inr p, Sum.inr q) => P₂.step p c q
      | _ => False,
      fun q ↦
      match q with
      | Sum.inl q => P₁.start q
      | Sum.inr q => P₂.start q,
      fun q ↦
      match q with
      | Sum.inl q => P₁.accept q
      | Sum.inr q => P₂.accept q⟩
  | comp r₁ r₂ =>
    let P₁ := r₁.toNFA
    let P₂ := r₂.toNFA
    ⟨fun p c q ↦
      match (p, q) with
      | (Sum.inl p, Sum.inl q) => P₁.step p c q
      | (Sum.inl p, Sum.inr q) => P₂.start q ∧ ∃ r, P₁.accept r ∧ P₁.step p c r
      | (Sum.inr p, Sum.inr q) => P₂.step p c q
      | _ => False,
      fun q ↦
      match q with
      | Sum.inl q => P₁.start q
      | Sum.inr q => P₂.start q ∧ ∃ p, P₁.accept p ∧ P₁.start p,
      fun q ↦
      match q with
      | Sum.inl q => P₁.accept q ∧ ∃ p, P₂.accept p ∧ P₂.start p
      | Sum.inr q => P₂.accept q⟩
  | star r =>
    let P := r.toNFA
    ⟨fun p c q ↦
      match (p, q) with
      | (some p, some q) => P.step p c q ∨ ∃ r, P.accept r ∧ P.step p c r ∧ P.start q
      | _ => False,
      fun q ↦
      match q with
      | some q => P.start q
      | none => True,
      fun q ↦
      match q with
      | some q => P.accept q
      | none => True⟩

/-- NFAs constructed from regular expressions have computational meaning.
One part of that comes from the state space always being finite and enumerable.
-/
instance {r : RegularExpression α} : FinEnum r.State :=
  r.recOn'
    (FinEnum.punit.{0})
    (FinEnum.punit.{0})
    (fun _ ↦ FinEnum.ofEquiv _ Equiv.boolEquivPUnitSumPUnit.{0,0})
    (fun r₁ r₂ hr₁ hr₂ ↦ @FinEnum.sum r₁.State r₂.State hr₁ hr₂)
    (fun r₁ r₂ hr₁ hr₂ ↦ @FinEnum.sum r₁.State r₂.State hr₁ hr₂)
    (fun r hr ↦ @FinEnum.instFinEnumOptionOfFinEnum r.State hr)

/-- NFAs constructed from regular expressions have computational meaning.
One part of that comes from all transition target state sets, the start state set and the accept
state set being defined by `DecidablePred`s.
-/
def regularExpressionToNFADecidable [DecidableEq α] {r : RegularExpression α} :
    (∀ p a, DecidablePred (· ∈ r.toNFA.step p a)) ×
    DecidablePred r.toNFA.start ×
    DecidablePred r.toNFA.accept := by
  apply r.recOn'
  case zero =>
    refine' ⟨_, _, _⟩ <;> (repeat intro _) <;> exact decidableFalse
  case epsilon =>
    refine' ⟨_, _, _⟩ <;> (repeat intro _) <;>
      first | exact decidableTrue | exact decidableFalse
  case char =>
    intro a
    refine' ⟨_, _, _⟩ <;> (repeat intro _) <;>
      first | exact And.decidable | exact Set.decidableSetOf _ <| Eq _
  case plus =>
    intro r₁ r₂ ⟨hr₁_step, hr₁_start, hr₁_accept⟩ ⟨hr₂_step, hr₂_start, hr₂_accept⟩
    refine' ⟨_, _, _⟩
    · rintro (p | p) a (q | q) <;> try exact decidableFalse
      · exact hr₁_step p a q
      · exact hr₂_step p a q
    · rintro (q | q)
      · exact hr₁_start q
      · exact hr₂_start q
    · rintro (q | q)
      · exact hr₁_accept q
      · exact hr₂_accept q
  case comp =>
    rintro r₁ r₂ ⟨hr₁_step, hr₁_start, hr₁_accept⟩ ⟨hr₂_step, hr₂_start, hr₂_accept⟩
    refine' ⟨_, _, _⟩
    · rintro (p | p) a (q | q)
      · exact hr₁_step p a q
      · have : Decidable (∃ r : r₁.State, r₁.toNFA.accept r ∧ r₁.toNFA.step p a r) :=
          haveI : DecidablePred fun r : r₁.State ↦ r₁.toNFA.accept r ∧ r₁.toNFA.step p a r := by
            intro r
            have : Decidable (r₁.toNFA.step p a r) := hr₁_step p a r
            exact And.decidable
          Fintype.decidableExistsFintype
        exact And.decidable
      · exact decidableFalse
      · exact hr₂_step p a q
    · rintro (q | q)
      · exact hr₁_start q
      · exact And.decidable
    · rintro (q | q)
      · exact And.decidable
      · exact hr₂_accept q
  case star =>
    rintro r ⟨hr_step, hr_start, hr_accept⟩
    refine' ⟨_, _, _⟩
    · rintro (⟨⟩ | p)  a (⟨⟩ | q) <;> try exact decidableFalse
      have : Decidable (r.toNFA.step p a q) := hr_step p a q
      have :
        Decidable (∃ r_1 : r.State, r.toNFA.accept r_1 ∧ r.toNFA.step p a r_1 ∧ r.toNFA.start q) :=
        haveI :
          DecidablePred fun r_1 : r.State ↦
            r.toNFA.accept r_1 ∧ r.toNFA.step p a r_1 ∧ r.toNFA.start q := by
          intro s
          have : Decidable (r.toNFA.step p a s ∧ r.toNFA.start q) :=
            haveI : Decidable (r.toNFA.step p a s) := hr_step p a s
            And.decidable
          exact And.decidable
        Fintype.decidableExistsFintype
      exact Or.decidable
    · rintro (⟨⟩ | q)
      · exact decidableTrue
      · exact hr_start q
    · rintro (⟨⟩ | q)
      · exact decidableTrue
      · exact hr_accept q

/-- NFAs constructed from regular expressions have computational meaning.
One part of that comes from all transition target state sets being defined by `DecidablePred`s.
-/
instance decidableStep [DecidableEq α] {r : RegularExpression α} {p a} :
    DecidablePred (· ∈ r.toNFA.step p a) :=
  regularExpressionToNFADecidable.1 p a

/-- NFAs constructed from regular expressions have computational meaning.
One part of that comes from the start state set being defined by a `DecidablePred`.
-/
instance decidableStart [DecidableEq α] {r : RegularExpression α} :
    DecidablePred r.toNFA.start :=
  regularExpressionToNFADecidable.2.1

/-- NFAs constructed from regular expressions have computational meaning.
One part of that comes from the start state set being defined by a `DecidablePred`.
-/
instance decidableAccept [DecidableEq α] {r : RegularExpression α} :
    DecidablePred r.toNFA.accept :=
  regularExpressionToNFADecidable.2.2

end RegularExpression

