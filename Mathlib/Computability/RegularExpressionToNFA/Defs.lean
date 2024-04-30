/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
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

variable {α : Type u} [dec : DecidableEq α]

namespace RegularExpression
def rec'
    {α : Type u}
    {motive : RegularExpression α → Type _}
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
  | .plus l r => plus l r (rec' zero epsilon char plus comp star l) (rec' zero epsilon char plus comp star r)
  | .comp l r => comp l r (rec' zero epsilon char plus comp star l) (rec' zero epsilon char plus comp star r)
  | .star r => star r (rec' zero epsilon char plus comp star r)


/-- The NFA state type for a particular regular expression.
-/
def State : RegularExpression α → Type _
  | zero => Unit
  | epsilon => Unit
  | char _ => Bool
  | plus r₁ r₂ => Sum (State r₁) (State r₂)
  | comp r₁ r₂ => Sum (State r₁) (State r₂)
  | star r => Option (State r)

instance {r : RegularExpression α} : Inhabited r.State :=
  @rec' α (Inhabited ∘ State)
    (instInhabitedPUnit)
    (instInhabitedPUnit)
    (λ a => instInhabitedBool)
    (λ r₁ r₂ hr₁ hr₂ => @Sum.inhabitedLeft r₁.State r₂.State hr₁)
    (λ r₁ r₂ hr₁ hr₂ => @Sum.inhabitedLeft r₁.State r₂.State hr₁)
    (λ r hr => instInhabitedOption)
    r

-- NFAs are only real NFAs when the states are fintypes, and the instance is needed for the proofs
instance {r : RegularExpression α} : FinEnum r.State :=
  @rec' α (FinEnum ∘ State)
    (FinEnum.punit.{0})
    (FinEnum.punit.{0})
    (λ a => FinEnum.ofEquiv _ Equiv.boolEquivPUnitSumPUnit.{0,0})
    (λ r₁ r₂ hr₁ hr₂ => @FinEnum.sum r₁.State r₂.State hr₁ hr₂)
    (λ r₁ r₂ hr₁ hr₂ => @FinEnum.sum r₁.State r₂.State hr₁ hr₂)
    (λ r hr => @FinEnum.instFinEnumOptionOfFinEnum r.State hr)
    r

/-- Recursively converts a regular expression to its corresponding NFA.
-/
def toNFA : ∀ r : RegularExpression α, NFA α r.State
  | zero => ⟨fun _ _ _ => False, fun _ => False, fun _ => False⟩
  | epsilon => ⟨fun _ _ _ => False, fun _ => True, fun _ => True⟩
  | char a => ⟨fun p c q => p = false ∧ a = c ∧ q = true, fun q => q = false, fun q => q = true⟩
  | plus r₁ r₂ =>
    let P₁ := r₁.toNFA
    let P₂ := r₂.toNFA
    ⟨fun p c q =>
      match (p, q) with
      | (Sum.inl p, Sum.inl q) => P₁.step p c q
      | (Sum.inl _, Sum.inr _) => False
      | (Sum.inr _, Sum.inl _) => False
      | (Sum.inr p, Sum.inr q) => P₂.step p c q,
      fun q =>
      match q with
      | Sum.inl q => P₁.start q
      | Sum.inr q => P₂.start q,
      fun q =>
      match q with
      | Sum.inl q => P₁.accept q
      | Sum.inr q => P₂.accept q⟩
  | comp r₁ r₂ =>
    let P₁ := r₁.toNFA
    let P₂ := r₂.toNFA
    ⟨fun p c q =>
      match (p, q) with
      | (Sum.inl p, Sum.inl q) => P₁.step p c q
      | (Sum.inl p, Sum.inr q) => P₂.start q ∧ ∃ r, P₁.accept r ∧ P₁.step p c r
      | (Sum.inr p, Sum.inl q) => False
      | (Sum.inr p, Sum.inr q) => P₂.step p c q,
      fun q =>
      match q with
      | Sum.inl q => P₁.start q
      | Sum.inr q => P₂.start q ∧ ∃ p, P₁.accept p ∧ P₁.start p,
      fun q =>
      match q with
      | Sum.inl q => P₁.accept q ∧ ∃ p, P₂.accept p ∧ P₂.start p
      | Sum.inr q => P₂.accept q⟩
  | star r =>
    let P := r.toNFA
    ⟨fun p c q =>
      match (p, q) with
      | (some p, some q) => P.step p c q ∨ ∃ r, P.accept r ∧ P.step p c r ∧ P.start q
      | (some p, none) => False
      | (none, some q) => False
      | (none, none) => False,
      fun q =>
      match q with
      | some q => P.start q
      | none => True,
      fun q =>
      match q with
      | some q => P.accept q
      | none => True⟩

/--
All three functions in an NFA constructed from `toNFA` are decidable. Since the functions rely on
each other, the class is proven here, and the instance declarations use this.
-/
def regularExpressionToNFADecidable {r : RegularExpression α} :
    (∀ p a, DecidablePred (· ∈ r.toNFA.step p a)) ×
      DecidablePred r.toNFA.start × DecidablePred r.toNFA.accept :=
  by
  apply r.rec'
  case zero =>
    refine' ⟨_, _, _⟩
    · intro _ _ _; exact decidableFalse
    · intro q; exact decidableFalse
    · intro q; exact decidableFalse
  case epsilon =>
    refine' ⟨_, _, _⟩
    · intro p a q; exact decidableFalse
    · intro q; exact decidableTrue
    · intro q; exact decidableTrue
  case char =>
    intro a
    refine' ⟨_, _, _⟩
    · intro p c q; exact And.decidable
    · intro q; exact Set.decidableSetOf false (Eq q)
    · intro q; exact Set.decidableSetOf true (Eq q)
  case plus =>
    intro r₁ r₂ hr₁ hr₂
    rcases hr₁ with ⟨hr₁_step, hr₁_start, hr₁_accept⟩
    rcases hr₂ with ⟨hr₂_step, hr₂_start, hr₂_accept⟩
    refine' ⟨_, _, _⟩
    · intro p a q
      rcases p with p | p <;> rcases q with q | q
      case inl.inl => exact hr₁_step p a q
      case inl.inr => exact decidableFalse
      case inr.inl => exact decidableFalse
      case inr.inr => exact hr₂_step p a q
    · intro q
      rcases q with q | q
      case inl => exact hr₁_start q
      case inr => exact hr₂_start q
    · intro q
      rcases q with q | q
      case inl => exact hr₁_accept q
      case inr => exact hr₂_accept q
  case comp =>
    intro r₁ r₂ hr₁ hr₂
    rcases hr₁ with ⟨hr₁_step, hr₁_start, hr₁_accept⟩
    rcases hr₂ with ⟨hr₂_step, hr₂_start, hr₂_accept⟩
    refine' ⟨_, _, _⟩
    · intro p a q
      rcases p with p | p <;> rcases q with q | q
      case inl.inl => exact hr₁_step p a q
      case
        inl.inr =>
        have : Decidable (∃ r : r₁.State, r₁.toNFA.accept r ∧ r₁.toNFA.step p a r) :=
          haveI : DecidablePred fun r : r₁.State => r₁.toNFA.accept r ∧ r₁.toNFA.step p a r :=
            by
            intro r
            have : Decidable (r₁.toNFA.step p a r) := hr₁_step p a r
            exact And.decidable
          Fintype.decidableExistsFintype
        exact And.decidable
      case inr.inl => exact decidableFalse
      case inr.inr => exact hr₂_step p a q
    · intro q
      rcases q with q | q
      case inl => exact hr₁_start q
      case inr => exact And.decidable
    · intro q
      rcases q with q | q
      case inl => exact And.decidable
      case inr => exact hr₂_accept q
  case star =>
    intro r hr
    rcases hr with ⟨hr_step, hr_start, hr_accept⟩
    refine' ⟨_, _, _⟩
    · intro p a q
      rcases p with p | p <;> rcases q with q | q
      case some.some =>
        have : Decidable (r.toNFA.step p a q) := hr_step p a q
        have :
          Decidable
            (∃ r_1 : r.State, r.toNFA.accept r_1 ∧ r.toNFA.step p a r_1 ∧ r.toNFA.start q) :=
          haveI :
            DecidablePred fun r_1 : r.State =>
              r.toNFA.accept r_1 ∧ r.toNFA.step p a r_1 ∧ r.toNFA.start q :=
            by
            intro s
            have : Decidable (r.toNFA.step p a s ∧ r.toNFA.start q) :=
              haveI : Decidable (r.toNFA.step p a s) := hr_step p a s
              And.decidable
            exact And.decidable
          Fintype.decidableExistsFintype
        exact Or.decidable
      all_goals exact decidableFalse
    · intro q
      rcases q with q | q
      case none => exact decidableTrue
      case some => exact hr_start q
    · intro q
      rcases q with q | q
      case none => exact decidableTrue
      case some => exact hr_accept q

instance decidableStep {r : RegularExpression α} {p a} : DecidablePred (· ∈ r.toNFA.step p a) :=
  regularExpressionToNFADecidable.1 p a

instance decidableStart {r : RegularExpression α} : DecidablePred r.toNFA.start :=
  regularExpressionToNFADecidable.2.1

instance decidableAccept {r : RegularExpression α} : DecidablePred r.toNFA.accept :=
  regularExpressionToNFADecidable.2.2

end RegularExpression

