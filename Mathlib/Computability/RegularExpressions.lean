/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.Language
import Mathlib.Tactic.AdaptationNote

#align_import computability.regular_expressions from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent. -/

-- Porting note: this has been commented out
-- * `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.



open List Set

open Computability

universe u

variable {α β γ : Type*} [dec : DecidableEq α]

/-- This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α
#align regular_expression RegularExpression


-- Porting note: `simpNF` gets grumpy about how the `foo_def`s below can simplify these..
attribute [nolint simpNF] RegularExpression.zero.sizeOf_spec
attribute [nolint simpNF] RegularExpression.epsilon.sizeOf_spec
attribute [nolint simpNF] RegularExpression.plus.sizeOf_spec
attribute [nolint simpNF] RegularExpression.plus.injEq
attribute [nolint simpNF] RegularExpression.comp.injEq
attribute [nolint simpNF] RegularExpression.comp.sizeOf_spec

namespace RegularExpression

variable {a b : α}

instance : Inhabited (RegularExpression α) :=
  ⟨zero⟩

instance : Add (RegularExpression α) :=
  ⟨plus⟩

instance : Mul (RegularExpression α) :=
  ⟨comp⟩

instance : One (RegularExpression α) :=
  ⟨epsilon⟩

instance : Zero (RegularExpression α) :=
  ⟨zero⟩

instance : Pow (RegularExpression α) ℕ :=
  ⟨fun n r => npowRec r n⟩

-- Porting note: declaration in an imported module
--attribute [match_pattern] Mul.mul

@[simp]
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl
#align regular_expression.zero_def RegularExpression.zero_def

@[simp]
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl
#align regular_expression.one_def RegularExpression.one_def

@[simp]
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q :=
  rfl
#align regular_expression.plus_def RegularExpression.plus_def

@[simp]
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q :=
  rfl
#align regular_expression.comp_def RegularExpression.comp_def

-- Porting note: `matches` is reserved, moved to `matches'`
#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- `matches' P` provides a language which contains all strings that `P` matches -/
-- Porting note: was '@[simp] but removed based on
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simpNF.20issues.20in.20Computability.2ERegularExpressions.20!4.232306/near/328355362
def matches' : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | comp P Q => P.matches' * Q.matches'
  | star P => P.matches'∗
#align regular_expression.matches RegularExpression.matches'

@[simp]
theorem matches'_zero : (0 : RegularExpression α).matches' = 0 :=
  rfl
#align regular_expression.matches_zero RegularExpression.matches'_zero

@[simp]
theorem matches'_epsilon : (1 : RegularExpression α).matches' = 1 :=
  rfl
#align regular_expression.matches_epsilon RegularExpression.matches'_epsilon

@[simp]
theorem matches'_char (a : α) : (char a).matches' = {[a]} :=
  rfl
#align regular_expression.matches_char RegularExpression.matches'_char

@[simp]
theorem matches'_add (P Q : RegularExpression α) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl
#align regular_expression.matches_add RegularExpression.matches'_add

@[simp]
theorem matches'_mul (P Q : RegularExpression α) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl
#align regular_expression.matches_mul RegularExpression.matches'_mul

@[simp]
theorem matches'_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).matches' = P.matches' ^ n
  | 0 => matches'_epsilon
  | n + 1 => (matches'_mul _ _).trans <| Eq.trans
      (congrFun (congrArg HMul.hMul (matches'_pow P n)) (matches' P))
      (pow_succ _ n).symm
#align regular_expression.matches_pow RegularExpression.matches'_pow

@[simp]
theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ :=
  rfl
#align regular_expression.matches_star RegularExpression.matches'_star

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | comp P Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true
#align regular_expression.match_epsilon RegularExpression.matchEpsilon

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | comp P Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P
#align regular_expression.deriv RegularExpression.deriv

@[simp]
theorem deriv_zero (a : α) : deriv 0 a = 0 :=
  rfl
#align regular_expression.deriv_zero RegularExpression.deriv_zero

@[simp]
theorem deriv_one (a : α) : deriv 1 a = 0 :=
  rfl
#align regular_expression.deriv_one RegularExpression.deriv_one

@[simp]
theorem deriv_char_self (a : α) : deriv (char a) a = 1 :=
  if_pos rfl
#align regular_expression.deriv_char_self RegularExpression.deriv_char_self

@[simp]
theorem deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 :=
  if_neg h
#align regular_expression.deriv_char_of_ne RegularExpression.deriv_char_of_ne

@[simp]
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl
#align regular_expression.deriv_add RegularExpression.deriv_add

@[simp]
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P :=
  rfl
#align regular_expression.deriv_star RegularExpression.deriv_star

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches'`. -/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as
#align regular_expression.rmatch RegularExpression.rmatch

@[simp]
theorem zero_rmatch (x : List α) : rmatch 0 x = false := by
  induction x <;> simp [rmatch, matchEpsilon, *]
#align regular_expression.zero_rmatch RegularExpression.zero_rmatch

theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [rmatch, matchEpsilon, *]
#align regular_expression.one_rmatch_iff RegularExpression.one_rmatch_iff

theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by
  cases' x with _ x
  · exact of_decide_eq_true rfl
  cases' x with head tail
  · rw [rmatch, deriv]
    split_ifs
    · tauto
    · simp [List.singleton_inj]; tauto
  · rw [rmatch, rmatch, deriv]
    split_ifs with h
    · simp only [deriv_one, zero_rmatch, cons.injEq, and_false]
    · simp only [deriv_zero, zero_rmatch, cons.injEq, and_false]
#align regular_expression.char_rmatch_iff RegularExpression.char_rmatch_iff

theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  induction' x with _ _ ih generalizing P Q
  · simp only [rmatch, matchEpsilon, Bool.or_eq_true_iff]
  · repeat rw [rmatch]
    rw [deriv_add]
    exact ih _ _
#align regular_expression.add_rmatch_iff RegularExpression.add_rmatch_iff

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by
  induction' x with a x ih generalizing P Q
  · rw [rmatch]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatch, rmatch]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      cases' List.append_eq_nil.1 h₁.symm with ht hu
      subst ht
      subst hu
      repeat rw [rmatch] at h₂
      simp [h₂]
  · rw [rmatch]; simp [deriv]
    split_ifs with hepsilon
    · rw [add_rmatch_iff, ih]
      constructor
      · rintro (⟨t, u, _⟩ | h)
        · exact ⟨a :: t, u, by tauto⟩
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
      · rintro ⟨t, u, h, hP, hQ⟩
        cases' t with b t
        · right
          rw [List.nil_append] at h
          rw [← h] at hQ
          exact hQ
        · left
          rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact ⟨a :: t, u, by tauto⟩
      · cases' t with b t
        · contradiction
        · rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
#align regular_expression.mul_rmatch_iff RegularExpression.mul_rmatch_iff

theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x
          = S.join ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t :=
  fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · cases' x with a x
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          omega
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases ht' with
          | head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatch]
            exact ht
          | tail _ ht' => exact helem t' ht'
    · rintro ⟨S, hsum, helem⟩
      cases' x with a x
      · rfl
      · rw [rmatch, deriv, mul_rmatch_iff]
        cases' S with t' U
        · exact ⟨[], [], by tauto⟩
        · cases' t' with b t
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [eq_self_iff_true, not_true, Ne, false_and_iff] at helem
          simp only [List.join, List.cons_append, List.cons_eq_cons] at hsum
          refine ⟨t, U.join, hsum.2, ?_, ?_⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatch] at helem
            convert helem.2
            exact hsum.1
          · have hwf : U.join.length < (List.cons a x).length := by
              rw [hsum.1, hsum.2]
              simp only [List.length_append, List.length_join, List.length]
              omega
            rw [IH _ hwf]
            refine ⟨U, rfl, fun t h => helem t ?_⟩
            right
            assumption
  termination_by t => (P, t.length)
#align regular_expression.star_rmatch_iff RegularExpression.star_rmatch_iff

@[simp]
theorem rmatch_iff_matches' (P : RegularExpression α) (x : List α) :
    P.rmatch x ↔ x ∈ P.matches' := by
  induction P generalizing x with
  | zero =>
    rw [zero_def, zero_rmatch]
    tauto
  | epsilon =>
    rw [one_def, one_rmatch_iff, matches'_epsilon, Language.mem_one]
  | char =>
    rw [char_rmatch_iff]
    rfl
  | plus _ _ ih₁ ih₂ =>
    rw [plus_def, add_rmatch_iff, ih₁, ih₂]
    rfl
  | comp P Q ih₁ ih₂ =>
    simp only [comp_def, mul_rmatch_iff, matches'_mul, Language.mem_mul, *]
    tauto
  | star _ ih =>
    simp only [star_rmatch_iff, matches'_star, ih, Language.mem_kstar_iff_exists_nonempty, and_comm]
#align regular_expression.rmatch_iff_matches RegularExpression.rmatch_iff_matches'

instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches') := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | comp R S => map f R * map f S
  | star R => star (map f R)
#align regular_expression.map RegularExpression.map

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => by dsimp; rfl
  | n + 1 => (congr_arg (· * map f P) (RegularExpression.map_pow f P n) : _)
#align regular_expression.map_pow RegularExpression.map_pow

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
@[simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | char a => rfl
  | R + S => by simp_rw [map, map_id]
  | comp R S => by simp_rw [map, map_id]; rfl
  | star R => by simp_rw [map, map_id]
#align regular_expression.map_id RegularExpression.map_id

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
@[simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | char a => rfl
  | R + S => by simp only [map, Function.comp_apply, map_map]
  | comp R S => by simp only [map, Function.comp_apply, map_map]
  | star R => by simp only [map, Function.comp_apply, map_map]
#align regular_expression.map_map RegularExpression.map_map

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp R S`,
  instead of `x * y` (and the `erw` was just `rw`). -/
/-- The language of the map is the map of the language. -/
@[simp]
theorem matches'_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    exact image_singleton
  -- Porting note: the following close with last `rw` but not with `simp`?
  | R + S => by simp only [matches'_map, map, matches'_add]; rw [map_add]
  | comp R S => by simp only [matches'_map, map, matches'_mul]; erw [map_mul]
  | star R => by
    simp_rw [map, matches', matches'_map]
    rw [Language.kstar_eq_iSup_pow, Language.kstar_eq_iSup_pow]
    simp_rw [← map_pow]
    exact image_iUnion.symm
#align regular_expression.matches_map RegularExpression.matches'_map

end RegularExpression
