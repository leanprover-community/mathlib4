/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson

! This file was ported from Lean 3 source module computability.regular_expressions
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Rcases
import Mathbin.Computability.Language

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent.
* `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.
-/


open List Set

open Computability

universe u

variable {α β γ : Type _} [dec : DecidableEq α]

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
  | zero : RegularExpression
  | epsilon : RegularExpression
  | Char : α → RegularExpression
  | plus : RegularExpression → RegularExpression → RegularExpression
  | comp : RegularExpression → RegularExpression → RegularExpression
  | star : RegularExpression → RegularExpression
#align regular_expression RegularExpression

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

attribute [match_pattern] Mul.mul

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

/-- `matches P` provides a language which contains all strings that `P` matches -/
@[simp]
def matches : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | Char a => {[a]}
  | P + Q => P.matches + Q.matches
  | P * Q => P.matches * Q.matches
  | star P => P.matches∗
#align regular_expression.matches RegularExpression.matches

@[simp]
theorem matches_zero : (0 : RegularExpression α).matches = 0 :=
  rfl
#align regular_expression.matches_zero RegularExpression.matches_zero

@[simp]
theorem matches_epsilon : (1 : RegularExpression α).matches = 1 :=
  rfl
#align regular_expression.matches_epsilon RegularExpression.matches_epsilon

@[simp]
theorem matches_char (a : α) : (char a).matches = {[a]} :=
  rfl
#align regular_expression.matches_char RegularExpression.matches_char

@[simp]
theorem matches_add (P Q : RegularExpression α) : (P + Q).matches = P.matches + Q.matches :=
  rfl
#align regular_expression.matches_add RegularExpression.matches_add

@[simp]
theorem matches_mul (P Q : RegularExpression α) : (P * Q).matches = P.matches * Q.matches :=
  rfl
#align regular_expression.matches_mul RegularExpression.matches_mul

@[simp]
theorem matches_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).matches = P.matches ^ n
  | 0 => matches_epsilon
  | n + 1 => (matches_mul _ _).trans <| Eq.trans (congr_arg _ (matches_pow n)) (pow_succ _ _).symm
#align regular_expression.matches_pow RegularExpression.matches_pow

@[simp]
theorem matches_star (P : RegularExpression α) : P.unit.matches = P.matches∗ :=
  rfl
#align regular_expression.matches_star RegularExpression.matches_star

/-- `match_epsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | Char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star P => true
#align regular_expression.match_epsilon RegularExpression.matchEpsilon

include dec

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | Char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
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
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.unit a = deriv P a * star P :=
  rfl
#align regular_expression.deriv_star RegularExpression.deriv_star

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches`. -/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as
#align regular_expression.rmatch RegularExpression.rmatch

@[simp]
theorem zero_rmatch (x : List α) : rmatch 0 x = false := by
  induction x <;> simp [rmatch, match_epsilon, *]
#align regular_expression.zero_rmatch RegularExpression.zero_rmatch

theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [rmatch, match_epsilon, *]
#align regular_expression.one_rmatch_iff RegularExpression.one_rmatch_iff

theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] :=
  by
  cases' x with _ x
  decide
  cases x
  rw [rmatch, deriv]
  split_ifs <;> tauto
  rw [rmatch, deriv]
  split_ifs
  rw [one_rmatch_iff]
  tauto
  rw [zero_rmatch]
  tauto
#align regular_expression.char_rmatch_iff RegularExpression.char_rmatch_iff

theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
  by
  induction' x with _ _ ih generalizing P Q
  · simp only [rmatch, match_epsilon, Bool.or_coe_iff]
  · repeat' rw [rmatch]
    rw [deriv]
    exact ih _ _
#align regular_expression.add_rmatch_iff RegularExpression.add_rmatch_iff

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
  by
  induction' x with a x ih generalizing P Q
  · rw [rmatch, match_epsilon]
    constructor
    · intro h
      refine' ⟨[], [], rfl, _⟩
      rw [rmatch, rmatch]
      rwa [Bool.and_coe_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      cases' List.append_eq_nil.1 h₁.symm with ht hu
      subst ht
      subst hu
      repeat' rw [rmatch] at h₂
      simp [h₂]
  · rw [rmatch, deriv]
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
          simp only [List.cons_append] at h
          refine' ⟨t, u, h.2, _, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact ⟨a :: t, u, by tauto⟩
      · cases' t with b t
        · contradiction
        · simp only [List.cons_append] at h
          refine' ⟨t, u, h.2, _, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
#align regular_expression.mul_rmatch_iff RegularExpression.mul_rmatch_iff

theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x = S.join ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t
  | x =>
    by
    have A : ∀ m n : ℕ, n < m + n + 1 := by
      intro m n
      convert add_lt_add_of_le_of_lt (add_le_add (zero_le m) (le_refl n)) zero_lt_one
      simp
    have IH := fun t (h : List.length t < List.length x) => star_rmatch_iff t
    clear star_rmatch_iff
    constructor
    · cases' x with a x
      · intro
        fconstructor
        exact []
        tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length :=
          by
          rw [hs, List.length_cons, List.length_append]
          apply A
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases' ht' with ht' ht'
          · rw [ht']
            exact ⟨by decide, ht⟩
          · exact helem _ ht'
    · rintro ⟨S, hsum, helem⟩
      cases' x with a x
      · decide
      · rw [rmatch, deriv, mul_rmatch_iff]
        cases' S with t' U
        · exact ⟨[], [], by tauto⟩
        · cases' t' with b t
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [eq_self_iff_true, not_true, Ne.def, false_and_iff] at helem
            cases helem
          simp only [List.join, List.cons_append] at hsum
          refine' ⟨t, U.join, hsum.2, _, _⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatch] at helem
            convert helem.2
            exact hsum.1
          · have hwf : U.join.length < (List.cons a x).length :=
              by
              rw [hsum.1, hsum.2]
              simp only [List.length_append, List.length_join, List.length]
              apply A
            rw [IH _ hwf]
            refine' ⟨U, rfl, fun t h => helem t _⟩
            right
            assumption termination_by'
  ⟨fun L₁ L₂ : List _ => L₁.length < L₂.length, InvImage.wf _ Nat.lt_wfRel⟩
#align regular_expression.star_rmatch_iff RegularExpression.star_rmatch_iff

@[simp]
theorem rmatch_iff_matches (P : RegularExpression α) : ∀ x : List α, P.rmatch x ↔ x ∈ P.matches :=
  by
  intro x
  induction P generalizing x
  all_goals
    try rw [zero_def]
    try rw [one_def]
    try rw [plus_def]
    try rw [comp_def]
    rw [matches]
  case zero =>
    rw [zero_rmatch]
    tauto
  case epsilon =>
    rw [one_rmatch_iff]
    rfl
  case char =>
    rw [char_rmatch_iff]
    rfl
  case plus _ _ ih₁ ih₂ =>
    rw [add_rmatch_iff, ih₁, ih₂]
    rfl
  case
    comp P Q ih₁ ih₂ =>
    simp only [mul_rmatch_iff, comp_def, Language.mul_def, exists_and_left, Set.mem_image2,
      Set.image_prod]
    constructor
    · rintro ⟨x, y, hsum, hmatch₁, hmatch₂⟩
      rw [ih₁] at hmatch₁
      rw [ih₂] at hmatch₂
      exact ⟨x, hmatch₁, y, hmatch₂, hsum.symm⟩
    · rintro ⟨x, hmatch₁, y, hmatch₂, hsum⟩
      rw [← ih₁] at hmatch₁
      rw [← ih₂] at hmatch₂
      exact ⟨x, y, hsum.symm, hmatch₁, hmatch₂⟩
  case star _ ih =>
    rw [star_rmatch_iff, Language.kstar_def_nonempty]
    constructor
    all_goals
      rintro ⟨S, hx, hS⟩
      refine' ⟨S, hx, _⟩
      intro y
      specialize hS y
    · rw [← ih y]
      tauto
    · rw [ih y]
      tauto
#align regular_expression.rmatch_iff_matches RegularExpression.rmatch_iff_matches

instance (P : RegularExpression α) : DecidablePred P.matches :=
  by
  intro x
  change Decidable (x ∈ P.matches)
  rw [← rmatch_iff_matches]
  exact Eq.decidable _ _

omit dec

/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | Char a => char (f a)
  | R + S => map R + map S
  | R * S => map R * map S
  | star R => star (map R)
#align regular_expression.map RegularExpression.map

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => rfl
  | n + 1 => (congr_arg ((· * ·) (map f P)) (map_pow n) : _)
#align regular_expression.map_pow RegularExpression.map_pow

@[simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | Char a => rfl
  | R + S => by simp_rw [map, map_id]
  | R * S => by simp_rw [map, map_id]
  | star R => by simp_rw [map, map_id]
#align regular_expression.map_id RegularExpression.map_id

@[simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | Char a => rfl
  | R + S => by simp_rw [map, map_map]
  | R * S => by simp_rw [map, map_map]
  | star R => by simp_rw [map, map_map]
#align regular_expression.map_map RegularExpression.map_map

/-- The language of the map is the map of the language. -/
@[simp]
theorem matches_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches = Language.map f P.matches
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | Char a => by
    rw [eq_comm]
    exact image_singleton
  | R + S => by simp only [matches_map, map, matches_add, map_add]
  | R * S => by simp only [matches_map, map, matches_mul, map_mul]
  | star R => by
    simp_rw [map, matches, matches_map]
    rw [Language.kstar_eq_supᵢ_pow, Language.kstar_eq_supᵢ_pow]
    simp_rw [← map_pow]
    exact image_Union.symm
#align regular_expression.matches_map RegularExpression.matches_map

end RegularExpression

