/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
module

public import Mathlib.Computability.Language

import Mathlib.Tactic.AdaptationNote

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regexes used in
computer science such as the POSIX standard.

## TODO

Currently, we do not show that regular expressions and DFAs/NFAs are equivalent.
Multiple competing PRs towards that goal are in review.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Regular.20languages.3A.20the.20review.20queue
-/

@[expose] public section

open List Set

open scoped Computability

universe u

variable {α β γ : Type*}

-- Disable generation of unneeded lemmas which the simpNF linter would complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- This is the definition of regular expressions. The names used here are meant to mirror the
[definition of a Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings that match `P`
* `P + Q` (`plus P Q`) matches anything that matches `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α

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

@[simp]
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl

@[simp]
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl

@[simp]
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q :=
  rfl

@[simp]
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q :=
  rfl

/-- `matches' P` provides a language which contains all strings that `P` matches.

Not named `matches` since that is a reserved word.
-/
@[simp]
def matches' : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => .ofSet {.of a}
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'
  | star P => P.matches'∗

theorem matches'_zero : (0 : RegularExpression α).matches' = 0 :=
  rfl

theorem matches'_epsilon : (1 : RegularExpression α).matches' = 1 :=
  rfl

theorem matches'_char (a : α) : (char a).matches' = .ofSet {.of a} :=
  rfl

theorem matches'_add (P Q : RegularExpression α) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl

theorem matches'_mul (P Q : RegularExpression α) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl

@[simp]
theorem matches'_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).matches' = P.matches' ^ n
  | 0 => matches'_epsilon
  | n + 1 => (matches'_mul _ _).trans <| Eq.trans
      congr($(matches'_pow P n) * (matches' P)) (pow_succ _ n).symm

theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ :=
  rfl

/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true

section DecidableEq
variable [DecidableEq α]

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

@[simp]
theorem deriv_zero (a : α) : deriv 0 a = 0 :=
  rfl

@[simp]
theorem deriv_one (a : α) : deriv 1 a = 0 :=
  rfl

@[simp]
theorem deriv_char_self (a : α) : deriv (char a) a = 1 :=
  ite_eq_left rfl

@[simp]
theorem deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 :=
  ite_eq_right h

@[simp]
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

@[simp]
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P :=
  rfl

/-- An auxiliary definition for `P.rmatch x` based on `x.toList`. -/
def rmatchL : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatchL (P.deriv a) as

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches'`. -/
def rmatch (P : RegularExpression α) (x : FreeMonoid α) : Bool :=
  P.rmatchL x.toList

@[simp]
lemma zero_rmatchL (x : List α) : rmatchL 0 x = false := by
  induction x <;> simp [rmatchL, matchEpsilon, *]

@[simp]
theorem zero_rmatch (x : FreeMonoid α) : rmatch 0 x = false := zero_rmatchL x.toList

lemma one_rmatchL_iff (x : List α) : rmatchL 1 x ↔ x = [] := by
  induction x <;> simp [rmatchL, matchEpsilon, *]

theorem one_rmatch_iff (x : FreeMonoid α) : rmatch 1 x ↔ x = 1 := by
  rw [rmatch, one_rmatchL_iff x.toList, FreeMonoid.ofList.injEq]
  exact Iff.rfl

lemma char_rmatchL_iff (a : α) (x : List α) : rmatchL (char a) x ↔ x = [a] := by
  rcases x with - | ⟨_, x⟩
  · exact of_decide_eq_true rfl
  · rcases x with - | ⟨head, tail⟩
    · rw [rmatchL, deriv, List.singleton_inj]
      split <;> tauto
    · rw [rmatchL, rmatchL, deriv, cons.injEq]
      split
      · simp_rw [deriv_one, zero_rmatchL, reduceCtorEq, and_false]
      · simp_rw [deriv_zero, zero_rmatchL, reduceCtorEq, and_false]

theorem char_rmatch_iff (a : α) (x : FreeMonoid α) : rmatch (char a) x ↔ x = .of a := by
  rw [rmatch, char_rmatchL_iff, FreeMonoid.ofList.injEq]
  exact Iff.rfl

lemma add_rmatchL_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatchL x ↔ P.rmatchL x ∨ Q.rmatchL x := by
  induction x generalizing P Q with
  | nil => simp only [rmatchL, matchEpsilon, Bool.or_eq_true_iff]
  | cons _ _ ih =>
    rw [rmatchL, deriv_add]
    exact ih ..

theorem add_rmatch_iff (P Q : RegularExpression α) (x : FreeMonoid α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  simp [rmatch, add_rmatchL_iff]

lemma mul_rmatchL_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatchL x ↔ ∃ t u, x = t ++ u ∧ P.rmatchL t ∧ Q.rmatchL u := by
  induction x generalizing P Q with
  | nil =>
    rw [rmatchL]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatchL, rmatchL]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h₁.symm
      repeat rw [rmatchL] at h₂
      simp [h₂]
  | cons a x ih =>
    rw [rmatchL]; simp only [deriv]
    split_ifs with hepsilon
    · rw [add_rmatchL_iff, ih]
      constructor
      · rintro (⟨t, u, _⟩ | h)
        · exact ⟨a :: t, u, by tauto⟩
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
      · rintro ⟨t, u, h, hP, hQ⟩
        rcases t with - | ⟨b, t⟩
        · right
          rw [List.nil_append] at h
          rw [← h] at hQ
          exact hQ
        · left
          rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatchL] at hP
          convert hP
          exact h.1
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact ⟨a :: t, u, by tauto⟩
      · rcases t with - | ⟨b, t⟩
        · contradiction
        · rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatchL] at hP
          convert hP
          exact h.1

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : FreeMonoid α) :
    (P * Q).rmatch x ↔ ∃ t u, x = t * u ∧ P.rmatch t ∧ Q.rmatch u := by
  simp [rmatch, mul_rmatchL_iff, FreeMonoid.exists, ← FreeMonoid.ofList.injEq]

lemma star_rmatchL_iff (P : RegularExpression α) :
    ∀ x, (star P).rmatchL x ↔ ∃ S : List (List α), x = S.flatten ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatchL t :=
  fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatchL_iff P t
    clear star_rmatchL_iff
    constructor
    · rcases x with - | ⟨a, x⟩
      · intro _h
        use []; dsimp; tauto
      · rw [rmatchL, deriv, mul_rmatchL_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          lia
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases ht' with
          | head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatchL, reduceCtorEq]
            exact ht
          | tail _ ht' => exact helem t' ht'
    · rintro ⟨S, hsum, helem⟩
      rcases x with - | ⟨a, x⟩
      · rfl
      · rw [rmatchL, deriv, mul_rmatchL_iff]
        rcases S with - | ⟨t', U⟩
        · exact ⟨[], [], by tauto⟩
        · obtain - | ⟨b, t⟩ := t'
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [not_true, Ne, false_and] at helem
          simp only [List.flatten_cons, List.cons_append, List.cons_eq_cons] at hsum
          refine ⟨t, U.flatten, hsum.2, ?_, ?_⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatchL] at helem
            convert helem.2
            exact hsum.1
          · grind
  termination_by t => (P, t.length)

theorem star_rmatch_iff (P : RegularExpression α) (x : FreeMonoid α) :
    (star P).rmatch x ↔ ∃ S : List (FreeMonoid α), x = S.prod ∧ ∀ t ∈ S, t ≠ 1 ∧ P.rmatch t := by
  simp_rw [rmatch, star_rmatchL_iff, ← FreeMonoid.ofList.injEq]
  constructor <;> rintro ⟨S, hS₁, hS₂⟩
  · refine ⟨S.map .ofList, by simp [← FreeMonoid.ofList_flatten, ← hS₁], fun y my ↦ ?_⟩
    rw [mem_map] at my
    obtain ⟨y, my, rfl⟩ := my
    specialize hS₂ _ my
    rwa [← FreeMonoid.toListEquiv.injective.ne_iff]
  · refine ⟨S.map FreeMonoid.toList, by simp [hS₁], fun l ml ↦ ?_⟩
    rw [mem_map] at ml
    obtain ⟨l, ml, rfl⟩ := ml
    specialize hS₂ _ ml
    rwa [← FreeMonoid.toListEquiv.injective.ne_iff] at hS₂

@[simp]
theorem rmatch_iff_matches' (P : RegularExpression α) (x : FreeMonoid α) :
    P.rmatch x ↔ x ∈ P.matches'.toSet := by
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
    simp only [star_rmatch_iff, matches'_star, ih, Language.mem_kstar_iff_exists_ne_one, and_comm]

instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches'.toSet) := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

end DecidableEq

/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | R * S => map f R * map f S
  | star R => star (map f R)

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => by unfold map; rfl
  | n + 1 => congr($(RegularExpression.map_pow f P n) * map f P)

@[simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | char _ => rfl
  | R + S => by simp_rw [map, map_id]
  | R * S => by simp_rw [map, map_id]
  | star R => by simp_rw [map, map_id]

@[simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | char _ => rfl
  | R + S => by simp only [map, map_map]
  | R * S => by simp only [map, map_map]
  | star R => by simp only [map, map_map]

/-- The language of the map is the map of the language. -/
@[simp]
theorem matches'_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    exact image_singleton
  | R + S => by simp only [matches'_map, map, matches'_add, map_add]
  | R * S => by simp [matches'_map]
  | star R => by simp [matches'_map]

end RegularExpression
