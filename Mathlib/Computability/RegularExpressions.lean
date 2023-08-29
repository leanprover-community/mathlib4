/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.Language

#align_import computability.regular_expressions from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent. -/

-- porting note: this has been commented out
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


-- porting note: `simpNF` gets grumpy about how the `foo_def`s below can simplify these..
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

-- porting note: declaration in an imported module
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

-- porting note: `matches` is reserved, moved to `matches'`
/-- `matches' P` provides a language which contains all strings that `P` matches -/
-- porting note: was '@[simp] but removed based on
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simpNF.20issues.20in.20Computability.2ERegularExpressions.20!4.232306/near/328355362
def matches' : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'
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
  | n + 1 => (matches'_mul _ _).trans <|
      Eq.trans (congr_arg _ (matches'_pow P n)) (pow_succ _ _).symm
#align regular_expression.matches_pow RegularExpression.matches'_pow

@[simp]
theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ :=
  rfl
#align regular_expression.matches_star RegularExpression.matches'_star

/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true
#align regular_expression.match_epsilon RegularExpression.matchEpsilon


/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
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
  -- ⊢ rmatch 0 [] = false
                  -- 🎉 no goals
                  -- 🎉 no goals
#align regular_expression.zero_rmatch RegularExpression.zero_rmatch

theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [rmatch, matchEpsilon, *]
  -- ⊢ rmatch 1 [] = true ↔ [] = []
                  -- 🎉 no goals
                  -- 🎉 no goals
#align regular_expression.one_rmatch_iff RegularExpression.one_rmatch_iff

theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by
  cases' x with _ x
  -- ⊢ rmatch (char a) [] = true ↔ [] = [a]
  · exact of_decide_eq_true rfl
    -- 🎉 no goals
  cases' x with head tail
  -- ⊢ rmatch (char a) [head✝] = true ↔ [head✝] = [a]
  · rw [rmatch, deriv]
    -- ⊢ rmatch (if a = head✝ then 1 else 0) [] = true ↔ [head✝] = [a]
    split_ifs
    -- ⊢ rmatch 1 [] = true ↔ [head✝] = [a]
    · tauto
      -- 🎉 no goals
    · simp [List.singleton_inj]; tauto
      -- ⊢ ¬head✝ = a
                                 -- 🎉 no goals
  · rw [rmatch, rmatch, deriv]
    -- ⊢ rmatch (deriv (if a = head✝ then 1 else 0) head) tail = true ↔ head✝ :: head …
    split_ifs with h
    -- ⊢ rmatch (deriv 1 head) tail = true ↔ head✝ :: head :: tail = [a]
    · simp only [deriv_one, zero_rmatch, cons.injEq, and_false]
      -- 🎉 no goals
    · simp only [deriv_zero, zero_rmatch, cons.injEq, and_false]
      -- 🎉 no goals
#align regular_expression.char_rmatch_iff RegularExpression.char_rmatch_iff

theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  induction' x with _ _ ih generalizing P Q
  -- ⊢ rmatch (P + Q) [] = true ↔ rmatch P [] = true ∨ rmatch Q [] = true
  · simp only [rmatch, matchEpsilon, Bool.or_coe_iff]
    -- 🎉 no goals
  · repeat' rw [rmatch]
    -- ⊢ rmatch (deriv (P + Q) head✝) tail✝ = true ↔ rmatch (deriv P head✝) tail✝ = t …
    rw [deriv_add]
    -- ⊢ rmatch (deriv P head✝ + deriv Q head✝) tail✝ = true ↔ rmatch (deriv P head✝) …
    exact ih _ _
    -- 🎉 no goals
#align regular_expression.add_rmatch_iff RegularExpression.add_rmatch_iff

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by
  induction' x with a x ih generalizing P Q
  -- ⊢ rmatch (P * Q) [] = true ↔ ∃ t u, [] = t ++ u ∧ rmatch P t = true ∧ rmatch Q …
  · rw [rmatch]; simp only [matchEpsilon]
    -- ⊢ matchEpsilon (P * Q) = true ↔ ∃ t u, [] = t ++ u ∧ rmatch P t = true ∧ rmatc …
                 -- ⊢ (matchEpsilon P && matchEpsilon Q) = true ↔ ∃ t u, [] = t ++ u ∧ rmatch P t  …
    constructor
    -- ⊢ (matchEpsilon P && matchEpsilon Q) = true → ∃ t u, [] = t ++ u ∧ rmatch P t  …
    · intro h
      -- ⊢ ∃ t u, [] = t ++ u ∧ rmatch P t = true ∧ rmatch Q u = true
      refine' ⟨[], [], rfl, _⟩
      -- ⊢ rmatch P [] = true ∧ rmatch Q [] = true
      rw [rmatch, rmatch]
      -- ⊢ matchEpsilon P = true ∧ matchEpsilon Q = true
      rwa [Bool.and_coe_iff] at h
      -- 🎉 no goals
    · rintro ⟨t, u, h₁, h₂⟩
      -- ⊢ (matchEpsilon P && matchEpsilon Q) = true
      cases' List.append_eq_nil.1 h₁.symm with ht hu
      -- ⊢ (matchEpsilon P && matchEpsilon Q) = true
      subst ht
      -- ⊢ (matchEpsilon P && matchEpsilon Q) = true
      subst hu
      -- ⊢ (matchEpsilon P && matchEpsilon Q) = true
      repeat' rw [rmatch] at h₂
      -- ⊢ (matchEpsilon P && matchEpsilon Q) = true
      simp [h₂]
      -- 🎉 no goals
  · rw [rmatch]; simp [deriv]
    -- ⊢ rmatch (deriv (P * Q) a) x = true ↔ ∃ t u, a :: x = t ++ u ∧ rmatch P t = tr …
                 -- ⊢ rmatch (if matchEpsilon P = true then deriv P a * Q + deriv Q a else deriv P …
    split_ifs with hepsilon
    -- ⊢ rmatch (deriv P a * Q + deriv Q a) x = true ↔ ∃ t u, a :: x = t ++ u ∧ rmatc …
    · rw [add_rmatch_iff, ih]
      -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true) ∨ rmat …
      constructor
      -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true) ∨ rmat …
      · rintro (⟨t, u, _⟩ | h)
        -- ⊢ ∃ t u, a :: x = t ++ u ∧ rmatch P t = true ∧ rmatch Q u = true
        · exact ⟨a :: t, u, by tauto⟩
          -- 🎉 no goals
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
          -- 🎉 no goals
      · rintro ⟨t, u, h, hP, hQ⟩
        -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true) ∨ rmat …
        cases' t with b t
        -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true) ∨ rmat …
        · right
          -- ⊢ rmatch (deriv Q a) x = true
          rw [List.nil_append] at h
          -- ⊢ rmatch (deriv Q a) x = true
          rw [← h] at hQ
          -- ⊢ rmatch (deriv Q a) x = true
          exact hQ
          -- 🎉 no goals
        · left
          -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true
          rw [List.cons_append, List.cons_eq_cons] at h
          -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true
          refine' ⟨t, u, h.2, _, hQ⟩
          -- ⊢ rmatch (deriv P a) t = true
          rw [rmatch] at hP
          -- ⊢ rmatch (deriv P a) t = true
          convert hP
          -- ⊢ a = b
          exact h.1
          -- 🎉 no goals
    · rw [ih]
      -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true) ↔ ∃ t  …
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true) → ∃ t  …
                      -- ⊢ ∃ t u, a :: x = t ++ u ∧ rmatch P t = true ∧ rmatch Q u = true
                      -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true
      · exact ⟨a :: t, u, by tauto⟩
        -- 🎉 no goals
      · cases' t with b t
        -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true
        · contradiction
          -- 🎉 no goals
        · rw [List.cons_append, List.cons_eq_cons] at h
          -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch Q u = true
          refine' ⟨t, u, h.2, _, hQ⟩
          -- ⊢ rmatch (deriv P a) t = true
          rw [rmatch] at hP
          -- ⊢ rmatch (deriv P a) t = true
          convert hP
          -- ⊢ a = b
          exact h.1
          -- 🎉 no goals
#align regular_expression.mul_rmatch_iff RegularExpression.mul_rmatch_iff

theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x
          = S.join ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t :=
  fun x => by
    have A : ∀ m n : ℕ, n < m + n + 1 := by
      intro m n
      convert add_lt_add_of_le_of_lt (add_le_add (zero_le m) (le_refl n)) zero_lt_one
      simp
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    -- ⊢ rmatch (star P) x = true ↔ ∃ S, x = join S ∧ ∀ (t : List α), t ∈ S → t ≠ []  …
    clear star_rmatch_iff
    -- ⊢ rmatch (star P) x = true ↔ ∃ S, x = join S ∧ ∀ (t : List α), t ∈ S → t ≠ []  …
    constructor
    -- ⊢ rmatch (star P) x = true → ∃ S, x = join S ∧ ∀ (t : List α), t ∈ S → t ≠ []  …
    · cases' x with a x
      -- ⊢ rmatch (star P) [] = true → ∃ S, [] = join S ∧ ∀ (t : List α), t ∈ S → t ≠ [ …
      · intro _h
        -- ⊢ ∃ S, [] = join S ∧ ∀ (t : List α), t ∈ S → t ≠ [] ∧ rmatch P t = true
        use []; dsimp; tauto
        -- ⊢ [] = join [] ∧ ∀ (t : List α), t ∈ [] → t ≠ [] ∧ rmatch P t = true
                -- ⊢ [] = [] ∧ ∀ (t : List α), t ∈ [] → ¬t = [] ∧ rmatch P t = true
                       -- 🎉 no goals
      · rw [rmatch, deriv, mul_rmatch_iff]
        -- ⊢ (∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch (star P) u = true) …
        rintro ⟨t, u, hs, ht, hu⟩
        -- ⊢ ∃ S, a :: x = join S ∧ ∀ (t : List α), t ∈ S → t ≠ [] ∧ rmatch P t = true
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          apply A
        rw [IH _ hwf] at hu
        -- ⊢ ∃ S, a :: x = join S ∧ ∀ (t : List α), t ∈ S → t ≠ [] ∧ rmatch P t = true
        rcases hu with ⟨S', hsum, helem⟩
        -- ⊢ ∃ S, a :: x = join S ∧ ∀ (t : List α), t ∈ S → t ≠ [] ∧ rmatch P t = true
        use (a :: t) :: S'
        -- ⊢ a :: x = join ((a :: t) :: S') ∧ ∀ (t_1 : List α), t_1 ∈ (a :: t) :: S' → t_ …
        constructor
        -- ⊢ a :: x = join ((a :: t) :: S')
        · simp [hs, hsum]
          -- 🎉 no goals
        · intro t' ht'
          -- ⊢ t' ≠ [] ∧ rmatch P t' = true
          cases ht'
          -- ⊢ a :: t ≠ [] ∧ rmatch P (a :: t) = true
          case head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatch]
            exact ht
          case tail ht' => exact helem t' ht'
          -- 🎉 no goals
          -- 🎉 no goals
    · rintro ⟨S, hsum, helem⟩
      -- ⊢ rmatch (star P) x = true
      cases' x with a x
      -- ⊢ rmatch (star P) [] = true
      · rfl
        -- 🎉 no goals
      · rw [rmatch, deriv, mul_rmatch_iff]
        -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch (star P) u = true
        cases' S with t' U
        -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch (star P) u = true
        · exact ⟨[], [], by tauto⟩
          -- 🎉 no goals
        · cases' t' with b t
          -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch (star P) u = true
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch (star P) u = true
            simp only [eq_self_iff_true, not_true, Ne.def, false_and_iff] at helem
            -- 🎉 no goals
          simp only [List.join, List.cons_append, List.cons_eq_cons] at hsum
          -- ⊢ ∃ t u, x = t ++ u ∧ rmatch (deriv P a) t = true ∧ rmatch (star P) u = true
          refine' ⟨t, U.join, hsum.2, _, _⟩
          -- ⊢ rmatch (deriv P a) t = true
          · specialize helem (b :: t) (by simp)
            -- ⊢ rmatch (deriv P a) t = true
            rw [rmatch] at helem
            -- ⊢ rmatch (deriv P a) t = true
            convert helem.2
            -- ⊢ a = b
            exact hsum.1
            -- 🎉 no goals
          · have hwf : U.join.length < (List.cons a x).length := by
              rw [hsum.1, hsum.2]
              simp only [List.length_append, List.length_join, List.length]
              apply A
            rw [IH _ hwf]
            -- ⊢ ∃ S, join U = join S ∧ ∀ (t : List α), t ∈ S → t ≠ [] ∧ rmatch P t = true
            refine' ⟨U, rfl, fun t h => helem t _⟩
            -- ⊢ t ∈ (b :: t✝) :: U
            right
            -- ⊢ Mem t U
            assumption
            -- 🎉 no goals
  termination_by star_rmatch_iff P t => (P,t.length)
#align regular_expression.star_rmatch_iff RegularExpression.star_rmatch_iff

@[simp]
theorem rmatch_iff_matches' (P : RegularExpression α) :
    ∀ x : List α, P.rmatch x ↔ x ∈ P.matches' := by
  intro x
  -- ⊢ rmatch P x = true ↔ x ∈ matches' P
  induction P generalizing x
  all_goals
    try rw [zero_def]
    try rw [one_def]
    try rw [plus_def]
    try rw [comp_def]
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
  case comp P Q ih₁ ih₂ =>
    simp only [mul_rmatch_iff, comp_def, Language.mul_def, exists_and_left, Set.mem_image2,
      Set.image_prod]
    constructor
    · rintro ⟨x, y, hsum, hmatch₁, hmatch₂⟩
      rw [ih₁] at hmatch₁
      rw [ih₂] at hmatch₂
      exact ⟨x, y, hmatch₁, hmatch₂, hsum.symm⟩
    · rintro ⟨x, y, hmatch₁, hmatch₂, hsum⟩
      rw [← ih₁] at hmatch₁
      rw [← ih₂] at hmatch₂
      exact ⟨x, y, hsum.symm, hmatch₁, hmatch₂⟩
  case star _ ih =>
    rw [star_rmatch_iff]
    simp only [ne_eq, matches', Language.kstar_def_nonempty, mem_setOf_eq]
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
#align regular_expression.rmatch_iff_matches RegularExpression.rmatch_iff_matches'

instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches') := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | R * S => map f R * map f S
  | star R => star (map f R)
#align regular_expression.map RegularExpression.map

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => by dsimp; rfl
            -- ⊢ 1 = map f P ^ 0
                   -- 🎉 no goals
  | n + 1 => (congr_arg ((· * ·) (map f P)) (RegularExpression.map_pow f P n) : _)
#align regular_expression.map_pow RegularExpression.map_pow

@[simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | char a => rfl
  | R + S => by simp_rw [map, map_id]
                -- 🎉 no goals
  | R * S => by simp_rw [map, map_id]
                -- 🎉 no goals
  | star R => by simp_rw [map, map_id]
                 -- 🎉 no goals
#align regular_expression.map_id RegularExpression.map_id

@[simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | char a => rfl
  | R + S => by simp only [map, Function.comp_apply, map_map]
                -- 🎉 no goals
  | R * S => by simp only [map, Function.comp_apply, map_map]
                -- 🎉 no goals
  | star R => by simp only [map, Function.comp_apply, map_map]
                 -- 🎉 no goals
#align regular_expression.map_map RegularExpression.map_map

/-- The language of the map is the map of the language. -/
@[simp]
theorem matches'_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    -- ⊢ ↑(Language.map f) (matches' (char a)) = matches' (map f (char a))
    exact image_singleton
    -- 🎉 no goals
  -- porting note: the following close with last `rw` but not with `simp`?
  | R + S => by simp only [matches'_map, map, matches'_add]; rw [map_add]
                -- ⊢ ↑(Language.map f) (matches' R) + ↑(Language.map f) (matches' S) = ↑(Language …
                                                             -- 🎉 no goals
  | R * S => by simp only [matches'_map, map, matches'_mul]; rw [map_mul]
                -- ⊢ ↑(Language.map f) (matches' R) * ↑(Language.map f) (matches' S) = ↑(Language …
                                                             -- 🎉 no goals
  | star R => by
    simp_rw [map, matches', matches'_map]
    -- ⊢ (↑(Language.map f) (matches' R))∗ = ↑(Language.map f) (matches' R)∗
    rw [Language.kstar_eq_iSup_pow, Language.kstar_eq_iSup_pow]
    -- ⊢ ⨆ (i : ℕ), ↑(Language.map f) (matches' R) ^ i = ↑(Language.map f) (⨆ (i : ℕ) …
    simp_rw [← map_pow]
    -- ⊢ ⨆ (i : ℕ), ↑(Language.map f) (matches' R ^ i) = ↑(Language.map f) (⨆ (i : ℕ) …
    exact image_iUnion.symm
    -- 🎉 no goals
#align regular_expression.matches_map RegularExpression.matches'_map

end RegularExpression
