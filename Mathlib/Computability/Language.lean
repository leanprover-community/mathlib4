/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson

! This file was ported from Lean 3 source module computability.language
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Ring
import Mathbin.Data.List.Join
import Mathbin.Data.Set.Lattice

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/


open List Set

universe v

variable {α β γ : Type _}

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_mem[has_mem] (list[list] α) -/
/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_singleton[has_singleton] (list[list] α) -/
/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_insert[has_insert] (list[list] α) -/
/-- A language is a set of strings over an alphabet. -/
def Language (α) :=
  Set (List α)deriving
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_mem[has_mem] (list[list] α)»,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_singleton[has_singleton] (list[list] α)»,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_insert[has_insert] (list[list] α)»,
  CompleteBooleanAlgebra
#align language Language

namespace Language

variable {l m : Language α} {a b x : List α}

attribute [local reducible] Language

/-- Zero language has no elements. -/
instance : Zero (Language α) :=
  ⟨(∅ : Set _)⟩

/-- `1 : language α` contains only one element `[]`. -/
instance : One (Language α) :=
  ⟨{[]}⟩

instance : Inhabited (Language α) :=
  ⟨0⟩

/-- The sum of two languages is their union. -/
instance : Add (Language α) :=
  ⟨(· ∪ ·)⟩

/-- The product of two languages `l` and `m` is the language made of the strings `x ++ y` where
`x ∈ l` and `y ∈ m`. -/
instance : Mul (Language α) :=
  ⟨image2 (· ++ ·)⟩

theorem zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl
#align language.zero_def Language.zero_def

theorem one_def : (1 : Language α) = {[]} :=
  rfl
#align language.one_def Language.one_def

theorem add_def (l m : Language α) : l + m = l ∪ m :=
  rfl
#align language.add_def Language.add_def

theorem mul_def (l m : Language α) : l * m = image2 (· ++ ·) l m :=
  rfl
#align language.mul_def Language.mul_def

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def star (l : Language α) : Language α :=
  { x | ∃ S : List (List α), x = S.join ∧ ∀ y ∈ S, y ∈ l }
#align language.star Language.star

theorem star_def (l : Language α) :
    l.star = { x | ∃ S : List (List α), x = S.join ∧ ∀ y ∈ S, y ∈ l } :=
  rfl
#align language.star_def Language.star_def

@[simp]
theorem not_mem_zero (x : List α) : x ∉ (0 : Language α) :=
  id
#align language.not_mem_zero Language.not_mem_zero

@[simp]
theorem mem_one (x : List α) : x ∈ (1 : Language α) ↔ x = [] := by rfl
#align language.mem_one Language.mem_one

theorem nil_mem_one : [] ∈ (1 : Language α) :=
  Set.mem_singleton _
#align language.nil_mem_one Language.nil_mem_one

@[simp]
theorem mem_add (l m : Language α) (x : List α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
  Iff.rfl
#align language.mem_add Language.mem_add

theorem mem_mul : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a ++ b = x :=
  mem_image2
#align language.mem_mul Language.mem_mul

theorem append_mem_mul : a ∈ l → b ∈ m → a ++ b ∈ l * m :=
  mem_image2_of_mem
#align language.append_mem_mul Language.append_mem_mul

theorem mem_star : x ∈ l.star ↔ ∃ S : List (List α), x = S.join ∧ ∀ y ∈ S, y ∈ l :=
  Iff.rfl
#align language.mem_star Language.mem_star

theorem join_mem_star {S : List (List α)} (h : ∀ y ∈ S, y ∈ l) : S.join ∈ l.star :=
  ⟨S, rfl, h⟩
#align language.join_mem_star Language.join_mem_star

theorem nil_mem_star (l : Language α) : [] ∈ l.star :=
  ⟨[], rfl, fun _ => False.elim⟩
#align language.nil_mem_star Language.nil_mem_star

instance : Semiring (Language α) where
  add := (· + ·)
  add_assoc := union_assoc
  zero := 0
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  mul := (· * ·)
  mul_assoc _ _ _ := image2_assoc append_assoc
  zero_mul _ := image2_empty_left
  mul_zero _ := image2_empty_right
  one := 1
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n := if n = 0 then 0 else 1
  nat_cast_zero := rfl
  nat_cast_succ n := by cases n <;> simp [Nat.cast, add_def, zero_def]
  left_distrib _ _ _ := image2_union_right
  right_distrib _ _ _ := image2_union_left

@[simp]
theorem add_self (l : Language α) : l + l = l :=
  sup_idem
#align language.add_self Language.add_self

/-- Maps the alphabet of a language. -/
def map (f : α → β) : Language α →+* Language β
    where
  toFun := image (List.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
  map_mul' _ _ := image_image2_distrib <| map_append _
#align language.map Language.map

@[simp]
theorem map_id (l : Language α) : map id l = l := by simp [map]
#align language.map_id Language.map_id

@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : Language α) : map g (map f l) = map (g ∘ f) l := by
  simp [map, image_image]
#align language.map_map Language.map_map

theorem star_def_nonempty (l : Language α) :
    l.star = { x | ∃ S : List (List α), x = S.join ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ [] } :=
  by
  ext x
  constructor
  · rintro ⟨S, rfl, h⟩
    refine' ⟨S.filter fun l => ¬List.isEmpty l, by simp, fun y hy => _⟩
    rw [mem_filter, empty_iff_eq_nil] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy => (h y hy).1⟩
#align language.star_def_nonempty Language.star_def_nonempty

theorem le_iff (l m : Language α) : l ≤ m ↔ l + m = m :=
  sup_eq_right.symm
#align language.le_iff Language.le_iff

theorem le_mul_congr {l₁ l₂ m₁ m₂ : Language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ :=
  by
  intro h₁ h₂ x hx
  simp only [mul_def, exists_and_left, mem_image2, image_prod] at hx⊢
  tauto
#align language.le_mul_congr Language.le_mul_congr

theorem le_add_congr {l₁ l₂ m₁ m₂ : Language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ :=
  sup_le_sup
#align language.le_add_congr Language.le_add_congr

theorem mem_supr {ι : Sort v} {l : ι → Language α} {x : List α} : (x ∈ ⨆ i, l i) ↔ ∃ i, x ∈ l i :=
  mem_Union
#align language.mem_supr Language.mem_supr

theorem supr_mul {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) * m = ⨆ i, l i * m :=
  image2_unionᵢ_left _ _ _
#align language.supr_mul Language.supr_mul

theorem mul_supr {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (m * ⨆ i, l i) = ⨆ i, m * l i :=
  image2_unionᵢ_right _ _ _
#align language.mul_supr Language.mul_supr

theorem supr_add {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) + m = ⨆ i, l i + m :=
  supᵢ_sup
#align language.supr_add Language.supr_add

theorem add_supr {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (m + ⨆ i, l i) = ⨆ i, m + l i :=
  sup_supᵢ
#align language.add_supr Language.add_supr

theorem mem_pow {l : Language α} {x : List α} {n : ℕ} :
    x ∈ l ^ n ↔ ∃ S : List (List α), x = S.join ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l :=
  by
  induction' n with n ihn generalizing x
  · simp only [mem_one, pow_zero, length_eq_zero]
    constructor
    · rintro rfl
      exact ⟨[], rfl, rfl, fun y h => h.elim⟩
    · rintro ⟨_, rfl, rfl, _⟩
      rfl
  · simp only [pow_succ, mem_mul, ihn]
    constructor
    · rintro ⟨a, b, ha, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [forall_mem_cons] at hS
      exact ⟨a, _, hS.1, ⟨S, rfl, rfl, hS.2⟩, rfl⟩
#align language.mem_pow Language.mem_pow

theorem star_eq_supr_pow (l : Language α) : l.star = ⨆ i : ℕ, l ^ i :=
  by
  ext x
  simp only [mem_star, mem_supr, mem_pow]
  constructor
  · rintro ⟨S, rfl, hS⟩
    exact ⟨_, S, rfl, rfl, hS⟩
  · rintro ⟨_, S, rfl, rfl, hS⟩
    exact ⟨S, rfl, hS⟩
#align language.star_eq_supr_pow Language.star_eq_supr_pow

@[simp]
theorem map_star (f : α → β) (l : Language α) : map f (star l) = star (map f l) :=
  by
  rw [star_eq_supr_pow, star_eq_supr_pow]
  simp_rw [← map_pow]
  exact image_Union
#align language.map_star Language.map_star

theorem mul_self_star_comm (l : Language α) : l.star * l = l * l.star := by
  simp only [star_eq_supr_pow, mul_supr, supr_mul, ← pow_succ, ← pow_succ']
#align language.mul_self_star_comm Language.mul_self_star_comm

@[simp]
theorem one_add_self_mul_star_eq_star (l : Language α) : 1 + l * l.star = l.star :=
  by
  simp only [star_eq_supr_pow, mul_supr, ← pow_succ, ← pow_zero l]
  exact sup_supᵢ_nat_succ _
#align language.one_add_self_mul_star_eq_star Language.one_add_self_mul_star_eq_star

@[simp]
theorem one_add_star_mul_self_eq_star (l : Language α) : 1 + l.star * l = l.star := by
  rw [mul_self_star_comm, one_add_self_mul_star_eq_star]
#align language.one_add_star_mul_self_eq_star Language.one_add_star_mul_self_eq_star

theorem star_mul_le_right_of_mul_le_right (l m : Language α) : l * m ≤ m → l.star * m ≤ m :=
  by
  intro h
  rw [star_eq_supr_pow, supr_mul]
  refine' supᵢ_le _
  intro n
  induction' n with n ih
  · simp
  rw [pow_succ', mul_assoc (l ^ n) l m]
  exact le_trans (le_mul_congr le_rfl h) ih
#align language.star_mul_le_right_of_mul_le_right Language.star_mul_le_right_of_mul_le_right

theorem star_mul_le_left_of_mul_le_left (l m : Language α) : m * l ≤ m → m * l.star ≤ m :=
  by
  intro h
  rw [star_eq_supr_pow, mul_supr]
  refine' supᵢ_le _
  intro n
  induction' n with n ih
  · simp
  rw [pow_succ, ← mul_assoc m l (l ^ n)]
  exact le_trans (le_mul_congr h le_rfl) ih
#align language.star_mul_le_left_of_mul_le_left Language.star_mul_le_left_of_mul_le_left

end Language

