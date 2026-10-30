/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Martin Dvorak, Rudy Peterson
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Semiring
public import Mathlib.Tactic.DeriveFintype

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Set.Lattice.Image

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet.
Note that strings are implemented as elements of `FreeMonoid α`.

Union and concatenation define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.

In addition to that, we define a reversal of a language and prove that it behaves well
with respect to other language operations.

## Notation

* `l + m`: union of languages `l` and `m`
* `l - m`: difference of languages `l` and `m`
* `l * m`: language of strings `x ++ y` such that `x ∈ l` and `y ∈ m`
* `l ^ n`: language of strings consisting of `n` members of `l` concatenated together
* `1`: language consisting of only the empty string. This is because it is the unit of the `*`
  operator.
* `l∗`: Kleene star – language of strings consisting of arbitrarily many members of `l`
  concatenated together. Note that this notation uses the Unicode asterisk operator `∗`, as opposed
  to the more common ASCII asterisk `*`.
* `lᶜ`: complement, language of strings `x` such that `x ∉ l`
* `l ⊓ m`: intersection of languages `l` and `m`

## Main definitions

* `Language α`: a set of strings over the alphabet `α`
* `l.map f`: transform a language `l` over `α` into a language over `β`
  by translating through `f : α → β`

## Main theorems

* `Language.self_eq_mul_add_iff`: Arden's lemma – if a language `l` satisfies the equation
  `l = m * l + n`, and `m` doesn't contain the empty string,
  then `l` is the language `m∗ * n`

-/

@[expose] public section

open List Set

open scoped Computability

universe v

variable {α β γ : Type*}

/-- A language is a `SetSemiring` of strings (elements of `FreeMonoid α`) over an alphabet `α`. -/
abbrev Language (α : Type*) := SetSemiring (FreeMonoid α)

namespace Language

variable {l m : Language α} {a b x : FreeMonoid α}

/-- The subtraction of two languages is their difference. -/
instance : Sub (Language α) where
  sub := (· \ ·)

theorem zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl

theorem one_def : (1 : Language α) = ({(1 : FreeMonoid α)} : Set _) :=
  rfl

theorem add_def (l m : Language α) : l + m = l.toSet ∪ m.toSet :=
  rfl

theorem sub_def (l m : Language α) : l - m = l.toSet \ m.toSet :=
  rfl

theorem mul_def (l m : Language α) : l * m = image2 (· * ·) l m :=
  rfl

/-- The Kleene star of a language `L` is the set of all strings which can be written by
concatenating strings from `L`. -/
instance : KStar (Language α) where
  kstar l := {x | ∃ L : List (FreeMonoid α), x = L.prod ∧ ∀ y ∈ L, y ∈ l.toSet}

lemma kstar_def (l : Language α) :
    l∗ = {x | ∃ L : List (FreeMonoid α), x = L.prod ∧ ∀ y ∈ L, y ∈ l.toSet} :=
  rfl

@[ext]
theorem ext (h : ∀ x, x ∈ l.toSet ↔ x ∈ m.toSet) : l = m :=
  Set.ext h

@[simp]
theorem notMem_zero (x : FreeMonoid α) : x ∉ (0 : Language α).toSet :=
  id

@[simp]
theorem mem_one (x : FreeMonoid α) : x ∈ (1 : Language α).toSet ↔ x = 1 := by rfl

theorem nil_mem_one : 1 ∈ (1 : Language α).toSet :=
  Set.mem_singleton _

theorem mem_add (l m : Language α) (x : FreeMonoid α) :
    x ∈ (l + m).toSet ↔ x ∈ l.toSet ∨ x ∈ m.toSet :=
  Iff.rfl

theorem mem_sub (l m : Language α) (x : FreeMonoid α) :
    x ∈ (l - m).toSet ↔ x ∈ l.toSet ∧ x ∉ m.toSet :=
  Iff.rfl

theorem mem_mul : x ∈ (l * m).toSet ↔ ∃ a ∈ l.toSet, ∃ b ∈ m.toSet, a * b = x :=
  mem_image2

theorem append_mem_mul : a ∈ l.toSet → b ∈ m.toSet → a * b ∈ (l * m).toSet :=
  mem_image2_of_mem

theorem mem_kstar : x ∈ l∗.toSet ↔ ∃ L : List (FreeMonoid α), x = L.prod ∧ ∀ y ∈ L, y ∈ l.toSet :=
  Iff.rfl

theorem join_mem_kstar {L : List (FreeMonoid α)} (h : ∀ y ∈ L, y ∈ l.toSet) : L.prod ∈ l∗.toSet :=
  ⟨L, rfl, h⟩

theorem nil_mem_kstar (l : Language α) : 1 ∈ l∗.toSet :=
  ⟨[], rfl, fun _ h ↦ by contradiction⟩

instance : OrderedSub (Language α) where
  tsub_le_iff_right _ _ _ := sdiff_le_iff'

@[simp]
theorem add_self (l : Language α) : l + l = l :=
  sup_idem _

/-- Maps the alphabet of a language. -/
def map (f : α → β) : Language α →+* Language β where
  toFun := image (FreeMonoid.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
  map_mul' _ _ := image_image2_distrib <| (FreeMonoid.map f).map_mul

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_id (l : Language α) : l.map id = l := by simp [map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : Language α) : map g (map f l) = map (g ∘ f) l := by
  simp [map, image_image]

lemma mem_kstar_iff_exists_ne_one {x : FreeMonoid α} :
    x ∈ l∗.toSet ↔ ∃ S : List (FreeMonoid α), x = S.prod ∧ ∀ y ∈ S, y ∈ l.toSet ∧ y ≠ 1 := by
  constructor
  · rintro ⟨S, rfl, h⟩
    classical
    refine ⟨S.filter fun l ↦ l ≠ 1, (prod_filter_bne_one S).symm, fun y hy ↦ ?_⟩
    rw [mem_filter, decide_eq_true_iff] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy ↦ (h y hy).1⟩

theorem kstar_def_ne_one (l : Language α) :
    l∗ = {x | ∃ S : List (FreeMonoid α), x = S.prod ∧ ∀ y ∈ S, y ∈ l.toSet ∧ y ≠ 1} := by
  ext x; apply mem_kstar_iff_exists_ne_one

@[deprecated (since := "2026-10-30")]
alias mem_kstar_iff_exists_nonempty := mem_kstar_iff_exists_ne_one
@[deprecated (since := "2026-10-30")] alias kstar_def_nonempty := kstar_def_ne_one

theorem le_iff (l m : Language α) : l ≤ m ↔ l + m = m :=
  sup_eq_right.symm

theorem mem_iSup {ι : Sort v} {l : ι → Language α} {x : FreeMonoid α} :
    (x ∈ (⨆ i, l i).toSet) ↔ ∃ i, x ∈ (l i).toSet :=
  mem_iUnion

theorem iSup_mul {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) * m = ⨆ i, l i * m :=
  image2_iUnion_left _ _ _

theorem mul_iSup {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (m * ⨆ i, l i) = ⨆ i, m * l i :=
  image2_iUnion_right _ _ _

theorem iSup_add {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) + m = ⨆ i, l i + m :=
  iSup_sup

theorem add_iSup {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (m + ⨆ i, l i) = ⨆ i, m + l i :=
  sup_iSup

theorem iSup_sub {ι : Sort v} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) - m = ⨆ i, l i - m :=
  iUnion_sdiff _ _

theorem sub_iSup {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (m - ⨆ i, l i) = ⨅ i, m - l i :=
  sdiff_iUnion _ _

theorem mem_pow {l : Language α} {x : FreeMonoid α} {n : ℕ} :
    x ∈ (l ^ n).toSet ↔
    ∃ S : List (FreeMonoid α), x = S.prod ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l.toSet := by
  induction n generalizing x with
  | zero => simp
  | succ n ihn =>
    simp only [pow_succ', mem_mul, ihn]
    constructor
    · rintro ⟨a, ha, b, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [forall_mem_cons] at hS
      exact ⟨a, hS.1, _, ⟨S, rfl, rfl, hS.2⟩, rfl⟩

theorem kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ i : ℕ, l ^ i := by
  ext x
  simp only [mem_kstar, mem_iSup, mem_pow]
  grind

@[simp]
theorem map_kstar (f : α → β) (l : Language α) : map f l∗ = (map f l)∗ := by
  rw [kstar_eq_iSup_pow, kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  exact image_iUnion

theorem mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

@[simp]
theorem one_add_self_mul_kstar_eq_kstar (l : Language α) : 1 + l * l∗ = l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ', ← pow_zero l]
  exact sup_iSup_nat_succ (l ^ ·)

@[simp]
theorem one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗ := by
  rw [mul_self_kstar_comm, one_add_self_mul_kstar_eq_kstar]

instance : KleeneAlgebra (Language α) where
  one_le_kstar a _ hl := ⟨[], hl, by simp⟩
  mul_kstar_le_kstar a := (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_kstar a := (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_self l m h := by
    rw [kstar_eq_iSup_pow, iSup_mul]
    refine iSup_le fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih => grw [pow_succ, mul_assoc, h, ih]
  mul_kstar_le_self l m h := by
    rw [kstar_eq_iSup_pow, mul_iSup]
    refine iSup_le fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih => grw [pow_succ, ← mul_assoc m (l ^ n) l, ih, h]

/-- **Arden's lemma** -/
theorem self_eq_mul_add_iff {l m n : Language α} (hm : 1 ∉ m.toSet) :
    l = m * l + n ↔ l = m∗ * n where
  mp h := by
    apply le_antisymm
    · intro x hx
      induction hlen : x.length using Nat.strong_induction_on generalizing x with | _ _ ih
      subst hlen
      rw [h] at hx
      obtain hx | hx := hx
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hx
        rw [length_append] at ih
        have hal : 0 < a.length := length_pos_iff.mpr <| ne_of_mem_of_not_mem ha hm
        specialize ih b.length (Nat.lt_add_left_iff_pos.mpr hal) hb rfl
        rw [← one_add_self_mul_kstar_eq_kstar, one_add_mul, mul_assoc]
        right
        exact ⟨_, ha, _, ih, rfl⟩
      · exact ⟨1, nil_mem_kstar _, _, ⟨hx, one_mul _⟩⟩
    · rw [kstar_eq_iSup_pow, iSup_mul, iSup_le_iff]
      intro i
      induction i with rw [h]
      | zero =>
        rw [pow_zero, one_mul, add_comm]
        exact le_self_add
      | succ _ ih =>
        grw [add_comm, pow_add, pow_one, mul_assoc, ih]
        exact le_self_add
  mpr h := by rw [h, add_comm, ← mul_assoc, ← one_add_mul, one_add_self_mul_kstar_eq_kstar]

/-- Language `l.reverse` is defined as the set of words from `l` backwards. -/
def reverse (l : Language α) : Language α := { w : List α | w.reverse ∈ l }

@[simp]
lemma mem_reverse : a ∈ l.reverse ↔ a.reverse ∈ l := Iff.rfl

lemma reverse_mem_reverse : a.reverse ∈ l.reverse ↔ a ∈ l := by
  rw [mem_reverse, List.reverse_reverse]

lemma reverse_eq_image (l : Language α) : l.reverse = List.reverse '' l :=
  ((List.reverse_involutive.toPerm _).image_eq_preimage_symm _).symm

@[simp]
lemma reverse_zero : (0 : Language α).reverse = 0 := rfl

@[simp]
lemma reverse_one : (1 : Language α).reverse = 1 := by
  simp [reverse, ← one_def]

lemma reverse_involutive : Function.Involutive (reverse : Language α → _) :=
  List.reverse_involutive.preimage

lemma reverse_bijective : Function.Bijective (reverse : Language α → _) :=
  reverse_involutive.bijective

lemma reverse_injective : Function.Injective (reverse : Language α → _) :=
  reverse_involutive.injective

lemma reverse_surjective : Function.Surjective (reverse : Language α → _) :=
  reverse_involutive.surjective

@[simp]
lemma reverse_reverse (l : Language α) : l.reverse.reverse = l := reverse_involutive l

@[simp]
lemma reverse_add (l m : Language α) : (l + m).reverse = l.reverse + m.reverse := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma reverse_mul (l m : Language α) : (l * m).reverse = m.reverse * l.reverse := by
  simp only [mul_def, reverse_eq_image, image2_image_left, image2_image_right, image_image2,
    List.reverse_append]
  apply image2_swap

@[simp]
lemma reverse_iSup {ι : Sort*} (l : ι → Language α) : (⨆ i, l i).reverse = ⨆ i, (l i).reverse :=
  preimage_iUnion

@[simp]
lemma reverse_iInf {ι : Sort*} (l : ι → Language α) : (⨅ i, l i).reverse = ⨅ i, (l i).reverse :=
  preimage_iInter

variable (α) in
/-- `Language.reverse` as a ring isomorphism to the opposite ring. -/
@[simps]
def reverseIso : Language α ≃+* (Language α)ᵐᵒᵖ where
  toFun l := .op l.reverse
  invFun l' := l'.unop.reverse
  left_inv := reverse_reverse
  right_inv l' := MulOpposite.unop_injective <| reverse_reverse l'.unop
  map_mul' l₁ l₂ := MulOpposite.unop_injective <| reverse_mul l₁ l₂
  map_add' l₁ l₂ := MulOpposite.unop_injective <| reverse_add l₁ l₂

@[simp]
lemma reverse_pow (l : Language α) (n : ℕ) : (l ^ n).reverse = l.reverse ^ n :=
  MulOpposite.op_injective (map_pow (reverseIso α) l n)

@[simp]
lemma reverse_kstar (l : Language α) : l∗.reverse = l.reverse∗ := by
  simp only [kstar_eq_iSup_pow, reverse_iSup, reverse_pow]

@[simp]
lemma mem_inf {x : FreeMonoid α} {l m : Language α} :
    x ∈ (l ⊓ m).toSet ↔ x ∈ l.toSet ∧ x ∈ m.toSet := by
  apply Set.mem_inter_iff

lemma compl_compl (l : Language α) : lᶜᶜ = l :=
  _root_.compl_compl l

end Language

/-- Symbols for use by all kinds of grammars. -/
inductive Symbol (T N : Type*)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr, Fintype

attribute [nolint docBlame] Symbol.proxyType Symbol.proxyTypeEquiv
