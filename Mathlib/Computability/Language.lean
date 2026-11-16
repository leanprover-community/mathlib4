/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Martin Dvorak, Rudy Peterson
-/
module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Tactic.DeriveFintype

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet.
Note that "strings" are implemented as lists over the alphabet.

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
  `l = m * l + n`, and `m` doesn't contain the empty string, then `l` is the language `m∗ * n`
-/

@[expose] public section

open List Set

open scoped Computability

variable {α β γ : Type*}

/-- A language is a set of strings over an alphabet. Implemented as a one-field structure. -/
@[ext]
structure Language (α : Type*) where
  /-- Convert a `Set (List α)` to a `Language α`. -/
  ofSet ::
  /-- The underlying set -/
  toSet : Set (List α)

namespace Language

/-- The natural equivalence between `Language α` and `Set (List α)`. -/
@[simps]
def toSetEquiv : Language α ≃ Set (List α) where
  toFun := toSet
  invFun := ofSet

instance : CompleteAtomicBooleanAlgebra (Language α) :=
  toSetEquiv.completeAtomicBooleanAlgebra

@[simp] lemma toSet_ofSet (s : Set (List α)) : (ofSet s).toSet = s := rfl
@[simp] lemma ofSet_toSet (s : Language α) : ofSet s.toSet = s := rfl

instance : Membership (List α) (Language α) where mem s a := a ∈ s.toSet
instance : Singleton (List α) (Language α) where singleton a := ofSet {a}
instance : Insert (List α) (Language α) where insert a s := ofSet (insert a s.toSet)

@[simp] lemma mem_toSet {s : Language α} {a : List α} : a ∈ s.toSet ↔ a ∈ s := Iff.rfl
@[simp] lemma mem_ofSet {s : Set (List α)} {a : List α} : a ∈ ofSet s ↔ a ∈ s := Iff.rfl
@[simp] lemma mem_singleton_iff {a b : List α} : a ∈ ({b} : Language α) ↔ a = b := Iff.rfl
@[simp] lemma toSet_singleton {a : List α} : toSet {a} = {a} := rfl
@[simp] lemma ofSet_singleton {a : List α} : ofSet {a} = {a} := rfl
@[simp] lemma toSet_insert {s : Language α} {a : List α} :
    (insert a s).toSet = insert a s.toSet := rfl
@[simp] lemma ofSet_insert {s : Set (List α)} {a : List α} :
    ofSet (insert a s) = insert a (ofSet s) := rfl

variable {l m : Language α} {a b x : List α}

/-- `0 : Language α` has no elements. -/
instance : Zero (Language α) where zero := ⟨∅⟩

/-- `1 : Language α` contains only one element `[]`. -/
instance : One (Language α) where one := ⟨{[]}⟩

instance : Inhabited (Language α) where default := 0

/-- The sum of two languages is their union. -/
instance : Add (Language α) where add l m := ⟨l.toSet ∪ m.toSet⟩

/-- The subtraction of two languages is their difference. -/
instance : Sub (Language α) where sub l m := ⟨l.toSet \ m.toSet⟩

/-- The product of two languages `l` and `m` is the language made of the strings `x ++ y` where
`x ∈ l` and `y ∈ m`. -/
instance : Mul (Language α) where mul l m := ⟨image2 (· ++ ·) l.toSet m.toSet⟩

theorem zero_def : (0 : Language α) = ⟨∅⟩ :=
  rfl

theorem one_def : (1 : Language α) = ⟨{[]}⟩ :=
  rfl

theorem add_def (l m : Language α) : l + m = ⟨l.toSet ∪ m.toSet⟩ :=
  rfl

theorem sub_def (l m : Language α) : l - m = ⟨l.toSet \ m.toSet⟩ :=
  rfl

theorem mul_def (l m : Language α) : l * m = ⟨image2 (· ++ ·) l.toSet m.toSet⟩ :=
  rfl

/-- The Kleene star of a language `L` is the set of all strings which can be written by
concatenating strings from `L`. -/
instance : KStar (Language α) where
  kstar l := ⟨{x | ∃ L : List (List α), x = L.flatten ∧ ∀ y ∈ L, y ∈ l}⟩

lemma kstar_def (l : Language α) :
    l∗ = ⟨{x | ∃ L : List (List α), x = L.flatten ∧ ∀ y ∈ L, y ∈ l}⟩ := rfl

@[simp]
theorem notMem_zero (x : List α) : x ∉ (0 : Language α) :=
  id

@[simp]
theorem mem_one (x : List α) : x ∈ (1 : Language α) ↔ x = [] := by rfl

theorem nil_mem_one : [] ∈ (1 : Language α) :=
  Set.mem_singleton _

theorem mem_add (l m : Language α) (x : List α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
  Iff.rfl

theorem mem_sub (l m : Language α) (x : List α) : x ∈ l - m ↔ x ∈ l ∧ x ∉ m :=
  Iff.rfl

theorem mem_mul : x ∈ l * m ↔ ∃ a ∈ l, ∃ b ∈ m, a ++ b = x :=
  mem_image2

theorem append_mem_mul : a ∈ l → b ∈ m → a ++ b ∈ l * m :=
  mem_image2_of_mem

theorem mem_kstar : x ∈ l∗ ↔ ∃ L : List (List α), x = L.flatten ∧ ∀ y ∈ L, y ∈ l :=
  Iff.rfl

theorem join_mem_kstar {L : List (List α)} (h : ∀ y ∈ L, y ∈ l) : L.flatten ∈ l∗ :=
  ⟨L, rfl, h⟩

theorem nil_mem_kstar (l : Language α) : [] ∈ l∗ :=
  ⟨[], rfl, fun _ h ↦ by contradiction⟩

instance : OrderedSub (Language α) where
  tsub_le_iff_right _ _ _ := sdiff_le_iff'

instance instSemiring : Semiring (Language α) where
  add_assoc _ _ _ := Language.ext (union_assoc ..)
  zero_add _ := Language.ext (empty_union _)
  add_zero _ := Language.ext (union_empty _)
  add_comm _ _ := Language.ext (union_comm ..)
  mul_assoc _ _ _ := Language.ext (image2_assoc append_assoc)
  zero_mul _ := Language.ext image2_empty_left
  mul_zero _ := Language.ext image2_empty_right
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n := if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp [add_def, zero_def]
  left_distrib _ _ _ := Language.ext image2_union_right
  right_distrib _ _ _ := Language.ext image2_union_left
  nsmul := nsmulRec

theorem add_self (l : Language α) : l + l = l :=
  sup_idem _

/-- Maps the alphabet of a language. -/
def map (f : α → β) : Language α →+* Language β where
  toFun l := ⟨l.toSet.image (List.map f)⟩
  map_zero' := Language.ext (image_empty _)
  map_one' := Language.ext image_singleton
  map_add' _ _ := Language.ext (image_union ..)
  map_mul' _ _ := Language.ext (image_image2_distrib fun _ _ ↦ map_append)

@[simp]
theorem map_id (l : Language α) : map id l = l := by simp [map]

@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : Language α) : map g (map f l) = map (g ∘ f) l := by
  simp [map, image_image]

lemma mem_kstar_iff_exists_nonempty {x : List α} :
    x ∈ l∗ ↔ ∃ S : List (List α), x = S.flatten ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ [] := by
  constructor
  · rintro ⟨S, rfl, h⟩
    refine ⟨S.filter fun l ↦ !List.isEmpty l,
      by simp [List.flatten_filter_not_isEmpty], fun y hy ↦ ?_⟩
    simp only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, isEmpty_eq_false_iff, ne_eq] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy ↦ (h y hy).1⟩

theorem kstar_def_nonempty (l : Language α) :
    l∗ = ⟨{x | ∃ S : List (List α), x = S.flatten ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ []}⟩ := by
  ext x; apply mem_kstar_iff_exists_nonempty

theorem le_iff (l m : Language α) : l ≤ m ↔ l + m = m :=
  sup_eq_right.symm

instance : MulLeftMono (Language α) where
  elim _ _ _ := image2_subset_left

instance : MulRightMono (Language α) where
  elim _ _ _ := image2_subset_right

@[simp] lemma toSet_iSup {ι : Sort*} (l : ι → Language α) : (⨆ i, l i).toSet = ⋃ i, (l i).toSet :=
  OrderIso.map_iSup ⟨toSetEquiv, Iff.rfl⟩ l

@[simp] lemma toSet_iInf {ι : Sort*} (l : ι → Language α) : (⨅ i, l i).toSet = ⋂ i, (l i).toSet :=
  OrderIso.map_iInf ⟨toSetEquiv, Iff.rfl⟩ l

theorem mem_iSup {ι : Sort*} {l : ι → Language α} {x : List α} : x ∈ ⨆ i, l i ↔ ∃ i, x ∈ l i := by
  simp [← mem_toSet]

theorem iSup_mul {ι : Sort*} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) * m = ⨆ i, l i * m := by ext; simp [mul_def, image2_iUnion_left]

theorem mul_iSup {ι : Sort*} (l : ι → Language α) (m : Language α) :
    m * ⨆ i, l i = ⨆ i, m * l i := by ext; simp [mul_def, image2_iUnion_right]

theorem iSup_add {ι : Sort*} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) + m = ⨆ i, l i + m :=
  iSup_sup

theorem add_iSup {ι : Sort*} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    m + ⨆ i, l i = ⨆ i, m + l i :=
  sup_iSup

theorem iSup_sub {ι : Sort*} (l : ι → Language α) (m : Language α) :
    (⨆ i, l i) - m = ⨆ i, l i - m := by ext; simp [sub_def]

theorem sub_iSup {ι : Sort*} [Nonempty ι] (l : ι → Language α) (m : Language α) :
    m - ⨆ i, l i = ⨅ i, m - l i := by ext; simp [sub_def, sdiff_iUnion]

theorem mem_pow {l : Language α} {x : List α} {n : ℕ} :
    x ∈ l ^ n ↔ ∃ S : List (List α), x = S.flatten ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l := by
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
  ext; simp [mem_kstar, mem_pow]

@[simp]
theorem map_kstar (f : α → β) (l : Language α) : map f l∗ = (map f l)∗ := by
  rw [kstar_eq_iSup_pow, kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  apply Language.ext
  simp [map, image_iUnion]

theorem mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

/-- This is the simp-normal form of `one_add_self_mul_kstar_eq_kstar`. -/
@[simp]
theorem one_sup_self_mul_kstar_eq_kstar (l : Language α) : 1 ⊔ l * l∗ = l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ', ← pow_zero l]
  exact sup_iSup_nat_succ (l ^ ·)

lemma one_add_self_mul_kstar_eq_kstar (l : Language α) : 1 + l * l∗ = l∗ :=
  one_sup_self_mul_kstar_eq_kstar _

/-- This is the simp-normal form of `one_add_kstar_mul_self_eq_kstar`. -/
@[simp]
theorem one_sup_kstar_mul_self_eq_kstar (l : Language α) : 1 ⊔ l∗ * l = l∗ := by
  rw [mul_self_kstar_comm, one_sup_self_mul_kstar_eq_kstar]

lemma one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗ :=
  one_sup_kstar_mul_self_eq_kstar _

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
theorem self_eq_mul_add_iff {l m n : Language α} (hm : [] ∉ m) : l = m * l + n ↔ l = m∗ * n where
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
      · exact ⟨[], nil_mem_kstar _, _, ⟨hx, nil_append _⟩⟩
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
def reverse (l : Language α) : Language α := ⟨{w | w.reverse ∈ l}⟩

@[simp]
lemma mem_reverse : a ∈ l.reverse ↔ a.reverse ∈ l := Iff.rfl

lemma reverse_mem_reverse : a.reverse ∈ l.reverse ↔ a ∈ l := by
  rw [mem_reverse, List.reverse_reverse]

lemma reverse_eq_image (l : Language α) : l.reverse = ⟨List.reverse '' l.toSet⟩ :=
  Language.ext ((reverse_involutive.toPerm _).image_eq_preimage_symm _).symm

lemma toSet_reverse (l : Language α) : l.reverse.toSet = List.reverse ⁻¹' l.toSet :=
  rfl

@[simp]
lemma reverse_zero : (0 : Language α).reverse = 0 := rfl

@[simp]
lemma reverse_one : (1 : Language α).reverse = 1 := by ext; simp

lemma reverse_involutive : Function.Involutive (reverse : Language α → _) := fun _ ↦
  Language.ext (List.reverse_involutive.preimage _)

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

@[simp]
lemma reverse_mul (l m : Language α) : (l * m).reverse = m.reverse * l.reverse := by
  apply Language.ext
  simp only [mul_def, reverse_eq_image, image2_image_left, image2_image_right, image_image2,
    List.reverse_append]
  apply image2_swap

@[simp]
lemma reverse_iSup {ι : Sort*} (l : ι → Language α) : (⨆ i, l i).reverse = ⨆ i, (l i).reverse := by
  apply Language.ext
  simp [toSet_reverse, preimage_iUnion]

@[simp]
lemma reverse_iInf {ι : Sort*} (l : ι → Language α) : (⨅ i, l i).reverse = ⨅ i, (l i).reverse := by
  apply Language.ext
  simp [toSet_reverse, preimage_iInter]

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
lemma mem_inf {x : List α} {l m : Language α} : x ∈ l ⊓ m ↔ x ∈ l ∧ x ∈ m := by
  apply Set.mem_inter_iff

lemma compl_compl (l : Language α) : lᶜᶜ = l :=
  _root_.compl_compl l

end Language
