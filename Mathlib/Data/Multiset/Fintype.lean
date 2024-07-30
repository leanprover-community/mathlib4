/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Multiset coercion to type

This module defines a `CoeSort` instance for multisets and gives it a `Fintype` instance.
It also defines `Multiset.toEnumFinset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`Finset` theory.

## Main definitions

* A coercion from `m : Multiset α` to a `Type*`. Each `x : m` has two components.
  The first, `x.1`, can be obtained via the coercion `↑x : α`,
  and it yields the underlying element of the multiset.
  The second, `x.2`, is a term of `Fin (m.count x)`,
  and its function is to ensure each term appears with the correct multiplicity.
  Note that this coercion requires `DecidableEq α` due to the definition using `Multiset.count`.
* `Multiset.toEnumFinset` is a `Finset` version of this.
* `Multiset.coeEmbedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `Multiset.coeEquiv` is the equivalence `m ≃ m.toEnumFinset`.

## Tags

multiset enumeration
-/


variable {α : Type*} [DecidableEq α] {m : Multiset α}

/-- Auxiliary definition for the `CoeSort` instance. This prevents the `CoeOut m α`
instance from inadvertently applying to other sigma types. -/
def Multiset.ToType (m : Multiset α) : Type _ := (x : α) × Fin (m.count x)

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times from different values of `i`. -/
instance : CoeSort (Multiset α) (Type _) := ⟨Multiset.ToType⟩

example : DecidableEq m := inferInstanceAs <| DecidableEq ((x : α) × Fin (m.count x))

-- Porting note: syntactic equality

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, match_pattern]
def Multiset.mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m :=
  ⟨x, i⟩

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
instance instCoeSortMultisetType.instCoeOutToType : CoeOut m α :=
  ⟨fun x ↦ x.1⟩

-- Porting note: syntactic equality

-- Syntactic equality

-- @[simp] -- Porting note (#10685): dsimp can prove this
theorem Multiset.coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl

@[simp] lemma Multiset.coe_mem {x : m} : ↑x ∈ m := Multiset.count_pos.mp (by have := x.2.2; omega)

@[simp]
protected theorem Multiset.forall_coe (p : m → Prop) :
    (∀ x : m, p x) ↔ ∀ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall

@[simp]
protected theorem Multiset.exists_coe (p : m → Prop) :
    (∃ x : m, p x) ↔ ∃ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists

instance : Fintype { p : α × ℕ | p.2 < m.count p.1 } :=
  Fintype.ofFinset
    (m.toFinset.biUnion fun x ↦ (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩)
    (by
      rintro ⟨x, i⟩
      simp only [Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Prod.mk.inj_iff, Set.mem_setOf_eq]
      simp only [← and_assoc, exists_eq_right, and_iff_right_iff_imp]
      exact fun h ↦ Multiset.count_pos.mp (by omega))

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `Finset`. -/
def Multiset.toEnumFinset (m : Multiset α) : Finset (α × ℕ) :=
  { p : α × ℕ | p.2 < m.count p.1 }.toFinset

@[simp]
theorem Multiset.mem_toEnumFinset (m : Multiset α) (p : α × ℕ) :
    p ∈ m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_toFinset

theorem Multiset.mem_of_mem_toEnumFinset {p : α × ℕ} (h : p ∈ m.toEnumFinset) : p.1 ∈ m :=
  have := (m.mem_toEnumFinset p).mp h; Multiset.count_pos.mp (by omega)

namespace Multiset

@[simp] lemma toEnumFinset_filter_eq (m : Multiset α) (a : α) :
    m.toEnumFinset.filter (·.1 = a) = {a} ×ˢ Finset.range (m.count a) := by aesop

@[simp] lemma map_toEnumFinset_fst (m : Multiset α) : m.toEnumFinset.val.map Prod.fst = m := by
  ext a; simp [count_map, ← Finset.filter_val, eq_comm (a := a)]

@[simp] lemma image_toEnumFinset_fst (m : Multiset α) :
    m.toEnumFinset.image Prod.fst = m.toFinset := by
  rw [Finset.image, Multiset.map_toEnumFinset_fst]

@[simp] lemma map_fst_le_of_subset_toEnumFinset {s : Finset (α × ℕ)} (hsm : s ⊆ m.toEnumFinset) :
    s.1.map Prod.fst ≤ m := by
  simp_rw [le_iff_count, count_map]
  rintro a
  obtain ha | ha := (s.1.filter fun x ↦ a = x.1).card.eq_zero_or_pos
  · rw [ha]
    exact Nat.zero_le _
  obtain ⟨n, han, hn⟩ : ∃ n ≥ card (s.1.filter fun x ↦ a = x.1) - 1, (a, n) ∈ s := by
    by_contra! h
    replace h : s.filter (·.1 = a) ⊆ {a} ×ˢ .range (card (s.1.filter fun x ↦ a = x.1) - 1) := by
      simpa (config := { contextual := true }) [forall_swap (β := _ = a), Finset.subset_iff,
        imp_not_comm, not_le, Nat.lt_sub_iff_add_lt] using h
    have : card (s.1.filter fun x ↦ a = x.1) ≤ card (s.1.filter fun x ↦ a = x.1) - 1 := by
      simpa [Finset.card, eq_comm] using Finset.card_mono h
    omega
  exact Nat.le_of_pred_lt (han.trans_lt $ by simpa using hsm hn)

end Multiset

@[mono]
theorem Multiset.toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ ≤ m₂) :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset := by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact gt_of_ge_of_gt (Multiset.le_iff_count.mp h p.1)

@[simp]
theorem Multiset.toEnumFinset_subset_iff {m₁ m₂ : Multiset α} :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset ↔ m₁ ≤ m₂ :=
  ⟨fun h ↦ by simpa using map_fst_le_of_subset_toEnumFinset h, Multiset.toEnumFinset_mono⟩

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.
If you are looking for the function `m → α`, that would be plain `(↑)`. -/
@[simps]
def Multiset.coeEmbedding (m : Multiset α) : m ↪ α × ℕ where
  toFun x := (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    rintro ⟨⟩
    rfl

/-- Another way to coerce a `Multiset` to a type is to go through `m.toEnumFinset` and coerce
that `Finset` to a type. -/
@[simps]
def Multiset.coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset where
  toFun x :=
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩
  left_inv := by
    rintro ⟨x, i, h⟩
    rfl
  right_inv := by
    rintro ⟨⟨x, i⟩, h⟩
    rfl

@[simp]
theorem Multiset.toEmbedding_coeEquiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by ext <;> rfl

@[irreducible]
instance Multiset.fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

theorem Multiset.map_univ_coeEmbedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset := by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk.inj_iff, exists_true_left, Multiset.exists_coe, Multiset.coe_mk, Fin.val_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, iff_self_iff,
    true_and_iff]

@[simp]
theorem Multiset.map_univ_coe (m : Multiset α) :
    (Finset.univ : Finset m).val.map (fun x : m ↦ (x : α)) = m := by
  have := m.map_toEnumFinset_fst
  rw [← m.map_univ_coeEmbedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this

@[simp]
theorem Multiset.map_univ {β : Type*} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map fun (x : m) ↦ f (x : α)) = m.map f := by
  erw [← Multiset.map_map, Multiset.map_univ_coe]

@[simp]
theorem Multiset.card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = Multiset.card m := by
  rw [Finset.card, ← Multiset.card_map Prod.fst m.toEnumFinset.val]
  congr
  exact m.map_toEnumFinset_fst

@[simp]
theorem Multiset.card_coe (m : Multiset α) : Fintype.card m = Multiset.card m := by
  rw [Fintype.card_congr m.coeEquiv]
  simp only [Fintype.card_coe, card_toEnumFinset]

@[to_additive]
theorem Multiset.prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.prod = ∏ x : m, (x : α) := by
  congr
  -- Porting note: `simp` fails with "maximum recursion depth has been reached"
  erw [map_univ_coe]

@[to_additive]
theorem Multiset.prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) :
    m.prod = ∏ x ∈ m.toEnumFinset, x.1 := by
  congr
  simp

@[to_additive]
theorem Multiset.prod_toEnumFinset {β : Type*} [CommMonoid β] (m : Multiset α) (f : α → ℕ → β) :
    ∏ x ∈ m.toEnumFinset, f x.1 x.2 = ∏ x : m, f x x.2 := by
  rw [Fintype.prod_equiv m.coeEquiv (fun x ↦ f x x.2) fun x ↦ f x.1.1 x.1.2]
  · rw [← m.toEnumFinset.prod_coe_sort fun x ↦ f x.1 x.2]
  · intro x
    rfl
