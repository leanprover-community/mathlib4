/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Prod.Lex

#align_import data.multiset.fintype from "leanprover-community/mathlib"@"e3d9ab8faa9dea8f78155c6c27d62a621f4c152d"

/-!
# Multiset coercion to type

This module defines a `hasCoeToSort` instance for multisets and gives it a `Fintype` instance.
It also defines `Multiset.toEnumFinset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`Finset` theory.

## Main definitions

* A coercion from `m : Multiset α` to a `Type*`. For `x : m`, then there is a coercion `↑x : α`,
  and `x.2` is a term of `Fin (m.count x)`. The second component is what ensures each term appears
  with the correct multiplicity. Note that this coercion requires `decidableEq α` due to
  `Multiset.count`.
* `Multiset.toEnumFinset` is a `Finset` version of this.
* `Multiset.coeEmbedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `Multiset.coeEquiv` is the equivalence `m ≃ m.toEnumFinset`.

## Tags

multiset enumeration
-/


open BigOperators

variable {α : Type*} [DecidableEq α] {m : Multiset α}

/-- Auxiliary definition for the `hasCoeToSort` instance. This prevents the `hasCoe m α`
instance from inadvertently applying to other sigma types. One should not use this definition
directly. -/
-- Porting note: @[nolint has_nonempty_instance]
def Multiset.ToType (m : Multiset α) : Type _ :=
  Σx : α, Fin (m.count x)
#align multiset.to_type Multiset.ToType

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times with different values of `i`. -/
instance : CoeSort (Multiset α) (Type _) :=
  ⟨Multiset.ToType⟩

-- Porting note: syntactic equality
#noalign multiset.coe_sort_eq

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, match_pattern]
def Multiset.mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m :=
  ⟨x, i⟩
#align multiset.mk_to_type Multiset.mkToType

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
-- Porting note: was `Coe m α`
instance instCoeSortMultisetType.instCoeOutToType : CoeOut m α :=
  ⟨fun x ↦ x.1⟩
#align multiset.has_coe_to_sort.has_coe instCoeSortMultisetType.instCoeOutToTypeₓ

-- Porting note: syntactic equality
#noalign multiset.fst_coe_eq_coe

@[simp]
theorem Multiset.coe_eq {x y : m} : (x : α) = (y : α) ↔ x.1 = y.1 := by
  cases x
  -- ⊢ { fst := fst✝, snd := snd✝ }.fst = y.fst ↔ { fst := fst✝, snd := snd✝ }.fst  …
  cases y
  -- ⊢ { fst := fst✝¹, snd := snd✝¹ }.fst = { fst := fst✝, snd := snd✝ }.fst ↔ { fs …
  rfl
  -- 🎉 no goals
#align multiset.coe_eq Multiset.coe_eq

-- @[simp] -- Porting note: dsimp can prove this
theorem Multiset.coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl
#align multiset.coe_mk Multiset.coe_mk

@[simp]
theorem Multiset.coe_mem {x : m} : ↑x ∈ m :=
  Multiset.count_pos.mp (pos_of_gt x.2.2)
#align multiset.coe_mem Multiset.coe_mem

@[simp]
protected theorem Multiset.forall_coe (p : m → Prop) :
    (∀ x : m, p x) ↔ ∀ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall
#align multiset.forall_coe Multiset.forall_coe

@[simp]
protected theorem Multiset.exists_coe (p : m → Prop) :
    (∃ x : m, p x) ↔ ∃ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists
#align multiset.exists_coe Multiset.exists_coe

instance : Fintype { p : α × ℕ | p.2 < m.count p.1 } :=
  Fintype.ofFinset
    (m.toFinset.biUnion fun x ↦ (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩)
    (by
      rintro ⟨x, i⟩
      -- ⊢ ((x, i) ∈ Finset.biUnion (Multiset.toFinset m) fun x => Finset.map { toFun : …
      simp only [Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Prod.mk.inj_iff, Set.mem_setOf_eq]
      simp only [←and_assoc, exists_eq_right, and_iff_right_iff_imp]
      -- ⊢ i < Multiset.count x m → x ∈ m
      exact fun h ↦ Multiset.count_pos.mp (pos_of_gt h))
      -- 🎉 no goals

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `Finset`. -/
def Multiset.toEnumFinset (m : Multiset α) : Finset (α × ℕ) :=
  { p : α × ℕ | p.2 < m.count p.1 }.toFinset
#align multiset.to_enum_finset Multiset.toEnumFinset

@[simp]
theorem Multiset.mem_toEnumFinset (m : Multiset α) (p : α × ℕ) :
    p ∈ m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_toFinset
#align multiset.mem_to_enum_finset Multiset.mem_toEnumFinset

theorem Multiset.mem_of_mem_toEnumFinset {p : α × ℕ} (h : p ∈ m.toEnumFinset) : p.1 ∈ m :=
  Multiset.count_pos.mp <| pos_of_gt <| (m.mem_toEnumFinset p).mp h
#align multiset.mem_of_mem_to_enum_finset Multiset.mem_of_mem_toEnumFinset

@[mono]
theorem Multiset.toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ ≤ m₂) :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset := by
  intro p
  -- ⊢ p ∈ toEnumFinset m₁ → p ∈ toEnumFinset m₂
  simp only [Multiset.mem_toEnumFinset]
  -- ⊢ p.snd < count p.fst m₁ → p.snd < count p.fst m₂
  exact gt_of_ge_of_gt (Multiset.le_iff_count.mp h p.1)
  -- 🎉 no goals
#align multiset.to_enum_finset_mono Multiset.toEnumFinset_mono

@[simp]
theorem Multiset.toEnumFinset_subset_iff {m₁ m₂ : Multiset α} :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset ↔ m₁ ≤ m₂ := by
  refine' ⟨fun h ↦ _, Multiset.toEnumFinset_mono⟩
  -- ⊢ m₁ ≤ m₂
  rw [Multiset.le_iff_count]
  -- ⊢ ∀ (a : α), count a m₁ ≤ count a m₂
  intro x
  -- ⊢ count x m₁ ≤ count x m₂
  by_cases hx : x ∈ m₁
  -- ⊢ count x m₁ ≤ count x m₂
  · apply Nat.le_of_pred_lt
    -- ⊢ Nat.pred (count x m₁) < count x m₂
    have : (x, m₁.count x - 1) ∈ m₁.toEnumFinset := by
      rw [Multiset.mem_toEnumFinset]
      exact Nat.pred_lt (ne_of_gt (Multiset.count_pos.mpr hx))
    simpa only [Multiset.mem_toEnumFinset] using h this
    -- 🎉 no goals
  · simp [hx]
    -- 🎉 no goals
#align multiset.to_enum_finset_subset_iff Multiset.toEnumFinset_subset_iff

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.
If you are looking for the function `m → α`, that would be plain `(↑)`. -/
@[simps]
def Multiset.coeEmbedding (m : Multiset α) : m ↪ α × ℕ
    where
  toFun x := (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    -- ⊢ (fun x => (x.fst, ↑x.snd)) { fst := x, snd := { val := i, isLt := hi } } = ( …
    rintro ⟨⟩
    -- ⊢ { fst := x, snd := { val := i, isLt := hi } } = { fst := x, snd := { val :=  …
    rfl
    -- 🎉 no goals
#align multiset.coe_embedding Multiset.coeEmbedding

/-- Another way to coerce a `Multiset` to a type is to go through `m.toEnumFinset` and coerce
that `Finset` to a type. -/
@[simps]
def Multiset.coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset
    where
  toFun x :=
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      -- ⊢ (↑(coeEmbedding m) x).snd < count (↑(coeEmbedding m) x).fst m
      exact x.2.2⟩
      -- 🎉 no goals
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      -- ⊢ ↑x ∈ toEnumFinset m
      exact x.2⟩
      -- 🎉 no goals
  left_inv := by
    rintro ⟨x, i, h⟩
    -- ⊢ (fun x => { fst := (↑x).fst, snd := { val := (↑x).snd, isLt := (_ : (↑x).snd …
    rfl
    -- 🎉 no goals
  right_inv := by
    rintro ⟨⟨x, i⟩, h⟩
    -- ⊢ (fun x => { val := ↑(coeEmbedding m) x, property := (_ : ↑(coeEmbedding m) x …
    rfl
    -- 🎉 no goals
#align multiset.coe_equiv Multiset.coeEquiv

@[simp]
theorem Multiset.toEmbedding_coeEquiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by ext <;> rfl
                                                                                       -- ⊢ (↑(Function.Embedding.trans (Equiv.toEmbedding (coeEquiv m)) (Function.Embed …
                                                                                               -- 🎉 no goals
                                                                                               -- 🎉 no goals
#align multiset.to_embedding_coe_equiv_trans Multiset.toEmbedding_coeEquiv_trans

@[irreducible]
instance Multiset.fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm
#align multiset.fintype_coe Multiset.fintypeCoe

theorem Multiset.map_univ_coeEmbedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset := by
  ext ⟨x, i⟩
  -- ⊢ (x, i) ∈ Finset.map (coeEmbedding m) Finset.univ ↔ (x, i) ∈ toEnumFinset m
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk.inj_iff, exists_true_left, Multiset.exists_coe, Multiset.coe_mk, Fin.val_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, iff_self_iff,
    true_and_iff]
#align multiset.map_univ_coe_embedding Multiset.map_univ_coeEmbedding

theorem Multiset.toEnumFinset_filter_eq (m : Multiset α) (x : α) :
    (m.toEnumFinset.filter fun p ↦ x = p.1) =
      (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩ := by
  ext ⟨y, i⟩
  -- ⊢ (y, i) ∈ Finset.filter (fun p => x = p.fst) (toEnumFinset m) ↔ (y, i) ∈ Fins …
  simp only [eq_comm, Finset.mem_filter, Multiset.mem_toEnumFinset, Finset.mem_map,
    Finset.mem_range, Function.Embedding.coeFn_mk, Prod.mk.inj_iff, exists_prop,
    exists_eq_right_right', and_congr_left_iff]
  rintro rfl
  -- ⊢ i < count x m ↔ i < count x m
  rfl
  -- 🎉 no goals
#align multiset.to_enum_finset_filter_eq Multiset.toEnumFinset_filter_eq

@[simp]
theorem Multiset.map_toEnumFinset_fst (m : Multiset α) : m.toEnumFinset.val.map Prod.fst = m := by
  ext x
  -- ⊢ count x (map Prod.fst (toEnumFinset m).val) = count x m
  simp only [Multiset.count_map, ← Finset.filter_val, Multiset.toEnumFinset_filter_eq,
    Finset.map_val, Finset.range_val, Multiset.card_map, Multiset.card_range]
#align multiset.map_to_enum_finset_fst Multiset.map_toEnumFinset_fst

@[simp]
theorem Multiset.image_toEnumFinset_fst (m : Multiset α) :
    m.toEnumFinset.image Prod.fst = m.toFinset := by
  rw [Finset.image, Multiset.map_toEnumFinset_fst]
  -- 🎉 no goals
#align multiset.image_to_enum_finset_fst Multiset.image_toEnumFinset_fst

@[simp]
theorem Multiset.map_univ_coe (m : Multiset α) :
    (Finset.univ : Finset m).val.map (fun x : m ↦ (x : α)) = m := by
  have := m.map_toEnumFinset_fst
  -- ⊢ map (fun x => x.fst) Finset.univ.val = m
  rw [← m.map_univ_coeEmbedding] at this
  -- ⊢ map (fun x => x.fst) Finset.univ.val = m
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this
#align multiset.map_univ_coe Multiset.map_univ_coe

@[simp]
theorem Multiset.map_univ {β : Type*} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map fun (x : m) ↦ f (x : α)) = m.map f := by
  erw [← Multiset.map_map]
  -- ⊢ map f (map (fun x => x.fst) Finset.univ.val) = map f m
  rw [Multiset.map_univ_coe]
  -- 🎉 no goals
#align multiset.map_univ Multiset.map_univ

@[simp]
theorem Multiset.card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = Multiset.card m := by
  rw [Finset.card, ←Multiset.card_map Prod.fst m.toEnumFinset.val]
  -- ⊢ ↑card (map Prod.fst (toEnumFinset m).val) = ↑card m
  congr
  -- ⊢ map Prod.fst (toEnumFinset m).val = m
  exact m.map_toEnumFinset_fst
  -- 🎉 no goals
#align multiset.card_to_enum_finset Multiset.card_toEnumFinset

@[simp]
theorem Multiset.card_coe (m : Multiset α) : Fintype.card m = Multiset.card m := by
  rw [Fintype.card_congr m.coeEquiv]
  -- ⊢ Fintype.card { x // x ∈ toEnumFinset m } = ↑card m
  simp only [Fintype.card_coe, card_toEnumFinset]
  -- 🎉 no goals
#align multiset.card_coe Multiset.card_coe

@[to_additive]
theorem Multiset.prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.prod = ∏ x : m, (x : α) := by
  congr
  -- ⊢ m = map (fun x => x.fst) Finset.univ.val
  -- Porting note: `simp` fails with "maximum recursion depth has been reached"
  erw [map_univ_coe]
  -- 🎉 no goals
#align multiset.prod_eq_prod_coe Multiset.prod_eq_prod_coe
#align multiset.sum_eq_sum_coe Multiset.sum_eq_sum_coe

@[to_additive]
theorem Multiset.prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) :
    m.prod = ∏ x in m.toEnumFinset, x.1 := by
  congr
  -- ⊢ m = map (fun x => x.fst) (toEnumFinset m).val
  simp
  -- 🎉 no goals
#align multiset.prod_eq_prod_to_enum_finset Multiset.prod_eq_prod_toEnumFinset
#align multiset.sum_eq_sum_to_enum_finset Multiset.sum_eq_sum_toEnumFinset

@[to_additive]
theorem Multiset.prod_toEnumFinset {β : Type*} [CommMonoid β] (m : Multiset α) (f : α → ℕ → β) :
    ∏ x in m.toEnumFinset, f x.1 x.2 = ∏ x : m, f x x.2 := by
  rw [Fintype.prod_equiv m.coeEquiv (fun x ↦ f x x.2) fun x ↦ f x.1.1 x.1.2]
  -- ⊢ ∏ x in toEnumFinset m, f x.fst x.snd = ∏ x : { x // x ∈ toEnumFinset m }, f  …
  · rw [← m.toEnumFinset.prod_coe_sort fun x ↦ f x.1 x.2]
    -- 🎉 no goals
  · intro x
    -- ⊢ f x.fst ↑x.snd = f (↑(↑(coeEquiv m) x)).fst (↑(↑(coeEquiv m) x)).snd
    rfl
    -- 🎉 no goals
#align multiset.prod_to_enum_finset Multiset.prod_toEnumFinset
#align multiset.sum_to_enum_finset Multiset.sum_toEnumFinset
