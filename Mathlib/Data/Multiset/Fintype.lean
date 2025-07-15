/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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


variable {α β : Type*} [DecidableEq α] [DecidableEq β] {m : Multiset α}

namespace Multiset

/-- Auxiliary definition for the `CoeSort` instance. This prevents the `CoeOut m α`
instance from inadvertently applying to other sigma types. -/
def ToType (m : Multiset α) : Type _ := (x : α) × Fin (m.count x)

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times from different values of `i`. -/
instance : CoeSort (Multiset α) (Type _) := ⟨Multiset.ToType⟩

example : DecidableEq m := inferInstanceAs <| DecidableEq ((x : α) × Fin (m.count x))

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, match_pattern]
def mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m :=
  ⟨x, i⟩

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
instance instCoeSortMultisetType.instCoeOutToType : CoeOut m α :=
  ⟨fun x ↦ x.1⟩

theorem coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl

@[simp] lemma coe_mem {x : m} : ↑x ∈ m := Multiset.count_pos.mp (by have := x.2.2; omega)

@[simp]
protected theorem forall_coe (p : m → Prop) :
    (∀ x : m, p x) ↔ ∀ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall

@[simp]
protected theorem exists_coe (p : m → Prop) :
    (∃ x : m, p x) ↔ ∃ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists

instance : Fintype { p : α × ℕ | p.2 < m.count p.1 } :=
  Fintype.ofFinset
    (m.toFinset.biUnion fun x ↦ (Finset.range (m.count x)).map ⟨_, Prod.mk_right_injective x⟩)
    (by
      rintro ⟨x, i⟩
      simp only [Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Prod.mk_inj, Set.mem_setOf_eq]
      simp only [← and_assoc, exists_eq_right, and_iff_right_iff_imp]
      exact fun h ↦ Multiset.count_pos.mp (by omega))

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `Finset`. -/
def toEnumFinset (m : Multiset α) : Finset (α × ℕ) :=
  { p : α × ℕ | p.2 < m.count p.1 }.toFinset

@[simp]
theorem mem_toEnumFinset (m : Multiset α) (p : α × ℕ) :
    p ∈ m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_toFinset

theorem mem_of_mem_toEnumFinset {p : α × ℕ} (h : p ∈ m.toEnumFinset) : p.1 ∈ m :=
  have := (m.mem_toEnumFinset p).mp h; Multiset.count_pos.mp (by omega)

@[simp] lemma toEnumFinset_filter_eq (m : Multiset α) (a : α) :
    {x ∈ m.toEnumFinset | x.1 = a} = {a} ×ˢ Finset.range (m.count a) := by aesop

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
    replace h : {x ∈ s | x.1 = a} ⊆ {a} ×ˢ .range (card (s.1.filter fun x ↦ a = x.1) - 1) := by
      simpa +contextual [forall_swap (β := _ = a), Finset.subset_iff,
        imp_not_comm, not_le, Nat.lt_sub_iff_add_lt] using h
    have : card (s.1.filter fun x ↦ a = x.1) ≤ card (s.1.filter fun x ↦ a = x.1) - 1 := by
      simpa [Finset.card, eq_comm] using Finset.card_mono h
    omega
  exact Nat.le_of_pred_lt (han.trans_lt <| by simpa using hsm hn)

@[mono]
theorem toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ ≤ m₂) :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset := by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact lt_of_le_of_lt' (Multiset.le_iff_count.mp h p.1)

@[simp]
theorem toEnumFinset_subset_iff {m₁ m₂ : Multiset α} :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset ↔ m₁ ≤ m₂ :=
  ⟨fun h ↦ by simpa using map_fst_le_of_subset_toEnumFinset h, Multiset.toEnumFinset_mono⟩

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.
If you are looking for the function `m → α`, that would be plain `(↑)`. -/
@[simps]
def coeEmbedding (m : Multiset α) : m ↪ α × ℕ where
  toFun x := (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    rintro ⟨⟩
    rfl

/-- Another way to coerce a `Multiset` to a type is to go through `m.toEnumFinset` and coerce
that `Finset` to a type. -/
@[simps]
def coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset where
  toFun x :=
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩

@[simp]
theorem toEmbedding_coeEquiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by ext <;> rfl

@[irreducible]
instance fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

theorem map_univ_coeEmbedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset := by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk_inj, Multiset.exists_coe, Multiset.coe_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, true_and]

@[simp]
theorem map_univ_coe (m : Multiset α) :
    (Finset.univ : Finset m).val.map (fun x : m ↦ (x : α)) = m := by
  have := m.map_toEnumFinset_fst
  rw [← m.map_univ_coeEmbedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this

theorem map_univ_comp_coe {β : Type*} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map (f ∘ (fun x : m ↦ (x : α)))) = m.map f := by
  rw [← Multiset.map_map, Multiset.map_univ_coe]

@[simp]
theorem map_univ {β : Type*} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map fun (x : m) ↦ f (x : α)) = m.map f := by
  simp_rw [← Function.comp_apply (f := f)]
  exact map_univ_comp_coe m f

@[simp]
theorem card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = Multiset.card m := by
  rw [Finset.card, ← Multiset.card_map Prod.fst m.toEnumFinset.val]
  congr
  exact m.map_toEnumFinset_fst

@[simp]
theorem card_coe (m : Multiset α) : Fintype.card m = Multiset.card m := by
  rw [Fintype.card_congr m.coeEquiv]
  simp only [Fintype.card_coe, card_toEnumFinset]

@[to_additive]
theorem prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.prod = ∏ x : m, (x : α) := by
  congr
  simp

@[to_additive]
theorem prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) :
    m.prod = ∏ x ∈ m.toEnumFinset, x.1 := by
  congr
  simp

@[to_additive]
theorem prod_toEnumFinset {β : Type*} [CommMonoid β] (m : Multiset α) (f : α → ℕ → β) :
    ∏ x ∈ m.toEnumFinset, f x.1 x.2 = ∏ x : m, f x x.2 := by
  rw [Fintype.prod_equiv m.coeEquiv (fun x ↦ f x x.2) fun x ↦ f x.1.1 x.1.2]
  · rw [← m.toEnumFinset.prod_coe_sort fun x ↦ f x.1 x.2]
  · intro x
    rfl

/--
If `s = t` then there's an equivalence between the appropriate types.
-/
@[simps]
def cast {s t : Multiset α} (h : s = t) : s ≃ t where
  toFun x := ⟨x.1, x.2.cast (by simp [h])⟩
  invFun x := ⟨x.1, x.2.cast (by simp [h])⟩

instance : IsEmpty (0 : Multiset α) := Fintype.card_eq_zero_iff.mp (by simp)

instance : IsEmpty (∅ : Multiset α) := Fintype.card_eq_zero_iff.mp (by simp)

/--
`v ::ₘ m` is equivalent to `Option m` by mapping one `v` to `none` and everything else to `m`.
-/
def consEquiv {v : α} : v ::ₘ m ≃ Option m where
  toFun x := if h : x.1 = v ∧ x.2.val = m.count v then none else some ⟨x.1, ⟨x.2, by
    by_cases hv : x.1 = v
    · simp only [hv, true_and] at h ⊢
      apply lt_of_le_of_ne (Nat.le_of_lt_add_one _) h
      convert x.2.2 using 1
      simp [hv]
    · convert x.2.2 using 1
      exact (count_cons_of_ne hv _).symm
    ⟩⟩
  invFun x := x.elim ⟨v, ⟨m.count v, by simp⟩⟩ (fun x ↦ ⟨x.1, x.2.castLE (count_le_count_cons ..)⟩)
  left_inv := by
    rintro ⟨x, hx⟩
    dsimp only
    split
    · rename_i h
      obtain ⟨rfl, h2⟩ := h
      simp [← h2]
    · simp
  right_inv := by
    rintro (_ | x)
    · simp
    · simp only [Option.elim_some, Fin.coe_castLE, Fin.eta, Sigma.eta, dite_eq_ite,
        ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
      rintro rfl
      exact x.2.2.ne

@[simp]
lemma consEquiv_symm_none {v : α} :
    (consEquiv (m := m) (v := v)).symm none =
      ⟨v, ⟨m.count v, (count_cons_self v m) ▸ (Nat.lt_add_one _)⟩⟩ :=
  rfl

@[simp]
lemma consEquiv_symm_some {v : α} {x : m} :
    (consEquiv (v := v)).symm (some x) =
      ⟨x, x.2.castLE (count_le_count_cons ..)⟩ :=
  rfl

lemma coe_consEquiv_of_ne {v : α} (x : v ::ₘ m) (hx : ↑x ≠ v) :
    consEquiv x = some ⟨x.1, x.2.cast (by simp [hx])⟩ := by
  simp [consEquiv, hx]
  rfl

lemma coe_consEquiv_of_eq_of_eq {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 = m.count v) :
    consEquiv x = none := by simp [consEquiv, hx, hx2]

lemma coe_consEquiv_of_eq_of_lt {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 < m.count v) :
    consEquiv x = some ⟨x.1, ⟨x.2, by simpa [hx]⟩⟩ := by simp [consEquiv, hx, hx2.ne]

/--
There is some equivalence between `m` and `m.map f` which respects `f`.
-/
def mapEquiv_aux (m : Multiset α) (f : α → β) :
    Squash { v : m ≃ m.map f // ∀ a : m, v a = f a} :=
  Quotient.recOnSubsingleton m fun l ↦ .mk <|
    List.recOn l
      ⟨@Equiv.equivOfIsEmpty _ _ (by dsimp; infer_instance) (by dsimp; infer_instance), by simp⟩
      fun a s ⟨v, hv⟩ ↦ ⟨Multiset.consEquiv.trans v.optionCongr |>.trans
        Multiset.consEquiv.symm |>.trans (Multiset.cast (map_cons f a s)).symm, fun x ↦ by
        simp only [consEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
            Equiv.coe_fn_symm_mk]
        split <;> simp_all⟩

/--
One of the possible equivalences from `Multiset.mapEquiv_aux`, selected using choice.
-/
noncomputable def mapEquiv (s : Multiset α) (f : α → β) : s ≃ s.map f :=
  (Multiset.mapEquiv_aux s f).out.1

@[simp]
theorem mapEquiv_apply (s : Multiset α) (f : α → β) (v : s) : s.mapEquiv f v = f v :=
  (Multiset.mapEquiv_aux s f).out.2 v

end Multiset
