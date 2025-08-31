/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Piecewise

/-!
# Interaction of big operators with piecewise functions

This file proves lemmas on the sum and product of piecewise functions, including `ite` and `dite`.
-/

variable {ι κ α β γ : Type*} {s : Finset α}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[to_additive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p}
    [DecidablePred fun x => ¬p x] (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
  calc
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x ∈ s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x ∈ s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x ∈ s | p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x : {x ∈ s | ¬p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ (prod_attach _ _).symm (prod_attach _ _).symm
    _ = (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
          ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x _hx ↦
        congr_arg h (dif_pos <| by simpa using (mem_filter.mp x.2).2))
        (prod_congr rfl fun x _hx => congr_arg h (dif_neg <| by simpa using (mem_filter.mp x.2).2))

@[to_additive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {_hp : DecidablePred p} (f g : α → γ)
    (h : γ → β) :
    (∏ x ∈ s, h (if p x then f x else g x)) =
      (∏ x ∈ s with p x, h (f x)) * ∏ x ∈ s with ¬p x, h (g x) :=
  (prod_apply_dite _ _ _).trans <| congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

@[to_additive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) :
    ∏ x ∈ s, (if hx : p x then f x hx else g x hx) =
      (∏ x : {x ∈ s | p x}, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
lemma prod_dite_of_false {p : α → Prop} {_ : DecidablePred p} (h : ∀ i ∈ s, ¬ p i)
    (f : ∀ i, p i → β) (g : ∀ i, ¬ p i → β) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, g i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]
lemma prod_ite_of_false {p : α → Prop} {_ : DecidablePred p} (h : ∀ x ∈ s, ¬p x) (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, g x :=
  (prod_dite_of_false h _ _).trans (prod_attach _ _)

@[to_additive]
lemma prod_dite_of_true {p : α → Prop} {_ : DecidablePred p} (h : ∀ i ∈ s, p i) (f : ∀ i, p i → β)
    (g : ∀ i, ¬ p i → β) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]
lemma prod_ite_of_true {p : α → Prop} {_ : DecidablePred p} (h : ∀ x ∈ s, p x) (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, f x :=
  (prod_dite_of_true h _ _).trans (prod_attach _ _)

@[to_additive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_false h _ _

@[to_additive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (f x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_true h _ _

@[to_additive (attr := simp)]
theorem prod_ite_mem [DecidableEq α] (s t : Finset α) (f : α → β) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]

@[to_additive]
lemma prod_attach_eq_prod_dite [Fintype α] (s : Finset α) (f : s → β) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite, Finset.univ_eq_attach, Finset.prod_const_one, mul_one]
  congr
  · ext; simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

@[to_additive (attr := simp)]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
    ∏ x ∈ s, (if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[to_additive (attr := simp)]
theorem prod_dite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, x = a → β) :
    ∏ x ∈ s, (if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `Finset.prod_ite_eq` is that the arguments to `Eq` are swapped. -/
@[to_additive (attr := simp) "A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped."]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
theorem prod_ite_eq_of_mem [DecidableEq α] (s : Finset α) (a : α) (b : α → β) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  simp only [prod_ite_eq, if_pos h]

/-- The difference with `Finset.prod_ite_eq_of_mem` is that the arguments to `Eq` are swapped. -/
@[to_additive]
theorem prod_ite_eq_of_mem' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) (h : a ∈ s) :
    (∏ x ∈ s, if x = a then b x else 1) = b a := by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle' [DecidableEq α] (a : α) (x : β) (s : Finset α) :
    ∏ a' ∈ s, Pi.mulSingle a x a' = if a ∈ s then x else 1 :=
  prod_dite_eq' _ _ _

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle {β : α → Type*} [DecidableEq α] [∀ a, CommMonoid (β a)] (a : α)
    (f : ∀ a, β a) (s : Finset α) :
    (∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1 :=
  prod_dite_eq _ _ _

@[to_additive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
    (∏ x ∈ s, (t.piecewise f g) x) = (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, g x := by
  simp only [piecewise]
  rw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

@[to_additive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by
  convert (s.prod_piecewise t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

@[to_additive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  convert (s.prod_inter_mul_prod_diff {i} f).symm
  simp [h]

@[to_additive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_diff_singleton h, mul_comm]

@[to_additive]
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = f a * ∏ i ∈ {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[to_additive]
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = (∏ i ∈ {a}ᶜ, f i) * f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f

theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton ha]
    exact dvd_mul_right _ _

@[to_additive]
theorem prod_update_of_notMem [DecidableEq α] {s : Finset α} {i : α} (h : i ∉ s) (f : α → β)
    (b : β) : ∏ x ∈ s, Function.update f i b x = ∏ x ∈ s, f x := by
  apply prod_congr rfl
  intros j hj
  have : j ≠ i := by
    rintro rfl
    exact h hj
  simp [this]

@[deprecated (since := "2025-05-23")] alias sum_update_of_not_mem := sum_update_of_notMem

@[to_additive existing, deprecated (since := "2025-05-23")]
alias prod_update_of_not_mem := prod_update_of_notMem

@[to_additive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
    ∏ x ∈ s, Function.update f i b x = b * ∏ x ∈ s \ singleton i, f x := by
  rw [update_eq_piecewise, prod_piecewise]
  simp [h]

/-- See also `Finset.prod_ite_zero`. -/
@[to_additive "See also `Finset.sum_boole`."]
theorem prod_ite_one (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : β) :
    ∏ i ∈ s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hpi]
    exact fun j hj hji ↦ if_neg fun hpj ↦ hji <| h _ hj _ hi hpj hpi
  · push_neg at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive sum_boole_nsmul]
theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∏ x ∈ s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp

end CommMonoid

lemma card_filter (p) [DecidablePred p] (s : Finset ι) :
    #{i ∈ s | p i} = ∑ i ∈ s, ite (p i) 1 0 := by simp [sum_ite]

end Finset

namespace Fintype

open Finset

variable [CommMonoid α] [Fintype ι]

@[to_additive]
lemma prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : α) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [prod_ite_one univ p (by simpa using h)]

variable [DecidableEq ι]

@[to_additive]
lemma prod_ite_mem (s : Finset ι) (f : ι → α) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  simp

/-- See also `Finset.prod_dite_eq`. -/
@[to_additive "See also `Finset.sum_dite_eq`."] lemma prod_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_dite_eq'`. -/
@[to_additive "See also `Finset.sum_dite_eq'`."] lemma prod_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    ∏ j, (if h : j = i then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq`. -/
@[to_additive "See also `Finset.sum_ite_eq`."]
lemma prod_ite_eq (i : ι) (f : ι → α) : ∏ j, (if i = j then f j else 1) = f i := by
  rw [Finset.prod_ite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq'`. -/
@[to_additive "See also `Finset.sum_ite_eq'`."]
lemma prod_ite_eq' (i : ι) (f : ι → α) : ∏ j, (if j = i then f j else 1) = f i := by
  rw [Finset.prod_ite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_pi_mulSingle`. -/
@[to_additive "See also `Finset.sum_pi_single`."]
lemma prod_pi_mulSingle {α : ι → Type*} [∀ i, CommMonoid (α i)] (i : ι) (f : ∀ i, α i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := prod_dite_eq _ _

/-- See also `Finset.prod_pi_mulSingle'`. -/
@[to_additive "See also `Finset.sum_pi_single'`."]
lemma prod_pi_mulSingle' (i : ι) (a : α) : ∏ j, Pi.mulSingle i a j = a := prod_dite_eq' _ _

end Fintype
