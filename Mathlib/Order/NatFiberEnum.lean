/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Nelson
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite

/-!
# Enumeration by parameter value

Here we prove that, if `r` is a function from an infinite type `α` to `ℕ` such that
every fiber of `r` is finite, then there is an enumeration `e : ℕ ≃ α` of `α` that
respects the function `r`, in the sense that `i ≤ j` implies `r (e i) ≤ r (e j)`.
This is proved by first producing an explicit equivalence `e : ℕ ≃ Sigma n` for `n : ℕ → ℕ`
that is monotone with respect to `Sigma.fst` (which is done in `Nat.exists_enum_fin_sigma`),
and then putting  `α` in bijection with such a sigma-type to prove the general result.
-/

open BigOperators

section enumeration

/-- For a sequence `n : ℕ → ℕ` that is not eventually zero, the type `Sigma n` has an equivalence
  to `ℕ` that sorts by the value of the first co-ordinate. -/
theorem Nat.exists_enum_fin_sigma (n : ℕ → ℕ) (hn : ∀ i, ∃ j, i ≤ j ∧ 0 < n j) :
    ∃ e : ℕ ≃ (Sigma (fun i ↦ Fin (n i))), Monotone (fun i ↦ (e i).1) := by
  set f : (Sigma (fun i ↦ Fin (n i))) → ℕ := fun a ↦ (∑ i in Finset.range a.1, n i) + a.2 with hf
  have h1 : ∀ {a a'}, f a ≤ f a' → a.1 ≤ a'.1 := by
    rintro ⟨a,⟨x,hx⟩⟩ ⟨a',⟨x',hx'⟩⟩ h
    simp_rw [hf] at h
    replace h := (Nat.le_add_right _ _).trans_lt <|
      h.trans_lt (add_lt_add_left hx' (∑ i in Finset.range a', n i))
    rw [add_comm, ← Finset.sum_insert (by simp), ← Finset.range_succ, Nat.succ_eq_add_one] at h
    rw [← not_lt, Nat.lt_iff_add_one_le]
    exact fun hle ↦ (Finset.sum_le_sum_of_subset (Finset.range_mono hle)).not_lt h

  have h_inj : f.Injective := by
    rintro ⟨a,⟨x,hx⟩⟩ ⟨a',⟨x',hx'⟩⟩ h_eq
    obtain rfl := (h1 h_eq.le).antisymm (h1 h_eq.symm.le)
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Fin.mk.injEq, true_and]
    simpa [hf] using h_eq

  have h_surj : f.Surjective := by
    intro i
    induction' i with i hi
    · refine ⟨⟨Nat.find (hn 0), ⟨0,(Nat.find_spec (hn 0)).2⟩⟩, ?_⟩
      simp only [hf, zero_le, true_and, add_zero, Nat.zero_eq, Finset.sum_eq_zero_iff,
        Finset.mem_range, Nat.lt_find_iff, not_lt, nonpos_iff_eq_zero]
      exact fun x h ↦ h x rfl.le
    obtain ⟨⟨a₀, ⟨x, hx⟩⟩, rfl⟩ := hi
    obtain (heq | hlt) := (Nat.lt_iff_add_one_le.1 hx).eq_or_lt
    · refine ⟨⟨Nat.find (hn (a₀+1)), ⟨0, (Nat.find_spec (hn (a₀+1))).2⟩⟩, ?_⟩
      simp only [hf, add_zero, Nat.succ_eq_add_one, add_assoc, heq]
      rw [eq_comm, add_comm, ← Finset.sum_insert (by simp)]
      refine Finset.sum_subset ?_ ?_
      · simp only [Finset.insert_subset_iff, Finset.mem_range, Nat.lt_find_iff, not_and, not_lt,
          nonpos_iff_eq_zero, Finset.range_subset, Nat.le_find_iff, Nat.add_one_le_iff]
        exact ⟨fun _ h h' ↦ (h.not_lt h').elim, fun _ h h' ↦ (h.not_lt h').elim ⟩
      simp only [Finset.mem_range, Nat.lt_find_iff, not_and, not_lt, nonpos_iff_eq_zero,
        Finset.mem_insert, not_or, and_imp]
      exact fun y hy hne hle ↦ hy _ rfl.le (Nat.add_one_le_iff.2 <| hle.lt_of_ne (Ne.symm hne))
    refine ⟨⟨a₀, ⟨_, hlt⟩⟩, by simp [hf, Nat.succ_eq_add_one, add_assoc]⟩

  set e := (Equiv.ofBijective f ⟨h_inj, h_surj⟩).symm
  refine ⟨e, fun i j hij ↦ h1 ?_ ⟩
  rwa [Equiv.ofBijective_apply_symm_apply (f := f), Equiv.ofBijective_apply_symm_apply (f := f)]

/-- Given a function `r` from an infinite type `α` to `ℕ` whose fibers are finite,
  we can sort `α` according to the value of `r`. -/
theorem exists_enum_by_fiber {α : Type*} [Infinite α] (r : α → ℕ) (hr : ∀ i, (r ⁻¹' {i}).Finite) :
    ∃ (e : ℕ ≃ α), Monotone (r ∘ e) := by
  have _ := fun i ↦ (hr i).fintype
  have hcard : ∀ i, Fintype.card (r ⁻¹' {i}) = (hr i).toFinset.card := by simp
  set e0s := fun (i : ℕ) ↦ (Fintype.equivFinOfCardEq <| hcard i ).symm
  set e1 := Equiv.sigmaFiberEquiv r
  set e2 := Equiv.sigmaCongr (Equiv.refl ℕ) (β₂ := fun i ↦ r ⁻¹' {i}) e0s
  have he1 : ∀ a, a.1 = r (e1 a) := by rintro ⟨a, ⟨b, rfl⟩⟩; rfl
  have h_enum := Nat.exists_enum_fin_sigma (fun i ↦ (hr i).toFinset.card) (fun n ↦ ?_)
  · obtain ⟨e4, he4⟩ := h_enum
    refine ⟨e4.trans (e2.trans e1) , fun i j hij ↦ ?_⟩
    convert he4 hij
    <;> exact (he1 _).symm
  by_contra! h
  have hfin : ∀ a, r a < n := fun a ↦ lt_of_not_le fun hle ↦ by simpa using h _ hle

  set r' : α → Fin n := fun a ↦ ⟨r a, hfin _⟩ with hr'
  obtain ⟨⟨y,hyn⟩, hy⟩ := Finite.exists_infinite_fiber r'
  simp_rw [Set.infinite_coe_iff, hr'] at hy
  exact (hr y).not_infinite (by convert hy; ext; simp)

end enumeration
