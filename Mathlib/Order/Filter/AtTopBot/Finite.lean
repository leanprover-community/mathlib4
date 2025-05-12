/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Finiteness and `Filter.atTop` and `Filter.atBot` filters

This file contains results on `Filter.atTop` and `Filter.atBot` that depend on
the finiteness theory developed in Mathlib.
-/

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

theorem eventually_forall_ge_atTop [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atTop, ∀ y, x ≤ y → p y) ↔ ∀ᶠ x in atTop, p x := by
  refine ⟨fun h ↦ h.mono fun x hx ↦ hx x le_rfl, fun h ↦ ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x ↦ Ici x.1) (fun _ ↦ Subset.rfl) fun x hx y hy ↦ ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz ↦ le_trans (hx ⟨z, hz⟩) hy

theorem eventually_forall_le_atBot [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atBot, ∀ y, y ≤ x → p y) ↔ ∀ᶠ x in atBot, p x :=
  eventually_forall_ge_atTop (α := αᵒᵈ)

theorem Tendsto.eventually_forall_ge_atTop [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atTop) (h_evtl : ∀ᶠ x in atTop, p x) :
    ∀ᶠ x in l, ∀ y, f x ≤ y → p y := by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

theorem Tendsto.eventually_forall_le_atBot [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atBot) (h_evtl : ∀ᶠ x in atBot, p x) :
    ∀ᶠ x in l, ∀ y, y ≤ f x → p y := by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

/-!
### Sequences
-/

/-- If `u` is a sequence which is unbounded above,
then after any point, it reaches a value strictly greater than all previous values.
-/
theorem high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β} (hu : Tendsto u atTop atTop) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u k < u n := by
  intro N
  obtain ⟨k : ℕ, - : k ≤ N, hku : ∀ l ≤ N, u l ≤ u k⟩ : ∃ k ≤ N, ∀ l ≤ N, u l ≤ u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : ∃ n ≥ N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : ℕ, hnN : n ≥ N, hnk : u k < u n, hn_min : ∀ m, m < n → N ≤ m → u m ≤ u k⟩ :
      ∃ n ≥ N, u k < u n ∧ ∀ m, m < n → N ≤ m → u m ≤ u k := by
    rcases Nat.findX ex with ⟨n, ⟨hnN, hnk⟩, hn_min⟩
    push_neg at hn_min
    exact ⟨n, hnN, hnk, hn_min⟩
  use n, hnN
  rintro (l : ℕ) (hl : l < n)
  have hlk : u l ≤ u k := by
    rcases (le_total l N : l ≤ N ∨ N ≤ l) with H | H
    · exact hku l H
    · exact hn_min l hl H
  calc
    u l ≤ u k := hlk
    _ < u n := hnk

-- see Note [nolint_ge]
/-- If `u` is a sequence which is unbounded below,
then after any point, it reaches a value strictly smaller than all previous values.
-/
theorem low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β} (hu : Tendsto u atTop atBot) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u n < u k :=
  @high_scores βᵒᵈ _ _ _ hu

/-- If `u` is a sequence which is unbounded above,
then it `Frequently` reaches a value strictly greater than all previous values.
-/
theorem frequently_high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ᶠ n in atTop, ∀ k < n, u k < u n := by
  simpa [frequently_atTop] using high_scores hu

/-- If `u` is a sequence which is unbounded below,
then it `Frequently` reaches a value strictly smaller than all previous values.
-/
theorem frequently_low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atBot) : ∃ᶠ n in atTop, ∀ k < n, u n < u k :=
  @frequently_high_scores βᵒᵈ _ _ _ hu

theorem strictMono_subseq_of_tendsto_atTop [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩

theorem strictMono_subseq_of_id_le {u : ℕ → ℕ} (hu : ∀ n, n ≤ u n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)

theorem Eventually.atTop_of_arithmetic {p : ℕ → Prop} {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ k < n, ∀ᶠ a in atTop, p (n * a + k)) : ∀ᶠ a in atTop, p a := by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [ge_iff_le, Nat.le_div_iff_mul_le hn.bot_lt, mul_comm]
  exact (Finset.le_sup (f := (n * N ·)) (Finset.mem_range.2 hlt)).trans hb

/-- Given an antitone basis `s : ℕ → Set α` of a filter, extract an antitone subbasis `s ∘ φ`,
`φ : ℕ → ℕ`, such that `m < n` implies `r (φ m) (φ n)`. This lemma can be used to extract an
antitone basis with basis sets decreasing "sufficiently fast". -/
theorem HasAntitoneBasis.subbasis_with_rel {f : Filter α} {s : ℕ → Set α}
    (hs : f.HasAntitoneBasis s) {r : ℕ → ℕ → Prop} (hr : ∀ m, ∀ᶠ n in atTop, r m n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ ⦃m n⦄, m < n → r (φ m) (φ n)) ∧ f.HasAntitoneBasis (s ∘ φ) := by
  rsuffices ⟨φ, hφ, hrφ⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m n, m < n → r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : ∀ t : Set ℕ, t.Finite → ∀ᶠ n in atTop, ∀ m ∈ t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (eventually_gt_atTop m).and (hr _)
  rcases seq_of_forall_finite_exists fun t ht => (this t ht).exists with ⟨φ, hφ⟩
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_swap.2 hφ.1, forall_swap.2 hφ.2⟩

end Filter

open Filter Finset

namespace Nat

theorem eventually_pow_lt_factorial_sub (c d : ℕ) : ∀ᶠ n in atTop, c ^ n < (n - d)! := by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d') c0)).trans_lt ?_
  convert_to (c ^ 2) ^ (c ^ 2 + d' + d + 1) < (c ^ 2 + (c ^ 2 + d' + d + 1) + 1)!
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega
  · congr 1
    omega
  refine (lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial).trans_le <|
    (factorial_le (Nat.le_succ _))
  rw [← one_mul (_ ^ _ : ℕ)]
  apply Nat.mul_lt_mul_of_le_of_lt
  · exact Nat.one_le_of_lt (Nat.factorial_pos _)
  · exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  · exact (Nat.factorial_pos _)

theorem eventually_mul_pow_lt_factorial_sub (a c d : ℕ) :
    ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn

end Nat
