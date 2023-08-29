/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.BigOperators.Finsupp

#align_import algebra.big_operators.associated from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `Algebra.Associated`
and products of multisets, finsets, and finsupps.

-/


variable {α β γ δ : Type*}

-- the same local notation used in `Algebra.Associated`
local infixl:50 " ~ᵤ " => Associated

open BigOperators

namespace Prime

variable [CommMonoidWithZero α] {p : α} (hp : Prime p)

theorem exists_mem_multiset_dvd {s : Multiset α} : p ∣ s.prod → ∃ a ∈ s, p ∣ a :=
  Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
                                -- 🎉 no goals
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
#align prime.exists_mem_multiset_dvd Prime.exists_mem_multiset_dvd

theorem exists_mem_multiset_map_dvd {s : Multiset β} {f : β → α} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h
#align prime.exists_mem_multiset_map_dvd Prime.exists_mem_multiset_map_dvd

theorem exists_mem_finset_dvd {s : Finset β} {f : β → α} : p ∣ s.prod f → ∃ i ∈ s, p ∣ f i :=
  hp.exists_mem_multiset_map_dvd
#align prime.exists_mem_finset_dvd Prime.exists_mem_finset_dvd

end Prime

theorem exists_associated_mem_of_dvd_prod [CancelCommMonoidWithZero α] {p : α} (hp : Prime p)
    {s : Multiset α} : (∀ r ∈ s, Prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
  Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_unit]) fun a s ih hs hps => by
                              -- 🎉 no goals
    rw [Multiset.prod_cons] at hps
    -- ⊢ ∃ q, q ∈ a ::ₘ s ∧ p ~ᵤ q
    cases' hp.dvd_or_dvd hps with h h
    -- ⊢ ∃ q, q ∈ a ::ₘ s ∧ p ~ᵤ q
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      -- ⊢ ∃ q, q ∈ a ::ₘ s ∧ p ~ᵤ q
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
      -- 🎉 no goals
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      -- ⊢ ∃ q, q ∈ a ::ₘ s ∧ p ~ᵤ q
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩
      -- 🎉 no goals
#align exists_associated_mem_of_dvd_prod exists_associated_mem_of_dvd_prod

theorem Multiset.prod_primes_dvd [CancelCommMonoidWithZero α]
    [∀ a : α, DecidablePred (Associated a)] {s : Multiset α} (n : α) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countP (Associated a) ≤ 1) : s.prod ∣ n := by
  induction' s using Multiset.induction_on with a s induct n primes divs generalizing n
  -- ⊢ prod 0 ∣ n
  · simp only [Multiset.prod_zero, one_dvd]
    -- 🎉 no goals
  · rw [Multiset.prod_cons]
    -- ⊢ a * prod s ∣ n
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    -- ⊢ a * prod s ∣ a * k
    apply mul_dvd_mul_left a
    -- ⊢ prod s ∣ k
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    · have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
      -- ⊢ b ∣ k
      have a_prime := h a (Multiset.mem_cons_self a s)
      -- ⊢ b ∣ k
      have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
      -- ⊢ b ∣ k
      refine' (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => _
      -- ⊢ False
      have assoc := b_prime.associated_of_dvd a_prime b_div_a
      -- ⊢ False
      have := uniq a
      -- ⊢ False
      rw [Multiset.countP_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
        Multiset.countP_pos] at this
      exact this ⟨b, b_in_s, assoc.symm⟩
      -- 🎉 no goals
#align multiset.prod_primes_dvd Multiset.prod_primes_dvd

theorem Finset.prod_primes_dvd [CancelCommMonoidWithZero α] [Unique αˣ] {s : Finset α} (n : α)
    (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : (∏ p in s, p) ∣ n := by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          -- POrting note: was
          -- `simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter, ←
          --    Multiset.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup]`
          intro a
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter]
          change Multiset.card (Multiset.filter (fun b => a = b) s.val) ≤ 1
          apply le_of_eq_of_le (Multiset.count_eq_card_filter_eq _ _).symm
          apply Multiset.nodup_iff_count_le_one.mp
          exact s.nodup)
#align finset.prod_primes_dvd Finset.prod_primes_dvd

namespace Associates

section CommMonoid

variable [CommMonoid α]

theorem prod_mk {p : Multiset α} : (p.map Associates.mk).prod = Associates.mk p.prod :=
  Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]
                              -- 🎉 no goals
                                                     -- 🎉 no goals
#align associates.prod_mk Associates.prod_mk

theorem finset_prod_mk {p : Finset β} {f : β → α} :
    (∏ i in p, Associates.mk (f i)) = Associates.mk (∏ i in p, f i) := by
  -- Porting note: added
  have : (fun i => Associates.mk (f i)) = Associates.mk ∘ f :=
    funext <| fun x => Function.comp_apply
  rw [Finset.prod_eq_multiset_prod, this, ←Multiset.map_map, prod_mk, ←Finset.prod_eq_multiset_prod]
  -- 🎉 no goals
#align associates.finset_prod_mk Associates.finset_prod_mk

theorem rel_associated_iff_map_eq_map {p q : Multiset α} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  -- ⊢ Multiset.Rel Associated p q ↔ Multiset.Rel (fun a b => Associates.mk a = Ass …
  simp only [mk_eq_mk_iff_associated]
  -- 🎉 no goals
#align associates.rel_associated_iff_map_eq_map Associates.rel_associated_iff_map_eq_map

theorem prod_eq_one_iff {p : Multiset (Associates α)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates α) = 1 :=
  Multiset.induction_on p (by simp)
                              -- 🎉 no goals
    (by simp (config := { contextual := true }) [mul_eq_one_iff, or_imp, forall_and])
        -- 🎉 no goals
#align associates.prod_eq_one_iff Associates.prod_eq_one_iff

theorem prod_le_prod {p q : Multiset (Associates α)} (h : p ≤ q) : p.prod ≤ q.prod := by
  haveI := Classical.decEq (Associates α)
  -- ⊢ Multiset.prod p ≤ Multiset.prod q
  haveI := Classical.decEq α
  -- ⊢ Multiset.prod p ≤ Multiset.prod q
  suffices p.prod ≤ (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  -- ⊢ Multiset.prod p ≤ Multiset.prod (p + (q - p))
  suffices p.prod * 1 ≤ p.prod * (q - p).prod by simpa
  -- ⊢ Multiset.prod p * 1 ≤ Multiset.prod p * Multiset.prod (q - p)
  exact mul_mono (le_refl p.prod) one_le
  -- 🎉 no goals
#align associates.prod_le_prod Associates.prod_le_prod

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates α)} {p : Associates α}
    (hp : Prime p) : p ≤ s.prod → ∃ a ∈ s, p ≤ a :=
  Multiset.induction_on s (fun ⟨d, Eq⟩ => (hp.ne_one (mul_eq_one_iff.1 Eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.prod := by simpa using h
                                -- 🎉 no goals
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
#align associates.exists_mem_multiset_le_of_prime Associates.exists_mem_multiset_le_of_prime

end CancelCommMonoidWithZero

end Associates

namespace Multiset

theorem prod_ne_zero_of_prime [CancelCommMonoidWithZero α] [Nontrivial α] (s : Multiset α)
    (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl
#align multiset.prod_ne_zero_of_prime Multiset.prod_ne_zero_of_prime

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.dvd_finset_prod_iff {S : Finset α} {p : M} (pp : Prime p) (g : α → M) :
    p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩
#align prime.dvd_finset_prod_iff Prime.dvd_finset_prod_iff

theorem Prime.dvd_finsupp_prod_iff {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finset_prod_iff pp _
#align prime.dvd_finsupp_prod_iff Prime.dvd_finsupp_prod_iff

end CommMonoidWithZero
