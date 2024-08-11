/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.BigOperators.Finsupp

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `Algebra.Associated`
and products of multisets, finsets, and finsupps.

-/


variable {α β γ δ : Type*}

/-- Notation for two elements of a monoid are associated, i.e.
if one of them is another one multiplied by a unit on the right.-/
local infixl:50 " ~ᵤ " => Associated

namespace Prime

variable [CommMonoidWithZero α] {p : α}

theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset α} : p ∣ s.prod → ∃ a ∈ s, p ∣ a :=
  Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset β} {f : β → α} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h

theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset β} {f : β → α} :
    p ∣ s.prod f → ∃ i ∈ s, p ∣ f i :=
  hp.exists_mem_multiset_map_dvd

end Prime

theorem Prod.associated_iff {M N : Type*} [Monoid M] [Monoid N] {x z : M × N} :
    x ~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2 :=
  ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

theorem Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι → M)
    (g : ι → M) (h : ∀ i, i ∈ s → (f i) ~ᵤ (g i)) : (∏ i ∈ s, f i) ~ᵤ (∏ i ∈ s, g i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | @insert j s hjs IH =>
    classical
    convert_to (∏ i ∈ insert j s, f i) ~ᵤ (∏ i ∈ insert j s, g i)
    rw [Finset.prod_insert hjs, Finset.prod_insert hjs]
    exact Associated.mul_mul (h j (Finset.mem_insert_self j s))
      (IH (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

theorem exists_associated_mem_of_dvd_prod [CancelCommMonoidWithZero α] {p : α} (hp : Prime p)
    {s : Multiset α} : (∀ r ∈ s, Prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
  Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_unit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    cases' hp.dvd_or_dvd hps with h h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

theorem Multiset.prod_primes_dvd [CancelCommMonoidWithZero α]
    [∀ a : α, DecidablePred (Associated a)] {s : Multiset α} (n : α) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countP (Associated a) ≤ 1) : s.prod ∣ n := by
  induction' s using Multiset.induction_on with a s induct n primes divs generalizing n
  · simp only [Multiset.prod_zero, one_dvd]
  · rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    apply mul_dvd_mul_left a
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
    have a_prime := h a (Multiset.mem_cons_self a s)
    have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
    refine (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => ?_
    have assoc := b_prime.associated_of_dvd a_prime b_div_a
    have := uniq a
    rw [Multiset.countP_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
      Multiset.countP_pos] at this
    exact this ⟨b, b_in_s, assoc.symm⟩

theorem Finset.prod_primes_dvd [CancelCommMonoidWithZero α] [Unique αˣ] {s : Finset α} (n : α)
    (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : (∏ p ∈ s, p) ∣ n := by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

namespace Associates

section CommMonoid

variable [CommMonoid α]

theorem prod_mk {p : Multiset α} : (p.map Associates.mk).prod = Associates.mk p.prod :=
  Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

theorem finset_prod_mk {p : Finset β} {f : β → α} :
    (∏ i ∈ p, Associates.mk (f i)) = Associates.mk (∏ i ∈ p, f i) := by
  -- Porting note: added
  have : (fun i => Associates.mk (f i)) = Associates.mk ∘ f :=
    funext fun x => Function.comp_apply
  rw [Finset.prod_eq_multiset_prod, this, ← Multiset.map_map, prod_mk,
    ← Finset.prod_eq_multiset_prod]

theorem rel_associated_iff_map_eq_map {p q : Multiset α} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]

theorem prod_eq_one_iff {p : Multiset (Associates α)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates α) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp (config := { contextual := true }) [mul_eq_one, or_imp, forall_and])

theorem prod_le_prod {p q : Multiset (Associates α)} (h : p ≤ q) : p.prod ≤ q.prod := by
  haveI := Classical.decEq (Associates α)
  haveI := Classical.decEq α
  suffices p.prod ≤ (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates α)} {p : Associates α}
    (hp : Prime p) : p ≤ s.prod → ∃ a ∈ s, p ≤ a :=
  Multiset.induction_on s (fun ⟨d, Eq⟩ => (hp.ne_one (mul_eq_one.1 Eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

end CancelCommMonoidWithZero

end Associates

namespace Multiset

theorem prod_ne_zero_of_prime [CancelCommMonoidWithZero α] [Nontrivial α] (s : Multiset α)
    (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.dvd_finset_prod_iff {S : Finset α} {p : M} (pp : Prime p) (g : α → M) :
    p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

theorem Prime.not_dvd_finset_prod {S : Finset α} {p : M} (pp : Prime p) {g : α → M}
    (hS : ∀ a ∈ S, ¬p ∣ g a) : ¬p ∣ S.prod g := by
  exact mt (Prime.dvd_finset_prod_iff pp _).1 <| not_exists.2 fun a => not_and.2 (hS a)

theorem Prime.dvd_finsupp_prod_iff {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finset_prod_iff pp _

theorem Prime.not_dvd_finsupp_prod {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p)
    (hS : ∀ a ∈ f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g :=
  Prime.not_dvd_finset_prod pp hS

end CommMonoidWithZero
