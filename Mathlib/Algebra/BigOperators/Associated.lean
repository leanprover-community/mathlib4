/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `Algebra.Associated`
and products of multisets, finsets, and finsupps.

-/

assert_not_exists Field

variable {ι M M₀ : Type*}

-- the same local notation used in `Algebra.Associated`
local infixl:50 " ~ᵤ " => Associated

namespace Prime

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod → ∃ a ∈ s, p ∣ a :=
  Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι → M₀} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h

theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι → M₀} :
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
  | insert j s hjs IH =>
    classical
    convert_to (∏ i ∈ insert j s, f i) ~ᵤ (∏ i ∈ insert j s, g i)
    rw [Finset.prod_insert hjs, Finset.prod_insert hjs]
    grind [Associated.mul_mul]

theorem exists_associated_mem_of_dvd_prod [CancelCommMonoidWithZero M₀] {p : M₀} (hp : Prime p)
    {s : Multiset M₀} : (∀ r ∈ s, Prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
  Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_unit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    rcases hp.dvd_or_dvd hps with h | h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

open Submonoid in
/-- Let x, y ∈ M₀. If x * y can be written as a product of units and prime elements, then x can be
written as a product of units and prime elements. -/
theorem divisor_closure_eq_closure [CancelCommMonoidWithZero M₀]
    (x y : M₀) (hxy : x * y ∈ closure { r : M₀ | IsUnit r ∨ Prime r}) :
    x ∈ closure { r : M₀ | IsUnit r ∨ Prime r} := by
  obtain ⟨m, hm, hprod⟩ := exists_multiset_of_mem_closure hxy
  induction m using Multiset.induction generalizing x y with
  | empty =>
    apply subset_closure
    simp only [Set.mem_setOf]
    simp only [Multiset.prod_zero] at hprod
    left; exact isUnit_of_mul_eq_one _ _ hprod.symm
  | cons c s hind =>
    simp only [Multiset.mem_cons, forall_eq_or_imp, Set.mem_setOf] at hm
    simp only [Multiset.prod_cons] at hprod
    simp only [Set.mem_setOf_eq] at hind
    obtain ⟨ha₁ | ha₂, hs⟩ := hm
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y * k) ?_ hs ?_
      · simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
        refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure ?_,
          Multiset.forall_mem_cons.2 ⟨subset_closure ?_, fun t ht => subset_closure (hs t ht)⟩⟩)
        · left; exact isUnit_of_mul_eq_one_right _ _ hk
        · left; exact ha₁
      · rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
        left; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; rw [hc, mul_assoc] at hprod
        refine Submonoid.mul_mem _ (subset_closure ?_)
          (hind _ _ ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
        · right; exact ha₂
        rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
        exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc, mul_comm x _, mul_assoc, mul_comm c _] at hprod
      refine hind x c ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))

theorem Multiset.prod_primes_dvd [CancelCommMonoidWithZero M₀]
    [∀ a : M₀, DecidablePred (Associated a)] {s : Multiset M₀} (n : M₀) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countP (Associated a) ≤ 1) : s.prod ∣ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.prod_zero, one_dvd]
  | cons a s induct =>
    rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    gcongr
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

theorem Finset.prod_primes_dvd [CancelCommMonoidWithZero M₀] [Subsingleton M₀ˣ] {s : Finset M₀}
    (n : M₀) (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : ∏ p ∈ s, p ∣ n := by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

namespace Associates

section CommMonoid

variable [CommMonoid M]

theorem prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.prod :=
  Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

theorem finset_prod_mk {p : Finset ι} {f : ι → M} :
    (∏ i ∈ p, Associates.mk (f i)) = Associates.mk (∏ i ∈ p, f i) := by
  rw [Finset.prod_eq_multiset_prod, ← Function.comp_def, ← Multiset.map_map, prod_mk,
    ← Finset.prod_eq_multiset_prod]

theorem rel_associated_iff_map_eq_map {p q : Multiset M} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]

theorem prod_eq_one_iff {p : Multiset (Associates M)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates M) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])

theorem prod_le_prod {p q : Multiset (Associates M)} (h : p ≤ q) : p.prod ≤ q.prod := by
  haveI := Classical.decEq (Associates M)
  suffices p.prod ≤ (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M₀]

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates M₀)} {p : Associates M₀}
    (hp : Prime p) : p ≤ s.prod → ∃ a ∈ s, p ≤ a :=
  Multiset.induction_on s (fun ⟨_, eq⟩ => (hp.ne_one (mul_eq_one.1 eq.symm).1).elim)
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

theorem prod_ne_zero_of_prime [CancelCommMonoidWithZero M₀] [Nontrivial M₀] (s : Multiset M₀)
    (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.dvd_finset_prod_iff {S : Finset M₀} {p : M} (pp : Prime p) (g : M₀ → M) :
    p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

theorem Prime.not_dvd_finset_prod {S : Finset M₀} {p : M} (pp : Prime p) {g : M₀ → M}
    (hS : ∀ a ∈ S, ¬p ∣ g a) : ¬p ∣ S.prod g := by
  exact mt (Prime.dvd_finset_prod_iff pp _).1 <| not_exists.2 fun a => not_and.2 (hS a)

theorem Prime.dvd_finsuppProd_iff {f : M₀ →₀ M} {g : M₀ → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finset_prod_iff pp _

@[deprecated (since := "2025-04-06")] alias Prime.dvd_finsupp_prod_iff := Prime.dvd_finsuppProd_iff

theorem Prime.not_dvd_finsuppProd {f : M₀ →₀ M} {g : M₀ → M → ℕ} {p : ℕ} (pp : Prime p)
    (hS : ∀ a ∈ f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g :=
  Prime.not_dvd_finset_prod pp hS

@[deprecated (since := "2025-04-06")] alias Prime.not_dvd_finsupp_prod := Prime.not_dvd_finsuppProd

end CommMonoidWithZero
