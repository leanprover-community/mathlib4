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

theorem Prod.associated_iff {M N : Type*} [Monoid M] [Monoid N] {x z : M × N} :
    x ~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2 :=
  ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

theorem Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι → M)
    (g : ι → M) (h : ∀ i, i ∈ s → (f i) ~ᵤ (g i)) : (∏ i in s, f i) ~ᵤ (∏ i in s, g i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | @insert j s hjs IH =>
    classical
    convert_to (∏ i in insert j s, f i) ~ᵤ (∏ i in insert j s, g i)
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
#align exists_associated_mem_of_dvd_prod exists_associated_mem_of_dvd_prod

/-- A submonoid S of a monoid α is said to be divisor-closed if every divisor a ∈ α of some element
b ∈ S lies in S when it is multiplied by a unit. -/
def IsDivisorClosed [Monoid α] (S : Submonoid α) :=
    ∀ b ∈ S, ∀ (a : α) (_ : ∃ k, b = a*k), ∃ z ∈ S, a ~ᵤ z

/-- Let α be a monoid. The divisor_closure of a subset s ⊆ α is defined as the intersection of
all the submonoids which contain s and are divisor-closed. -/
def Submonoid.divisor_closure [Monoid α] (s : Set α) :=
    sInf { S : Submonoid α | s ⊆ S ∧ IsDivisorClosed S }

theorem Submonoid.subset_divisor_closure [Monoid α] {s : Set α} :
    s ⊆ (Submonoid.divisor_closure s) := by
  unfold divisor_closure
  simp only [coe_sInf, Set.mem_setOf_eq, Set.subset_iInter_iff, and_imp]
  exact (fun _ hi _ => hi)

theorem Submonoid.divisor_closure_le [Monoid α] {s : Set α} {S : Submonoid α} :
    s ⊆ S ∧ IsDivisorClosed S → Submonoid.divisor_closure s ≤ S := fun h => sInf_le h

/-- An induction principle for divisor closure membership. If `p` satisfies the four conditions
below, then `p` holds for all elements of the divisor closure of `s`.
First condition: `p` holds for `1`.
Second condition: `p` holds for all elements of `s`.
Third condition: `p` is preserved under multiplication.
Fourth condition: If `p` holds for an element x, then each divisor of x is the product of an element
z for which `p` holds and a unit. -/
theorem Submonoid.divisor_closure_induction [Monoid α] {s : Set α} {p : α → Prop} {x : α}
    (h : x ∈ Submonoid.divisor_closure s) (mem : ∀ x ∈ s, p x) (one : p 1)
    (mul : ∀ x y, p x → p y → p (x*y))
    (div : ∀ x (_ : p x), ∀ y k (_ : x = y*k), ∃ z ∈ {x | p x}, y ~ᵤ z) : p x := by
  have := Submonoid.divisor_closure_le (s := s) (S := ⟨⟨_, fun hx hy => mul _ _ hx hy⟩, one⟩)
  unfold IsDivisorClosed at this
  simp only [coe_set_mk, Subsemigroup.coe_set_mk, and_imp, mem_mk, Subsemigroup.mem_mk,
    forall_exists_index] at this
  exact this mem div h

theorem top_divisor_closed [Monoid α] : IsDivisorClosed (⊤ : Submonoid α) :=
  fun _ _ a _ => ⟨_, Submonoid.mem_top a, Associated.refl a⟩

theorem bot_divisor_closed [CommMonoid α] : IsDivisorClosed (⊥ : Submonoid α) := by
  refine' fun _ hb _ ha => ⟨_, (⊥ : Submonoid α).one_mem, _⟩
  rcases ha with ⟨k, ha⟩
  rw [Submonoid.mem_bot.1 hb] at ha
  exact associated_one_of_mul_eq_one _ ha.symm

open Submonoid in
/-- Let x, y ∈ α. If x * y can be written as a product of prime elements, then x can be written as
a product of a unit and prime elements. -/
theorem divisor_closure_eq_closure [CancelCommMonoidWithZero α] :
    ∀ x y, x * y ∈ closure { r | Prime r } → ∃ z ∈ closure { r : α | Prime r }, x ~ᵤ z := by
  intros a b hab
  obtain ⟨m, hm⟩ := exists_multiset_of_mem_closure hab
  revert a b hm
  refine' m.induction (p := fun m => ∀ a b, a * b ∈ closure {r | Prime r} →
    (∃ (_ : ∀ y ∈ m, Prime y), m.prod = a * b) → ∃ z ∈ closure {r | Prime r}, a ~ᵤ z) _ _
  simp only [Multiset.prod_zero, Multiset.not_mem_zero, Set.mem_setOf_eq, IsEmpty.forall_iff,
    forall_const, exists_const]
  exact (fun _ _ _ hprod => ⟨1, one_mem _, associated_one_of_mul_eq_one _ hprod.symm⟩)
  simp only [Set.mem_setOf_eq, exists_prop, and_imp, Multiset.prod_cons, Multiset.mem_cons,
    forall_eq_or_imp]
  intros a s hind x y _ hprime hprime₂ hprod
  rcases hprime.dvd_mul.1 (Dvd.intro _ hprod) with h₁ | h₂
  · rcases h₁ with ⟨c, h₁⟩
    rw [h₁, mul_assoc] at hprod
    have hprod₂ := mul_left_cancel₀ (hprime.ne_zero) hprod
    obtain ⟨_, hz₁, hz₂⟩ :=
      hind _ _ (mem_closure_of_exists_multiset ⟨_, hprime₂, hprod₂⟩) hprime₂ hprod₂
    rw [h₁]
    exact ⟨_, mul_mem (Set.mem_of_subset_of_mem subset_closure hprime) hz₁, hz₂.mul_left _⟩
  · rcases h₂ with ⟨c, h₂⟩
    rw [h₂, ← mul_assoc, mul_comm _ a, mul_assoc] at hprod
    have hprod₂ := mul_left_cancel₀ (hprime.ne_zero) hprod
    exact (hind _ _ (mem_closure_of_exists_multiset ⟨_, hprime₂, hprod₂⟩) hprime₂ hprod₂)

theorem Submonoid.closure_divisor_closed [CancelCommMonoidWithZero α] :
    IsDivisorClosed (closure { r : α | Prime r }) := by
  intros _ hb _ ha
  rcases ha with ⟨k, ha⟩
  rw [ha] at hb
  exact divisor_closure_eq_closure _ _ hb

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
    · have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
      have a_prime := h a (Multiset.mem_cons_self a s)
      have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
      refine' (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => _
      have assoc := b_prime.associated_of_dvd a_prime b_div_a
      have := uniq a
      rw [Multiset.countP_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
        Multiset.countP_pos] at this
      exact this ⟨b, b_in_s, assoc.symm⟩
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
#align associates.prod_mk Associates.prod_mk

theorem finset_prod_mk {p : Finset β} {f : β → α} :
    (∏ i in p, Associates.mk (f i)) = Associates.mk (∏ i in p, f i) := by
  -- Porting note: added
  have : (fun i => Associates.mk (f i)) = Associates.mk ∘ f :=
    funext fun x => Function.comp_apply
  rw [Finset.prod_eq_multiset_prod, this, ← Multiset.map_map, prod_mk,
    ← Finset.prod_eq_multiset_prod]
#align associates.finset_prod_mk Associates.finset_prod_mk

theorem rel_associated_iff_map_eq_map {p q : Multiset α} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]
#align associates.rel_associated_iff_map_eq_map Associates.rel_associated_iff_map_eq_map

theorem prod_eq_one_iff {p : Multiset (Associates α)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates α) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp (config := { contextual := true }) [mul_eq_one_iff, or_imp, forall_and])
#align associates.prod_eq_one_iff Associates.prod_eq_one_iff

theorem prod_le_prod {p q : Multiset (Associates α)} (h : p ≤ q) : p.prod ≤ q.prod := by
  haveI := Classical.decEq (Associates α)
  haveI := Classical.decEq α
  suffices p.prod ≤ (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le
#align associates.prod_le_prod Associates.prod_le_prod

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates α)} {p : Associates α}
    (hp : Prime p) : p ≤ s.prod → ∃ a ∈ s, p ≤ a :=
  Multiset.induction_on s (fun ⟨d, Eq⟩ => (hp.ne_one (mul_eq_one_iff.1 Eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.prod := by simpa using h
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

theorem Prime.not_dvd_finset_prod {S : Finset α} {p : M} (pp : Prime p) {g : α → M}
    (hS : ∀ a ∈ S, ¬p ∣ g a) : ¬p ∣ S.prod g := by
  exact mt (Prime.dvd_finset_prod_iff pp _).1 <| not_exists.2 fun a => not_and.2 (hS a)

theorem Prime.dvd_finsupp_prod_iff {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finset_prod_iff pp _
#align prime.dvd_finsupp_prod_iff Prime.dvd_finsupp_prod_iff

theorem Prime.not_dvd_finsupp_prod {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p)
    (hS : ∀ a ∈ f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g :=
  Prime.not_dvd_finset_prod pp hS

end CommMonoidWithZero
