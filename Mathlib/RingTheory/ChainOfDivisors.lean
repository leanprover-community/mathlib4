/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Order.Atoms
import Mathlib.Order.Hom.Bounded
/-!

# Chains of divisors

The results in this file show that in the monoid `Associates M` of a `UniqueFactorizationMonoid`
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, meaning that we can find a strictly increasing bijection between `Fin (n + 1)`
and the set of factors of `a`.

## Main results
- `DivisorChain.exists_chain_of_prime_pow` : existence of a chain for prime powers.
- `DivisorChain.is_prime_pow_of_has_chain` : elements that have a chain are prime powers.
- `multiplicity_prime_eq_multiplicity_image_by_factor_orderIso` : if there is a
  monotone bijection `d` between the set of factors of `a : Associates M` and the set of factors of
  `b : Associates N` then for any prime `p ∣ a`, `multiplicity p a = multiplicity (d p) b`.
- `multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalizedFactors` : if there is a bijection
  between the set of factors of `a : M` and `b : N` then for any prime `p ∣ a`,
  `multiplicity p a = multiplicity (d p) b`


## TODO
- Create a structure for chains of divisors.
- Simplify proof of `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors` using
  `mem_normalizedFactors_factor_order_iso_of_mem_normalizedFactors` or vice versa.

-/

assert_not_exists Field

variable {M : Type*} [CancelCommMonoidWithZero M]

theorem Associates.isAtom_iff {p : Associates M} (h₁ : p ≠ 0) : IsAtom p ↔ Irreducible p :=
  ⟨fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one] using hp.1, fun a b h =>
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.isUnit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            apply isUnit_of_associated_mul (show Associated (p * b) p by conv_rhs => rw [h]) h₁)⟩,
    fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one, Associates.bot_eq_one] using hp.1,
      fun b ⟨⟨a, hab⟩, hb⟩ =>
      (hp.isUnit_or_isUnit hab).casesOn
        (fun hb => show b = ⊥ by rwa [Associates.isUnit_iff_eq_one, ← Associates.bot_eq_one] at hb)
        fun ha =>
        absurd
          (show p ∣ b from
            ⟨(ha.unit⁻¹ : Units _), by rw [hab, mul_assoc, IsUnit.mul_val_inv ha, mul_one]⟩)
          hb⟩⟩

open UniqueFactorizationMonoid Irreducible Associates

namespace DivisorChain

theorem exists_chain_of_prime_pow {p : Associates M} {n : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    ∃ c : Fin (n + 1) → Associates M,
      c 1 = p ∧ StrictMono c ∧ ∀ {r : Associates M}, r ≤ p ^ n ↔ ∃ i, r = c i := by
  refine ⟨fun i => p ^ (i : ℕ), ?_, fun n m h => ?_, @fun y => ⟨fun h => ?_, ?_⟩⟩
  · dsimp only
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt, pow_one]
    exact Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn)
  · exact Associates.dvdNotUnit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_zero, p ^ (m - n : ℕ),
          not_isUnit_of_not_isUnit_dvd hp.not_unit (dvd_pow dvd_rfl (Nat.sub_pos_of_lt h).ne'),
          (pow_mul_pow_sub p h.le).symm⟩
  · obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h
    rw [associated_iff_eq] at hi
    exact ⟨⟨i, Nat.lt_succ_of_le i_le⟩, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ (n - i : ℕ), (pow_mul_pow_sub p (Nat.succ_le_succ_iff.mp i.2)).symm⟩

theorem element_of_chain_not_isUnit_of_index_ne_zero {n : ℕ} {i : Fin (n + 1)} (i_pos : i ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) : ¬IsUnit (c i) :=
  DvdNotUnit.not_unit
    (Associates.dvdNotUnit_iff_lt.2
      (h₁ <| show (0 : Fin (n + 1)) < i from Fin.pos_iff_ne_zero.mpr i_pos))

theorem first_of_chain_isUnit {q : Associates M} {n : ℕ} {c : Fin (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp Associates.one_le
  rw [Associates.isUnit_iff_eq_one, ← Associates.le_one_iff, hr]
  exact h₁.monotone (Fin.zero_le i)

/-- The second element of a chain is irreducible. -/
theorem second_of_chain_is_irreducible {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
    (hq : q ≠ 0) : Irreducible (c 1) := by
  rcases n with - | n; · contradiction
  refine (Associates.isAtom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨?_, fun b hb => ?_⟩
  · exact ne_bot_of_gt (h₁ (show (0 : Fin (n + 2)) < 1 from Fin.one_pos))
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.isUnit_iff_eq_one _).mp (first_of_chain_isUnit h₁ @h₂)
  · simpa [Fin.lt_iff_val_lt_val] using h₁.lt_iff_lt.mp hb

theorem eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r) :
    p = c 1 := by
  rcases n with - | n
  · contradiction
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine congr_arg c (eq_of_le_of_not_lt' ?_ fun hi => ?_)
  · rw [Fin.le_iff_val_le_val, Fin.val_one, Nat.succ_le_iff, ← Fin.val_zero (n.succ + 1), ←
      Fin.lt_iff_val_lt_val, Fin.pos_iff_ne_zero]
    rintro rfl
    exact hp.not_unit (first_of_chain_isUnit h₁ @h₂)
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · cases hi
  refine
    not_irreducible_of_not_unit_dvdNotUnit
      (DvdNotUnit.not_unit
        (Associates.dvdNotUnit_iff_lt.2 (h₁ (show (0 : Fin (n + 2)) < j.castSucc from ?_))))
      ?_ hp.irreducible
  · simpa using Fin.lt_def.mp hi
  · refine Associates.dvdNotUnit_iff_lt.2 (h₁ ?_)
    simpa only [Fin.coe_eq_castSucc] using Fin.lt_succ

theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : ℕ}
    {c : Fin (n + 1) → Associates M} (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) {m : Finset (Associates M)}
    (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 := by
  classical
    have mem_image : ∀ r : Associates M, r ≤ q → r ∈ Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_card fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le

variable [UniqueFactorizationMonoid M]

theorem element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
    (hr : r ∣ q) (hq : q ≠ 0) : ∃ i : Fin (n + 1), r = c 1 ^ (i : ℕ) := by
  classical
    let i := Multiset.card (normalizedFactors r)
    have hi : normalizedFactors r = Multiset.replicate i (c 1) := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      refine
        eq_second_of_chain_of_prime_dvd hn h₁ (@fun r' => h₂) (prime_of_normalized_factor b hb) hr
          (dvd_of_mem_normalizedFactors hb)
    have H : r = c 1 ^ i := by
      have := UniqueFactorizationMonoid.prod_normalizedFactors (ne_zero_of_dvd_ne_zero hq hr)
      rw [associated_iff_eq, hi, Multiset.prod_replicate] at this
      rw [this]
    refine ⟨⟨i, ?_⟩, H⟩
    have : (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ)).card = i + 1 := by
      conv_rhs => rw [← Finset.card_fin (i + 1)]
      cases n
      · contradiction
      rw [Finset.card_image_iff]
      refine Set.injOn_of_injective (fun m m' h => Fin.ext ?_)
      refine
        pow_injective_of_not_isUnit (element_of_chain_not_isUnit_of_index_ne_zero (by simp) h₁) ?_ h
      exact Irreducible.ne_zero (second_of_chain_is_irreducible hn h₁ (@h₂) hq)
    suffices H' : ∀ r ∈ Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ), r ≤ q by
      simp only [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← this]
      apply card_subset_divisors_le_length_of_chain (@h₂) H'
    simp only [Finset.mem_image]
    rintro r ⟨a, _, rfl⟩
    refine dvd_trans ?_ hr
    use c 1 ^ (i - (a : ℕ))
    rw [pow_mul_pow_sub (c 1)]
    · exact H
    · exact Nat.succ_le_succ_iff.mp a.2

theorem eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : q = c 1 ^ n := by
  classical
    obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (@fun r => h₂) (dvd_refl q) hq
    convert hi'
    refine (Nat.lt_succ_iff.1 i.prop).antisymm' (Nat.le_of_succ_le_succ ?_)
    calc
      n + 1 = (Finset.univ : Finset (Fin (n + 1))).card := (Finset.card_fin _).symm
      _ = (Finset.univ.image c).card := (Finset.card_image_iff.mpr h₁.injective.injOn).symm
      _ ≤ (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ)).card :=
        (Finset.card_le_card ?_)
      _ ≤ (Finset.univ : Finset (Fin (i + 1))).card := Finset.card_image_le
      _ = i + 1 := Finset.card_fin _
    intro r hr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
    have := h₂.2 ⟨j, rfl⟩
    rw [hi'] at this
    have h := (dvd_prime_pow (show Prime (c 1) from ?_) i).1 this
    · rcases h with ⟨u, hu, hu'⟩
      refine Finset.mem_image.mpr ⟨⟨u, Nat.lt_succ_of_le hu⟩, Finset.mem_univ _, ?_⟩
      rwa [associated_iff_eq, eq_comm] at hu'
    · rw [← irreducible_iff_prime]
      exact second_of_chain_is_irreducible hn h₁ (@h₂) hq

theorem isPrimePow_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : IsPrimePow q :=
  ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq),
    zero_lt_iff.mpr hn, (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

end DivisorChain

variable {N : Type*} [CancelCommMonoidWithZero N]

theorem factor_orderIso_map_one_eq_bot {m : Associates M} {n : Associates N}
    (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) :
    (d ⟨1, one_dvd m⟩ : Associates N) = 1 := by
  letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
  letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  letI : BotHomClass ({ l // l ≤ m } ≃o { l // l ≤ n }) _ _ := OrderIsoClass.toBotHomClass
  exact map_bot d

theorem coe_factor_orderIso_map_eq_one_iff {m u : Associates M} {n : Associates N} (hu' : u ≤ m)
    (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ : Associates N) = 1 ↔ u = 1 :=
  ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u, hu'⟩, (d ⟨u, hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    congr, fun hu => by
    simp_rw [hu]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d]
    rfl⟩

section

variable [UniqueFactorizationMonoid N] [UniqueFactorizationMonoid M]

open DivisorChain

theorem pow_image_of_prime_by_factor_orderIso_dvd
    {m p : Associates M} {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    (d : Set.Iic m ≃o Set.Iic n) {s : ℕ} (hs' : p ^ s ≤ m) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s ≤ n := by
  by_cases hs : s = 0
  · simp [← Associates.bot_eq_one, hs]
  suffices (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s =
      (d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalized_factor p hp)
  let c₂ : Fin (s + 1) → Associates N := fun t => d ⟨c₁ t, le_trans (hc₁''.2 ⟨t, by simp⟩) hs'⟩
  have c₂_def : ∀ t, c₂ t = d ⟨c₁ t, _⟩ := fun t => rfl
  rw [← c₂_def]
  refine (eq_pow_second_of_chain_of_has_chain hs (fun t u h => ?_)
    (@fun r => ⟨@fun hr => ?_, ?_⟩) ?_).symm
  · rw [c₂_def, c₂_def, Subtype.coe_lt_coe, d.lt_iff_lt, Subtype.mk_lt_mk, hc₁'.lt_iff_lt]
    exact h
  · have : r ≤ n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2
    suffices d.symm ⟨r, this⟩ ≤ ⟨c₁ 1 ^ s, hs'⟩ by
      obtain ⟨i, hi⟩ := hc₁''.1 this
      use i
      simp only [c₂_def, ← hi, d.apply_symm_apply, Subtype.coe_eta, Subtype.coe_mk]
    conv_rhs => rw [← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩]
    rw [d.symm.le_iff_le]
    simpa only [← Subtype.coe_le_coe, Subtype.coe_mk] using hr
  · rintro ⟨i, hr⟩
    rw [hr, c₂_def, Subtype.coe_le_coe, d.le_iff_le]
    simpa [Subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩
  exact ne_zero_of_dvd_ne_zero hn (Subtype.prop (d ⟨c₁ 1 ^ s, _⟩))

theorem map_prime_of_factor_orderIso {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    Prime (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) := by
  rw [← irreducible_iff_prime]
  refine (Associates.isAtom_iff <|
    ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop).mp ⟨?_, fun b hb => ?_⟩
  · rw [Ne, ← Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one,
      coe_factor_orderIso_map_eq_one_iff _ d]
    rintro rfl
    exact (prime_of_normalized_factor 1 hp).not_unit isUnit_one
  · have : b ≤ n := le_trans (le_of_lt hb) (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
    obtain ⟨x, hx⟩ := d.surjective ⟨b, this⟩
    rw [← Subtype.coe_mk (p := (· ≤ n)) b this, ← hx] at hb
    letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
    letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
    suffices x = ⊥ by
      rw [this, OrderIso.map_bot d] at hx
      refine (Subtype.mk_eq_bot_iff ?_ _).mp hx.symm
      simp
    obtain ⟨a, ha⟩ := x
    rw [Subtype.mk_eq_bot_iff]
    · exact
        ((Associates.isAtom_iff <| Prime.ne_zero <| prime_of_normalized_factor p hp).mpr <|
              irreducible_of_normalized_factor p hp).right
          a (Subtype.mk_lt_mk.mp <| d.lt_iff_lt.mp hb)
    simp

theorem mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors {m p : Associates M}
    {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ∈ normalizedFactors n := by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
      (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
  rw [associated_iff_eq] at hq'
  rwa [hq']

theorem emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m ≤ emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm] at hp
  rw [FiniteMultiplicity.of_prime_left (prime_of_normalized_factor p hp) hm
    |>.emultiplicity_eq_multiplicity, ← pow_dvd_iff_le_emultiplicity]
  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicity_dvd ..)

theorem emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m = emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  refine le_antisymm (emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso hp d) ?_
  suffices emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n ≤
      emultiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalizedFactors hp⟩))) m by
    rw [d.symm_apply_apply ⟨p, dvd_of_mem_normalizedFactors hp⟩, Subtype.coe_mk] at this
    exact this
  letI := Classical.decEq (Associates N)
  simpa only [Subtype.coe_eta] using
    emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso
      (mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors hn hp d) d.symm

end

variable [Subsingleton Mˣ] [Subsingleton Nˣ]

/-- The order isomorphism between the factors of `mk m` and the factors of `mk n` induced by a
  bijection between the factors of `m` and the factors of `n` that preserves `∣`. -/
@[simps]
def mkFactorOrderIsoOfFactorDvdEquiv {m : M} {n : N} {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n) where
  toFun l :=
    ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  invFun l :=
    ⟨Associates.mk
        (d.symm
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d.symm ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  left_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, mk_out, out_mk, normalize_eq]
  right_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq, mk_out]
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Associates.mk_le_mk_iff_dvd, hd,
        associatesEquivOfUniqueUnits_apply, out_dvd_iff, mk_out]

variable [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N]

theorem mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors {m p : M} {n : N} (hm : m ≠ 0)
    (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    ↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩) ∈ normalizedFactors n := by
  suffices
    Prime (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
            simp [dvd_of_mem_normalizedFactors hp]⟩ : N) by
    simp only [associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq,
      associatesEquivOfUniqueUnits_symm_apply] at this
    obtain ⟨q, hq, hq'⟩ :=
      exists_mem_normalizedFactors_of_dvd hn this.irreducible
        (d ⟨p, by apply dvd_of_mem_normalizedFactors; convert hp⟩).prop
    rwa [associated_iff_eq.mp hq']
  have :
    Associates.mk
        (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
              simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_apply,
                out_mk, normalize_eq, associatesEquivOfUniqueUnits_symm_apply]⟩ : N) =
      ↑(mkFactorOrderIsoOfFactorDvdEquiv hd
          ⟨associatesEquivOfUniqueUnits.symm p, by
            simp only [associatesEquivOfUniqueUnits_symm_apply]
            exact mk_dvd_mk.mpr (dvd_of_mem_normalizedFactors hp)⟩) := by
    rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [← Associates.prime_mk, this]
  letI := Classical.decEq (Associates M)
  refine map_prime_of_factor_orderIso (mk_ne_zero.mpr hn) ?_ _
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      (prime_mk.mpr (prime_of_normalized_factor p (by convert hp))).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  simpa only [associated_iff_eq.mp hq', associatesEquivOfUniqueUnits_symm_apply] using hq

theorem emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors {m p : M} {n : N}
    (hm : m ≠ 0) (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }} (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ l') :
    emultiplicity (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : N) n = emultiplicity p m := by
  apply Eq.symm
  suffices emultiplicity (Associates.mk p) (Associates.mk m) = emultiplicity (Associates.mk
    ↑(d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
      simp [dvd_of_mem_normalizedFactors hp]⟩)) (Associates.mk n) by
    simpa only [emultiplicity_mk_eq_emultiplicity, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq] using this
  have : Associates.mk (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
    simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq]⟩ : N) =
    ↑(mkFactorOrderIsoOfFactorDvdEquiv hd ⟨associatesEquivOfUniqueUnits.symm p, by
      rw [associatesEquivOfUniqueUnits_symm_apply]
      exact mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp)⟩) := by
    rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [this]
  refine
    emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso (mk_ne_zero.mpr hn) ?_
      (mkFactorOrderIsoOfFactorDvdEquiv hd)
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      (prime_mk.mpr (prime_of_normalized_factor p hp)).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  rwa [associated_iff_eq.mp hq']
