/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Squarefree
import Mathlib.Order.Hom.Bounded
import Mathlib.Algebra.GCDMonoid.Basic

#align_import ring_theory.chain_of_divisors from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"
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


## Todo
- Create a structure for chains of divisors.
- Simplify proof of `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors` using
  `mem_normalizedFactors_factor_order_iso_of_mem_normalizedFactors` or vice versa.

-/


variable {M : Type*} [CancelCommMonoidWithZero M]

theorem Associates.isAtom_iff {p : Associates M} (h₁ : p ≠ 0) : IsAtom p ↔ Irreducible p :=
  ⟨fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one] using hp.1, fun a b h =>
        -- 🎉 no goals
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.isUnit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            -- ⊢ IsUnit b
            apply isUnit_of_associated_mul (show Associated (p * b) p by conv_rhs => rw [h]) h₁)⟩,
            -- 🎉 no goals
    fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one, Associates.bot_eq_one] using hp.1,
        -- 🎉 no goals
      fun b ⟨⟨a, hab⟩, hb⟩ =>
      (hp.isUnit_or_isUnit hab).casesOn
        (fun hb => show b = ⊥ by rwa [Associates.isUnit_iff_eq_one, ← Associates.bot_eq_one] at hb)
                                 -- 🎉 no goals
        fun ha =>
        absurd
          (show p ∣ b from
            ⟨(ha.unit⁻¹ : Units _), by
              simp [hab]; rw [mul_assoc]; rw [IsUnit.mul_val_inv ha]; rw [mul_one]⟩)
              -- ⊢ b = b * a * ↑(IsUnit.unit ha)⁻¹
                          -- ⊢ b = b * (a * ↑(IsUnit.unit ha)⁻¹)
                                          -- ⊢ b = b * 1
                                                                      -- 🎉 no goals
          hb⟩⟩
#align associates.is_atom_iff Associates.isAtom_iff

open UniqueFactorizationMonoid multiplicity Irreducible Associates

namespace DivisorChain

theorem exists_chain_of_prime_pow {p : Associates M} {n : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    ∃ c : Fin (n + 1) → Associates M,
      c 1 = p ∧ StrictMono c ∧ ∀ {r : Associates M}, r ≤ p ^ n ↔ ∃ i, r = c i := by
  refine' ⟨fun i => p ^ (i : ℕ), _, fun n m h => _, @fun y => ⟨fun h => _, _⟩⟩
  · dsimp only
    -- ⊢ p ^ ↑1 = p
    rw [Fin.val_one', Nat.mod_eq_of_lt, pow_one]
    -- ⊢ 1 < n + 1
    exact Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn)
    -- 🎉 no goals
  · exact Associates.dvdNotUnit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_zero, p ^ (m - n : ℕ),
          not_isUnit_of_not_isUnit_dvd hp.not_unit (dvd_pow dvd_rfl (Nat.sub_pos_of_lt h).ne'),
          (pow_mul_pow_sub p h.le).symm⟩
  · obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h
    -- ⊢ ∃ i, y = (fun i => p ^ ↑i) i
    rw [associated_iff_eq] at hi
    -- ⊢ ∃ i, y = (fun i => p ^ ↑i) i
    exact ⟨⟨i, Nat.lt_succ_of_le i_le⟩, hi⟩
    -- 🎉 no goals
  · rintro ⟨i, rfl⟩
    -- ⊢ (fun i => p ^ ↑i) i ≤ p ^ n
    exact ⟨p ^ (n - i : ℕ), (pow_mul_pow_sub p (Nat.succ_le_succ_iff.mp i.2)).symm⟩
    -- 🎉 no goals
#align divisor_chain.exists_chain_of_prime_pow DivisorChain.exists_chain_of_prime_pow

theorem element_of_chain_not_isUnit_of_index_ne_zero {n : ℕ} {i : Fin (n + 1)} (i_pos : i ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) : ¬IsUnit (c i) :=
  DvdNotUnit.not_unit
    (Associates.dvdNotUnit_iff_lt.2
      (h₁ <| show (0 : Fin (n + 1)) < i from Fin.pos_iff_ne_zero.mpr i_pos))
#align divisor_chain.element_of_chain_not_is_unit_of_index_ne_zero DivisorChain.element_of_chain_not_isUnit_of_index_ne_zero

theorem first_of_chain_isUnit {q : Associates M} {n : ℕ} {c : Fin (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp Associates.one_le
  -- ⊢ IsUnit (c 0)
  rw [Associates.isUnit_iff_eq_one, ← Associates.le_one_iff, hr]
  -- ⊢ c 0 ≤ c i
  exact h₁.monotone (Fin.zero_le i)
  -- 🎉 no goals
#align divisor_chain.first_of_chain_is_unit DivisorChain.first_of_chain_isUnit

/-- The second element of a chain is irreducible. -/
theorem second_of_chain_is_irreducible {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
    (hq : q ≠ 0) : Irreducible (c 1) := by
  cases' n with n; · contradiction
  -- ⊢ Irreducible (c 1)
                     -- 🎉 no goals
  refine' (Associates.isAtom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨_, fun b hb => _⟩
  -- ⊢ c 1 ≠ ⊥
  · exact ne_bot_of_gt (h₁ (show (0 : Fin (n + 2)) < 1 from Fin.one_pos))
    -- 🎉 no goals
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  -- ⊢ c { val := i, isLt := hi } = ⊥
  cases i
  -- ⊢ c { val := Nat.zero, isLt := hi } = ⊥
  · exact (Associates.isUnit_iff_eq_one _).mp (first_of_chain_isUnit h₁ @h₂)
    -- 🎉 no goals
  · simpa [Fin.lt_iff_val_lt_val] using h₁.lt_iff_lt.mp hb
    -- 🎉 no goals
#align divisor_chain.second_of_chain_is_irreducible DivisorChain.second_of_chain_is_irreducible

theorem eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r) :
    p = c 1 := by
  cases' n with n
  -- ⊢ p = c 1
  · contradiction
    -- 🎉 no goals
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  -- ⊢ c i = c 1
  refine' congr_arg c (eq_of_ge_of_not_gt _ fun hi => _)
  -- ⊢ 1 ≤ i
  · rw [Fin.le_iff_val_le_val, Fin.val_one, Nat.succ_le_iff, ← Fin.val_zero' (n.succ + 1), ←
      Fin.lt_iff_val_lt_val, Fin.pos_iff_ne_zero]
    rintro rfl
    -- ⊢ False
    exact hp.not_unit (first_of_chain_isUnit h₁ @h₂)
    -- 🎉 no goals
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  -- ⊢ False
  · cases hi
    -- 🎉 no goals
  refine'
    not_irreducible_of_not_unit_dvdNotUnit
      (DvdNotUnit.not_unit
        (Associates.dvdNotUnit_iff_lt.2 (h₁ (show (0 : Fin (n + 2)) < j from _))))
      _ hp.irreducible
  · simpa [Fin.succ_lt_succ_iff, Fin.lt_iff_val_lt_val] using hi
    -- 🎉 no goals
  · refine' Associates.dvdNotUnit_iff_lt.2 (h₁ _)
    -- ⊢ ↑↑j < Fin.succ j
    simpa only [Fin.coe_eq_castSucc] using Fin.lt_succ
    -- 🎉 no goals
#align divisor_chain.eq_second_of_chain_of_prime_dvd DivisorChain.eq_second_of_chain_of_prime_dvd

theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : ℕ}
    {c : Fin (n + 1) → Associates M} (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) {m : Finset (Associates M)}
    (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 := by
  classical
    have mem_image : ∀ r : Associates M, r ≤ q → r ∈ Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_of_subset fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le
#align divisor_chain.card_subset_divisors_le_length_of_chain DivisorChain.card_subset_divisors_le_length_of_chain

variable [UniqueFactorizationMonoid M]

theorem element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
    (hr : r ∣ q) (hq : q ≠ 0) : ∃ i : Fin (n + 1), r = c 1 ^ (i : ℕ) := by
  classical
    let i := Multiset.card (normalizedFactors r)
    have hi : normalizedFactors r = Multiset.replicate i (c 1) := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      refine'
        eq_second_of_chain_of_prime_dvd hn h₁ (@fun r' => h₂) (prime_of_normalized_factor b hb) hr
          (dvd_of_mem_normalizedFactors hb)
    have H : r = c 1 ^ i := by
      have := UniqueFactorizationMonoid.normalizedFactors_prod (ne_zero_of_dvd_ne_zero hq hr)
      rw [associated_iff_eq, hi, Multiset.prod_replicate] at this
      rw [this]
    refine' ⟨⟨i, _⟩, H⟩
    have : (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ)).card = i + 1 := by
      conv_rhs => rw [← Finset.card_fin (i + 1)]
      cases n
      · contradiction
      rw [Finset.card_image_iff]
      refine' Set.injOn_of_injective (fun m m' h => Fin.ext _) _
      refine'
        pow_injective_of_not_unit (element_of_chain_not_isUnit_of_index_ne_zero (by simp) h₁) _ h
      exact Irreducible.ne_zero (second_of_chain_is_irreducible hn h₁ (@h₂) hq)
    suffices H' : ∀ r ∈ Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ), r ≤ q
    · simp only [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← this]
      apply card_subset_divisors_le_length_of_chain (@h₂) H'
    simp only [Finset.mem_image]
    rintro r ⟨a, _, rfl⟩
    refine' dvd_trans _ hr
    use c 1 ^ (i - (a : ℕ))
    rw [pow_mul_pow_sub (c 1)]
    · exact H
    · exact Nat.succ_le_succ_iff.mp a.2
#align divisor_chain.element_of_chain_eq_pow_second_of_chain DivisorChain.element_of_chain_eq_pow_second_of_chain

theorem eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : q = c 1 ^ n := by
  classical
    obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (@fun r => h₂) (dvd_refl q) hq
    convert hi'
    refine' (Nat.lt_succ_iff.1 i.prop).antisymm' (Nat.le_of_succ_le_succ _)
    calc
      n + 1 = (Finset.univ : Finset (Fin (n + 1))).card := (Finset.card_fin _).symm
      _ = (Finset.univ.image c).card := (Finset.card_image_iff.mpr (h₁.injective.injOn _)).symm
      _ ≤ (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ)).card :=
        (Finset.card_le_of_subset ?_)
      _ ≤ (Finset.univ : Finset (Fin (i + 1))).card := Finset.card_image_le
      _ = i + 1 := Finset.card_fin _
    intro r hr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
    have := h₂.2 ⟨j, rfl⟩
    rw [hi'] at this
    have h := (dvd_prime_pow (show Prime (c 1) from ?_) i).1 this
    rcases h with ⟨u, hu, hu'⟩
    refine' Finset.mem_image.mpr ⟨u, Finset.mem_univ _, _⟩
    · rw [associated_iff_eq] at hu'
      rw [Fin.val_cast_of_lt (Nat.lt_succ_of_le hu), hu']
    · rw [← irreducible_iff_prime]
      exact second_of_chain_is_irreducible hn h₁ (@h₂) hq
#align divisor_chain.eq_pow_second_of_chain_of_has_chain DivisorChain.eq_pow_second_of_chain_of_has_chain

theorem isPrimePow_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : IsPrimePow q :=
  ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq),
    zero_lt_iff.mpr hn, (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩
#align divisor_chain.is_prime_pow_of_has_chain DivisorChain.isPrimePow_of_has_chain

end DivisorChain

variable {N : Type*} [CancelCommMonoidWithZero N]

theorem factor_orderIso_map_one_eq_bot {m : Associates M} {n : Associates N}
    (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) :
    (d ⟨1, one_dvd m⟩ : Associates N) = 1 := by
  letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
  -- ⊢ ↑(↑d { val := 1, property := (_ : 1 ∣ m) }) = 1
  letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
  -- ⊢ ↑(↑d { val := 1, property := (_ : 1 ∣ m) }) = 1
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  -- ⊢ ↑d ⊥ = ⊥
  letI : BotHomClass ({ l // l ≤ m } ≃o { l // l ≤ n }) _ _ := OrderIsoClass.toBotHomClass
  -- ⊢ ↑d ⊥ = ⊥
  exact map_bot d
  -- 🎉 no goals
#align factor_order_iso_map_one_eq_bot factor_orderIso_map_one_eq_bot

theorem coe_factor_orderIso_map_eq_one_iff {m u : Associates M} {n : Associates N} (hu' : u ≤ m)
    (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ : Associates N) = 1 ↔ u = 1 :=
  ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u, hu'⟩, (d ⟨u, hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    -- ⊢ ↑(↑(OrderIso.symm d) { val := ↑(↑d { val := u, property := hu' }), property  …
    congr, fun hu => by
    -- 🎉 no goals
    simp_rw [hu]
    -- ⊢ ↑(↑d { val := 1, property := (_ : (fun x => x ∈ Set.Iic m) 1) }) = 1
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d]⟩
    -- 🎉 no goals
#align coe_factor_order_iso_map_eq_one_iff coe_factor_orderIso_map_eq_one_iff

section

variable [UniqueFactorizationMonoid N] [UniqueFactorizationMonoid M]

open DivisorChain

theorem pow_image_of_prime_by_factor_orderIso_dvd
    [DecidableEq (Associates M)] {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) {s : ℕ} (hs' : p ^ s ≤ m) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s ≤ n := by
  by_cases hs : s = 0
  -- ⊢ ↑(↑d { val := p, property := (_ : p ∣ m) }) ^ s ≤ n
  · simp [hs]
    -- 🎉 no goals
  suffices (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s =
      (d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalized_factor p hp)
  -- ⊢ ↑(↑d { val := c₁ 1, property := (_ : c₁ 1 ∣ m) }) ^ s = ↑(↑d { val := c₁ 1 ^ …
  let c₂ : Fin (s + 1) → Associates N := fun t => d ⟨c₁ t, le_trans (hc₁''.2 ⟨t, by simp⟩) hs'⟩
  -- ⊢ ↑(↑d { val := c₁ 1, property := (_ : c₁ 1 ∣ m) }) ^ s = ↑(↑d { val := c₁ 1 ^ …
  have c₂_def : ∀ t, c₂ t = d ⟨c₁ t, _⟩ := fun t => rfl
  -- ⊢ ↑(↑d { val := c₁ 1, property := (_ : c₁ 1 ∣ m) }) ^ s = ↑(↑d { val := c₁ 1 ^ …
  rw [← c₂_def]
  -- ⊢ c₂ 1 ^ s = ↑(↑d { val := c₁ 1 ^ s, property := hs' })
  refine'
    (eq_pow_second_of_chain_of_has_chain hs (fun t u h => _) (@fun r => ⟨@fun hr => _, _⟩) _).symm
  · rw [c₂_def, c₂_def, Subtype.coe_lt_coe, d.lt_iff_lt, Subtype.mk_lt_mk, hc₁'.lt_iff_lt]
    -- ⊢ t < u
    exact h
    -- 🎉 no goals
  · have : r ≤ n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2
    -- ⊢ ∃ i, r = c₂ i
    suffices d.symm ⟨r, this⟩ ≤ ⟨c₁ 1 ^ s, hs'⟩ by
      obtain ⟨i, hi⟩ := hc₁''.1 this
      use i
      simp only [c₂_def, ← hi, d.apply_symm_apply, Subtype.coe_eta, Subtype.coe_mk]
    conv_rhs => rw [← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩]
    -- ⊢ ↑(OrderIso.symm d) { val := r, property := this } ≤ ↑(OrderIso.symm d) (↑d { …
    rw [d.symm.le_iff_le]
    -- ⊢ { val := r, property := this } ≤ ↑d { val := c₁ 1 ^ s, property := hs' }
    simpa only [← Subtype.coe_le_coe, Subtype.coe_mk] using hr
    -- 🎉 no goals
  · rintro ⟨i, hr⟩
    -- ⊢ r ≤ ↑(↑d { val := c₁ 1 ^ s, property := hs' })
    rw [hr, c₂_def, Subtype.coe_le_coe, d.le_iff_le]
    -- ⊢ { val := c₁ i, property := (_ : c₁ i ≤ m) } ≤ { val := c₁ 1 ^ s, property := …
    simpa [Subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩
    -- 🎉 no goals
  exact ne_zero_of_dvd_ne_zero hn (Subtype.prop (d ⟨c₁ 1 ^ s, _⟩))
  -- 🎉 no goals
#align pow_image_of_prime_by_factor_order_iso_dvd pow_image_of_prime_by_factor_orderIso_dvd

theorem map_prime_of_factor_orderIso [DecidableEq (Associates M)] {m p : Associates M}
    {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    Prime (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) := by
  rw [← irreducible_iff_prime]
  -- ⊢ Irreducible ↑(↑d { val := p, property := (_ : p ∣ m) })
  refine' (Associates.isAtom_iff <| ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop).mp ⟨_, fun b hb => _⟩
  -- ⊢ ↑(↑d { val := p, property := (_ : p ∣ m) }) ≠ ⊥
  · rw [Ne.def, ← Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one,
      coe_factor_orderIso_map_eq_one_iff _ d]
    rintro rfl
    -- ⊢ False
    exact (prime_of_normalized_factor 1 hp).not_unit isUnit_one
    -- 🎉 no goals
  · obtain ⟨x, hx⟩ :=
      d.surjective ⟨b, le_trans (le_of_lt hb) (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop⟩
    rw [← Subtype.coe_mk b _, ← hx] at hb
    -- ⊢ b = ⊥
    letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
    -- ⊢ b = ⊥
    letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
    -- ⊢ b = ⊥
    suffices x = ⊥ by
      rw [this, OrderIso.map_bot d] at hx
      refine' (Subtype.mk_eq_bot_iff _ _).mp hx.symm
      simp
    obtain ⟨a, ha⟩ := x
    -- ⊢ { val := a, property := ha } = ⊥
    rw [Subtype.mk_eq_bot_iff]
    -- ⊢ a = ⊥
    · exact
        ((Associates.isAtom_iff <| Prime.ne_zero <| prime_of_normalized_factor p hp).mpr <|
              irreducible_of_normalized_factor p hp).right
          a (Subtype.mk_lt_mk.mp <| d.lt_iff_lt.mp hb)
    simp
    -- 🎉 no goals
#align map_prime_of_factor_order_iso map_prime_of_factor_orderIso

theorem mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors [DecidableEq (Associates M)]
    [DecidableEq (Associates N)] {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ∈ normalizedFactors n := by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
      (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
  rw [associated_iff_eq] at hq'
  -- ⊢ ↑(↑d { val := p, property := (_ : p ∣ m) }) ∈ normalizedFactors n
  rwa [hq']
  -- 🎉 no goals
#align mem_normalized_factors_factor_order_iso_of_mem_normalized_factors mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors

variable [DecidableRel ((· ∣ ·) : M → M → Prop)] [DecidableRel ((· ∣ ·) : N → N → Prop)]

theorem multiplicity_prime_le_multiplicity_image_by_factor_orderIso [DecidableEq (Associates M)]
    {m p : Associates M} {n : Associates N} (hp : p ∈ normalizedFactors m)
    (d : Set.Iic m ≃o Set.Iic n) :
    multiplicity p m ≤ multiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  by_cases hn : n = 0
  -- ⊢ multiplicity p m ≤ multiplicity (↑(↑d { val := p, property := (_ : p ∣ m) }) …
  · simp [hn]
    -- 🎉 no goals
  by_cases hm : m = 0
  -- ⊢ multiplicity p m ≤ multiplicity (↑(↑d { val := p, property := (_ : p ∣ m) }) …
  · simp [hm] at hp
    -- 🎉 no goals
  rw [←
    PartENat.natCast_get
      (finite_iff_dom.1 <| finite_prime_left (prime_of_normalized_factor p hp) hm),
    ← pow_dvd_iff_le_multiplicity]
  exact pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicity_dvd _)
  -- 🎉 no goals
#align multiplicity_prime_le_multiplicity_image_by_factor_order_iso multiplicity_prime_le_multiplicity_image_by_factor_orderIso

theorem multiplicity_prime_eq_multiplicity_image_by_factor_orderIso [DecidableEq (Associates M)]
    {m p : Associates M} {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    (d : Set.Iic m ≃o Set.Iic n) :
    multiplicity p m = multiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  refine' le_antisymm (multiplicity_prime_le_multiplicity_image_by_factor_orderIso hp d) _
  -- ⊢ multiplicity (↑(↑d { val := p, property := (_ : p ∣ m) })) n ≤ multiplicity  …
  suffices multiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n ≤
      multiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalizedFactors hp⟩))) m by
    rw [d.symm_apply_apply ⟨p, dvd_of_mem_normalizedFactors hp⟩, Subtype.coe_mk] at this
    exact this
  letI := Classical.decEq (Associates N)
  -- ⊢ multiplicity (↑(↑d { val := p, property := (_ : p ∣ m) })) n ≤ multiplicity  …
  simpa only [Subtype.coe_eta] using
    multiplicity_prime_le_multiplicity_image_by_factor_orderIso
      (mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors hn hp d) d.symm
#align multiplicity_prime_eq_multiplicity_image_by_factor_order_iso multiplicity_prime_eq_multiplicity_image_by_factor_orderIso

end

variable [Unique Mˣ] [Unique Nˣ]

/-- The order isomorphism between the factors of `mk m` and the factors of `mk n` induced by a
  bijection between the factors of `m` and the factors of `n` that preserves `∣`. -/
@[simps]
def mkFactorOrderIsoOfFactorDvdEquiv {m : M} {n : N} {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n)
    where
  toFun l :=
    ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            -- ⊢ ↑associatesEquivOfUniqueUnits ↑{ val := x, property := hx } ∣ m
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            -- ⊢ x ≤ Associates.mk m
            exact hx⟩),
            -- 🎉 no goals
      mk_le_mk_iff_dvd_iff.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  invFun l :=
    ⟨Associates.mk
        (d.symm
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            -- ⊢ ↑associatesEquivOfUniqueUnits ↑{ val := x, property := hx } ∣ n
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            -- ⊢ x ≤ Associates.mk n
            exact hx⟩),
            -- 🎉 no goals
      mk_le_mk_iff_dvd_iff.mpr (Subtype.prop (d.symm ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  left_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, mk_out, out_mk, normalize_eq]
  right_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq, mk_out]
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    -- ⊢ ↑{ toFun := fun l => { val := Associates.mk ↑(↑d { val := ↑associatesEquivOf …
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Associates.mk_le_mk_iff_dvd_iff, hd,
        Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff, mk_out]
#align mk_factor_order_iso_of_factor_dvd_equiv mkFactorOrderIsoOfFactorDvdEquiv

variable [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N] [DecidableEq M]

theorem mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors [DecidableEq N] {m p : M}
    {n : N} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
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
  -- ⊢ Prime ↑(↑(mkFactorOrderIsoOfFactorDvdEquiv hd) { val := ↑(MulEquiv.symm asso …
  letI := Classical.decEq (Associates M)
  -- ⊢ Prime ↑(↑(mkFactorOrderIsoOfFactorDvdEquiv hd) { val := ↑(MulEquiv.symm asso …
  refine' map_prime_of_factor_orderIso (mk_ne_zero.mpr hn) _ _
  -- ⊢ ↑(MulEquiv.symm associatesEquivOfUniqueUnits) p ∈ normalizedFactors (Associa …
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      ((prime_mk p).mpr (prime_of_normalized_factor p (by convert hp))).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  simpa only [associated_iff_eq.mp hq', associatesEquivOfUniqueUnits_symm_apply] using hq
  -- 🎉 no goals
#align mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors

variable [DecidableRel ((· ∣ ·) : M → M → Prop)] [DecidableRel ((· ∣ ·) : N → N → Prop)]

theorem multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalizedFactors {m p : M} {n : N}
    (hm : m ≠ 0) (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }} (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ l') :
    multiplicity (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : N) n = multiplicity p m := by
  apply Eq.symm
  -- ⊢ multiplicity p m = multiplicity (↑(↑d { val := p, property := (_ : p ∣ m) }) …
  suffices multiplicity (Associates.mk p) (Associates.mk m) = multiplicity (Associates.mk
    ↑(d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
      simp [dvd_of_mem_normalizedFactors hp]⟩)) (Associates.mk n) by
    simpa only [multiplicity_mk_eq_multiplicity, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq] using this
  have : Associates.mk (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
    simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq]⟩ : N) =
    ↑(mkFactorOrderIsoOfFactorDvdEquiv hd ⟨associatesEquivOfUniqueUnits.symm p, by
      rw [associatesEquivOfUniqueUnits_symm_apply]
      exact mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp)⟩) :=
    by rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [this]
  -- ⊢ multiplicity (Associates.mk p) (Associates.mk m) = multiplicity (↑(↑(mkFacto …
  letI := Classical.decEq (Associates M)
  -- ⊢ multiplicity (Associates.mk p) (Associates.mk m) = multiplicity (↑(↑(mkFacto …
  refine'
    multiplicity_prime_eq_multiplicity_image_by_factor_orderIso (mk_ne_zero.mpr hn) _
      (mkFactorOrderIsoOfFactorDvdEquiv hd)
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      ((prime_mk p).mpr (prime_of_normalized_factor p hp)).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  rwa [associated_iff_eq.mp hq']
  -- 🎉 no goals
#align multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalized_factor multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalizedFactors
