/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Order.Minimal

#align_import ring_theory.ideal.minimal_prime from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# Minimal primes

We provide various results concerning the minimal primes above an ideal

## Main results
- `Ideal.minimalPrimes`: `I.minimalPrimes` is the set of ideals that are minimal primes over `I`.
- `minimalPrimes`: `minimalPrimes R` is the set of minimal primes of `R`.
- `Ideal.exists_minimalPrimes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `Ideal.radical_minimalPrimes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `Ideal.sInf_minimalPrimes`: The intersection of minimal primes over `I` is `I.radical`.
- `Ideal.exists_minimalPrimes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `Ideal.minimalPrimes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.


-/


section

variable {R S : Type*} [CommRing R] [CommRing S] (I J : Ideal R)

/-- `I.minimalPrimes` is the set of ideals that are minimal primes over `I`. -/
protected def Ideal.minimalPrimes : Set (Ideal R) :=
  minimals (· ≤ ·) { p | p.IsPrime ∧ I ≤ p }
#align ideal.minimal_primes Ideal.minimalPrimes

/-- `minimalPrimes R` is the set of minimal primes of `R`.
This is defined as `Ideal.minimalPrimes ⊥`. -/
def minimalPrimes (R : Type*) [CommRing R] : Set (Ideal R) :=
  Ideal.minimalPrimes ⊥
#align minimal_primes minimalPrimes

variable {I J}

theorem Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I ≤ J) : ∃ p ∈ I.minimalPrimes, p ≤ J := by
  suffices
    ∃ m ∈ { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ OrderDual.ofDual p },
      OrderDual.toDual J ≤ m ∧ ∀ z ∈ { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ p }, m ≤ z → z = m by
    obtain ⟨p, h₁, h₂, h₃⟩ := this
    simp_rw [← @eq_comm _ p] at h₃
    exact ⟨p, ⟨h₁, fun a b c => le_of_eq (h₃ a b c)⟩, h₂⟩
  apply zorn_nonempty_partialOrder₀
  -- ⊢ ∀ (c : Set (Ideal R)ᵒᵈ), c ⊆ {p | IsPrime p ∧ I ≤ ↑OrderDual.ofDual p} → IsC …
  swap
  -- ⊢ ↑OrderDual.toDual J ∈ {p | IsPrime p ∧ I ≤ ↑OrderDual.ofDual p}
  · refine' ⟨show J.IsPrime by infer_instance, e⟩
    -- 🎉 no goals
  rintro (c : Set (Ideal R)) hc hc' J' hJ'
  -- ⊢ ∃ ub, ub ∈ {p | IsPrime p ∧ I ≤ ↑OrderDual.ofDual p} ∧ ∀ (z : (Ideal R)ᵒᵈ),  …
  refine'
    ⟨OrderDual.toDual (sInf c),
      ⟨Ideal.sInf_isPrime_of_isChain ⟨J', hJ'⟩ hc'.symm fun x hx => (hc hx).1, _⟩, _⟩
  · rw [OrderDual.ofDual_toDual, le_sInf_iff]
    -- ⊢ ∀ (b : Ideal R), b ∈ c → I ≤ b
    exact fun _ hx => (hc hx).2
    -- 🎉 no goals
  · rintro z hz
    -- ⊢ z ≤ ↑OrderDual.toDual (sInf c)
    rw [OrderDual.le_toDual]
    -- ⊢ sInf c ≤ ↑OrderDual.ofDual z
    exact sInf_le hz
    -- 🎉 no goals
#align ideal.exists_minimal_primes_le Ideal.exists_minimalPrimes_le

@[simp]
theorem Ideal.radical_minimalPrimes : I.radical.minimalPrimes = I.minimalPrimes := by
  rw [Ideal.minimalPrimes, Ideal.minimalPrimes]
  -- ⊢ minimals (fun x x_1 => x ≤ x_1) {p | IsPrime p ∧ radical I ≤ p} = minimals ( …
  congr
  -- ⊢ minimals (fun x x_1 => x ≤ x_1) {p | IsPrime p ∧ radical I ≤ p} = minimals ( …
  ext p
  -- ⊢ p ∈ minimals (fun x x_1 => x ≤ x_1) {p | IsPrime p ∧ radical I ≤ p} ↔ p ∈ mi …
  refine' ⟨_, _⟩ <;> rintro ⟨⟨a, ha⟩, b⟩
  -- ⊢ p ∈ minimals (fun x x_1 => x ≤ x_1) {p | IsPrime p ∧ radical I ≤ p} → p ∈ mi …
                     -- ⊢ p ∈ minimals (fun x x_1 => x ≤ x_1) {p | IsPrime p ∧ I ≤ p}
                     -- ⊢ p ∈ minimals (fun x x_1 => x ≤ x_1) {p | IsPrime p ∧ radical I ≤ p}
  · refine' ⟨⟨a, a.radical_le_iff.1 ha⟩, _⟩
    -- ⊢ ∀ ⦃b : Ideal R⦄, b ∈ {p | IsPrime p ∧ I ≤ p} → (fun x x_1 => x ≤ x_1) b p →  …
    · simp only [Set.mem_setOf_eq, and_imp] at *
      -- ⊢ ∀ ⦃b : Ideal R⦄, IsPrime b → I ≤ b → b ≤ p → p ≤ b
      exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.2 h3) h4
      -- 🎉 no goals
  · refine' ⟨⟨a, a.radical_le_iff.2 ha⟩, _⟩
    -- ⊢ ∀ ⦃b : Ideal R⦄, b ∈ {p | IsPrime p ∧ radical I ≤ p} → (fun x x_1 => x ≤ x_1 …
    · simp only [Set.mem_setOf_eq, and_imp] at *
      -- ⊢ ∀ ⦃b : Ideal R⦄, IsPrime b → radical I ≤ b → b ≤ p → p ≤ b
      exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.1 h3) h4
      -- 🎉 no goals
#align ideal.radical_minimal_primes Ideal.radical_minimalPrimes

@[simp]
theorem Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical := by
  rw [I.radical_eq_sInf]
  -- ⊢ sInf (Ideal.minimalPrimes I) = sInf {J | I ≤ J ∧ IsPrime J}
  apply le_antisymm
  -- ⊢ sInf (Ideal.minimalPrimes I) ≤ sInf {J | I ≤ J ∧ IsPrime J}
  · intro x hx
    -- ⊢ x ∈ sInf {J | I ≤ J ∧ IsPrime J}
    rw [Ideal.mem_sInf] at hx ⊢
    -- ⊢ ∀ ⦃I_1 : Ideal R⦄, I_1 ∈ {J | I ≤ J ∧ IsPrime J} → x ∈ I_1
    rintro J ⟨e, hJ⟩
    -- ⊢ x ∈ J
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le e
    -- ⊢ x ∈ J
    exact hp' (hx hp)
    -- 🎉 no goals
  · apply sInf_le_sInf _
    -- ⊢ Ideal.minimalPrimes I ⊆ {J | I ≤ J ∧ IsPrime J}
    intro I hI
    -- ⊢ I ∈ {J | I✝ ≤ J ∧ IsPrime J}
    exact hI.1.symm
    -- 🎉 no goals
#align ideal.Inf_minimal_primes Ideal.sInf_minimalPrimes

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective {f : R →+* S}
    (hf : Function.Injective f) (p) (H : p ∈ minimalPrimes R) :
    ∃ p' : Ideal S, p'.IsPrime ∧ p'.comap f = p := by
  have := H.1.1
  -- ⊢ ∃ p', IsPrime p' ∧ comap f p' = p
  have : Nontrivial (Localization (Submonoid.map f p.primeCompl)) := by
    refine' ⟨⟨1, 0, _⟩⟩
    convert (IsLocalization.map_injective_of_injective p.primeCompl (Localization.AtPrime p)
        (Localization <| p.primeCompl.map f) hf).ne one_ne_zero
    · rw [map_one]
    · rw [map_zero]
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization (Submonoid.map f p.primeCompl))
  -- ⊢ ∃ p', IsPrime p' ∧ comap f p' = p
  refine' ⟨M.comap (algebraMap S <| Localization (Submonoid.map f p.primeCompl)), inferInstance, _⟩
  -- ⊢ comap f (comap (algebraMap S (Localization (Submonoid.map f (primeCompl p))) …
  rw [Ideal.comap_comap, ← @IsLocalization.map_comp _ _ _ _ _ _ _ _ Localization.isLocalization
      _ _ _ _ p.primeCompl.le_comap_map _ Localization.isLocalization,
    ← Ideal.comap_comap]
  suffices _ ≤ p by exact this.antisymm (H.2 ⟨inferInstance, bot_le⟩ this)
  -- ⊢ comap (algebraMap R (Localization (primeCompl p))) (comap (IsLocalization.ma …
  intro x hx
  -- ⊢ x ∈ p
  by_contra h
  -- ⊢ False
  apply hM.ne_top
  -- ⊢ M = ⊤
  apply M.eq_top_of_isUnit_mem hx
  -- ⊢ IsUnit (↑(IsLocalization.map (Localization (Submonoid.map f (primeCompl p))) …
  apply IsUnit.map
  -- ⊢ IsUnit (↑(algebraMap R (Localization (primeCompl p))) x)
  apply IsLocalization.map_units _ (show p.primeCompl from ⟨x, h⟩)
  -- 🎉 no goals
#align ideal.exists_comap_eq_of_mem_minimal_primes_of_injective Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' : Ideal S, p'.IsPrime ∧ I ≤ p' ∧ p'.comap f = p := by
  have := H.1.1
  -- ⊢ ∃ p', IsPrime p' ∧ I ≤ p' ∧ comap f p' = p
  let f' := (Ideal.Quotient.mk I).comp f
  -- ⊢ ∃ p', IsPrime p' ∧ I ≤ p' ∧ comap f p' = p
  have e : RingHom.ker f' = I.comap f := by
    ext1
    exact Submodule.Quotient.mk_eq_zero _
  have : RingHom.ker (Ideal.Quotient.mk <| RingHom.ker f') ≤ p := by
    rw [Ideal.mk_ker, e]
    exact H.1.2
  suffices _ by
    have ⟨p', hp₁, hp₂⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
      (RingHom.kerLift_injective f') (p.map <| Ideal.Quotient.mk <| RingHom.ker f') this
    refine' ⟨p'.comap <| Ideal.Quotient.mk I, Ideal.IsPrime.comap _, _, _⟩
    · exact Ideal.mk_ker.symm.trans_le (Ideal.comap_mono bot_le)
    · convert congr_arg (Ideal.comap <| Ideal.Quotient.mk <| RingHom.ker f') hp₂
      rwa [Ideal.comap_map_of_surjective (Ideal.Quotient.mk <| RingHom.ker f')
        Ideal.Quotient.mk_surjective, eq_comm, sup_eq_left]
  refine' ⟨⟨_, bot_le⟩, _⟩
  -- ⊢ IsPrime (map (Quotient.mk (RingHom.ker f')) p)
  · apply Ideal.map_isPrime_of_surjective _ this
    -- ⊢ Function.Surjective ↑(Quotient.mk (RingHom.ker f'))
    exact Ideal.Quotient.mk_surjective
    -- 🎉 no goals
  · rintro q ⟨hq, -⟩ hq'
    -- ⊢ map (Quotient.mk (RingHom.ker f')) p ≤ q
    rw [← Ideal.map_comap_of_surjective
        (Ideal.Quotient.mk (RingHom.ker ((Ideal.Quotient.mk I).comp f)))
        Ideal.Quotient.mk_surjective q]
    apply Ideal.map_mono
    -- ⊢ p ≤ comap (Quotient.mk (RingHom.ker (RingHom.comp (Quotient.mk I) f))) q
    apply H.2
    -- ⊢ comap (Quotient.mk (RingHom.ker (RingHom.comp (Quotient.mk I) f))) q ∈ {p |  …
    · refine' ⟨inferInstance, (Ideal.mk_ker.trans e).symm.trans_le (Ideal.comap_mono bot_le)⟩
      -- 🎉 no goals
    · refine' (Ideal.comap_mono hq').trans _
      -- ⊢ comap (Quotient.mk (RingHom.ker (RingHom.comp (Quotient.mk I) f))) (map (Quo …
      rw [Ideal.comap_map_of_surjective]
      -- ⊢ p ⊔ comap (Quotient.mk (RingHom.ker (RingHom.comp (Quotient.mk I) f))) ⊥ ≤ p
      exacts [sup_le rfl.le this, Ideal.Quotient.mk_surjective]
      -- 🎉 no goals
#align ideal.exists_comap_eq_of_mem_minimal_primes Ideal.exists_comap_eq_of_mem_minimalPrimes

theorem Ideal.exists_minimalPrimes_comap_eq {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' ∈ I.minimalPrimes, Ideal.comap f p' = p := by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  -- ⊢ ∃ p', p' ∈ Ideal.minimalPrimes I ∧ comap f p' = p
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  -- ⊢ ∃ p', p' ∈ Ideal.minimalPrimes I ∧ comap f p' = p
  refine' ⟨q, hq, Eq.symm _⟩
  -- ⊢ p = comap f q
  have := hq.1.1
  -- ⊢ p = comap f q
  have := (Ideal.comap_mono hq').trans_eq h₃
  -- ⊢ p = comap f q
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.1.2⟩ this).antisymm this
  -- 🎉 no goals
#align ideal.exists_minimal_primes_comap_eq Ideal.exists_minimalPrimes_comap_eq

theorem Ideal.mimimal_primes_comap_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    {I J : Ideal S} (h : J ∈ I.minimalPrimes) : J.comap f ∈ (I.comap f).minimalPrimes := by
  have := h.1.1
  -- ⊢ comap f J ∈ Ideal.minimalPrimes (comap f I)
  refine' ⟨⟨inferInstance, Ideal.comap_mono h.1.2⟩, _⟩
  -- ⊢ ∀ ⦃b : Ideal R⦄, b ∈ {p | IsPrime p ∧ comap f I ≤ p} → (fun x x_1 => x ≤ x_1 …
  rintro K ⟨hK, e₁⟩ e₂
  -- ⊢ comap f J ≤ K
  have : RingHom.ker f ≤ K := (Ideal.comap_mono bot_le).trans e₁
  -- ⊢ comap f J ≤ K
  rw [← sup_eq_left.mpr this, RingHom.ker_eq_comap_bot, ← Ideal.comap_map_of_surjective f hf]
  -- ⊢ comap f J ≤ comap f (map f K)
  apply Ideal.comap_mono _
  -- ⊢ J ≤ map f K
  apply h.2 _ _
  -- ⊢ map f K ∈ {p | IsPrime p ∧ I ≤ p}
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
    -- 🎉 no goals
  · exact Ideal.map_le_of_le_comap e₂
    -- 🎉 no goals
#align ideal.mimimal_primes_comap_of_surjective Ideal.mimimal_primes_comap_of_surjective

theorem Ideal.comap_minimalPrimes_eq_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    (I : Ideal S) : (I.comap f).minimalPrimes = Ideal.comap f '' I.minimalPrimes := by
  ext J
  -- ⊢ J ∈ Ideal.minimalPrimes (comap f I) ↔ J ∈ comap f '' Ideal.minimalPrimes I
  constructor
  -- ⊢ J ∈ Ideal.minimalPrimes (comap f I) → J ∈ comap f '' Ideal.minimalPrimes I
  · intro H
    -- ⊢ J ∈ comap f '' Ideal.minimalPrimes I
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    -- ⊢ comap f p ∈ comap f '' Ideal.minimalPrimes I
    exact ⟨p, h, rfl⟩
    -- 🎉 no goals
  · rintro ⟨J, hJ, rfl⟩
    -- ⊢ comap f J ∈ Ideal.minimalPrimes (comap f I)
    exact Ideal.mimimal_primes_comap_of_surjective hf hJ
    -- 🎉 no goals
#align ideal.comap_minimal_primes_eq_of_surjective Ideal.comap_minimalPrimes_eq_of_surjective

theorem Ideal.minimalPrimes_eq_comap :
    I.minimalPrimes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
  rw [minimalPrimes, ← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
#align ideal.minimal_primes_eq_comap Ideal.minimalPrimes_eq_comap

theorem Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes = {I.radical} := by
  ext J
  -- ⊢ J ∈ Ideal.minimalPrimes I ↔ J ∈ {radical I}
  constructor
  -- ⊢ J ∈ Ideal.minimalPrimes I → J ∈ {radical I}
  · exact fun H =>
      let e := H.1.1.radical_le_iff.mpr H.1.2
      (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ e).antisymm e
  · rintro (rfl : J = I.radical)
    -- ⊢ radical I ∈ Ideal.minimalPrimes I
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩
    -- 🎉 no goals
#align ideal.minimal_primes_eq_subsingleton Ideal.minimalPrimes_eq_subsingleton

theorem Ideal.minimalPrimes_eq_subsingleton_self [I.IsPrime] : I.minimalPrimes = {I} := by
  ext J
  -- ⊢ J ∈ Ideal.minimalPrimes I ↔ J ∈ {I}
  constructor
  -- ⊢ J ∈ Ideal.minimalPrimes I → J ∈ {I}
  · exact fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.1.2).antisymm H.1.2
    -- 🎉 no goals
  · rintro (rfl : J = I)
    -- ⊢ J ∈ Ideal.minimalPrimes J
    refine' ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩
    -- 🎉 no goals
#align ideal.minimal_primes_eq_subsingleton_self Ideal.minimalPrimes_eq_subsingleton_self

end
