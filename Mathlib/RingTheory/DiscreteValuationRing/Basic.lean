/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.LinearAlgebra.AdicCompletion

#align_import ring_theory.discrete_valuation_ring.basic from "leanprover-community/mathlib"@"c163ec99dfc664628ca15d215fce0a5b9c265b68"

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `DiscreteValuationRing R` : a predicate expressing that R is a DVR.

### Definitions

* `addVal R : AddValuation R PartENat` : the additive valuation on a DVR.

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `Uniformizer` at all, because we can use `Irreducible` instead.

## Tags

discrete valuation ring
-/


open Classical

universe u

open Ideal LocalRing

/-- An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which
  is not a field. -/
class DiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R]
    extends IsPrincipalIdealRing R, LocalRing R : Prop where
  not_a_field' : maximalIdeal R ≠ ⊥
#align discrete_valuation_ring DiscreteValuationRing

namespace DiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [DiscreteValuationRing R]

theorem not_a_field : maximalIdeal R ≠ ⊥ :=
  not_a_field'
#align discrete_valuation_ring.not_a_field DiscreteValuationRing.not_a_field

/-- A discrete valuation ring `R` is not a field. -/
theorem not_isField : ¬IsField R :=
  LocalRing.isField_iff_maximalIdeal_eq.not.mpr (not_a_field R)
#align discrete_valuation_ring.not_is_field DiscreteValuationRing.not_isField

variable {R}

open PrincipalIdealRing

theorem irreducible_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [LocalRing R] [IsDomain R]
    (ϖ : R) (hϖ : ϖ ≠ 0) (h : maximalIdeal R = Ideal.span {ϖ}) : Irreducible ϖ := by
  have h2 : ¬IsUnit ϖ := show ϖ ∈ maximalIdeal R from h.symm ▸ Submodule.mem_span_singleton_self ϖ
  -- ⊢ Irreducible ϖ
  refine' ⟨h2, _⟩
  -- ⊢ ∀ (a b : R), ϖ = a * b → IsUnit a ∨ IsUnit b
  intro a b hab
  -- ⊢ IsUnit a ∨ IsUnit b
  by_contra' h
  -- ⊢ False
  obtain ⟨ha : a ∈ maximalIdeal R, hb : b ∈ maximalIdeal R⟩ := h
  -- ⊢ False
  rw [h, mem_span_singleton'] at ha hb
  -- ⊢ False
  rcases ha with ⟨a, rfl⟩
  -- ⊢ False
  rcases hb with ⟨b, rfl⟩
  -- ⊢ False
  rw [show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)) by ring] at hab
  -- ⊢ False
  apply hϖ
  -- ⊢ ϖ = 0
  apply eq_zero_of_mul_eq_self_right _ hab.symm
  -- ⊢ ϖ * (a * b) ≠ 1
  exact fun hh => h2 (isUnit_of_dvd_one ⟨_, hh.symm⟩)
  -- 🎉 no goals
#align discrete_valuation_ring.irreducible_of_span_eq_maximal_ideal DiscreteValuationRing.irreducible_of_span_eq_maximalIdeal

/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of `R`. -/
theorem irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ} :=
  ⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,
    fun h => irreducible_of_span_eq_maximalIdeal ϖ
      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩
                                    -- 🎉 no goals
#align discrete_valuation_ring.irreducible_iff_uniformizer DiscreteValuationRing.irreducible_iff_uniformizer

theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :
    maximalIdeal R = Ideal.span {ϖ} :=
  (irreducible_iff_uniformizer _).mp h
#align irreducible.maximal_ideal_eq Irreducible.maximalIdeal_eq

variable (R)

/-- Uniformizers exist in a DVR. -/
theorem exists_irreducible : ∃ ϖ : R, Irreducible ϖ := by
  simp_rw [irreducible_iff_uniformizer]
  -- ⊢ ∃ ϖ, maximalIdeal R = span {ϖ}
  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal
  -- 🎉 no goals
#align discrete_valuation_ring.exists_irreducible DiscreteValuationRing.exists_irreducible

/-- Uniformizers exist in a DVR. -/
theorem exists_prime : ∃ ϖ : R, Prime ϖ :=
  (exists_irreducible R).imp fun _ => PrincipalIdealRing.irreducible_iff_prime.1
#align discrete_valuation_ring.exists_prime DiscreteValuationRing.exists_prime

/-- An integral domain is a DVR iff it's a PID with a unique non-zero prime ideal. -/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] :
    DiscreteValuationRing R ↔ IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ IsPrime P := by
  constructor
  -- ⊢ DiscreteValuationRing R → IsPrincipalIdealRing R ∧ ∃! P, P ≠ ⊥ ∧ IsPrime P
  · intro RDVR
    -- ⊢ IsPrincipalIdealRing R ∧ ∃! P, P ≠ ⊥ ∧ IsPrime P
    rcases id RDVR with ⟨Rlocal⟩
    -- ⊢ IsPrincipalIdealRing R ∧ ∃! P, P ≠ ⊥ ∧ IsPrime P
    constructor
    -- ⊢ IsPrincipalIdealRing R
    assumption
    -- ⊢ ∃! P, P ≠ ⊥ ∧ IsPrime P
    use LocalRing.maximalIdeal R
    -- ⊢ (fun P => P ≠ ⊥ ∧ IsPrime P) (maximalIdeal R) ∧ ∀ (y : Ideal R), (fun P => P …
    constructor
    -- ⊢ (fun P => P ≠ ⊥ ∧ IsPrime P) (maximalIdeal R)
    exact ⟨Rlocal, inferInstance⟩
    -- ⊢ ∀ (y : Ideal R), (fun P => P ≠ ⊥ ∧ IsPrime P) y → y = maximalIdeal R
    · rintro Q ⟨hQ1, hQ2⟩
      -- ⊢ Q = maximalIdeal R
      obtain ⟨q, rfl⟩ := (IsPrincipalIdealRing.principal Q).1
      -- ⊢ Submodule.span R {q} = maximalIdeal R
      have hq : q ≠ 0 := by
        rintro rfl
        apply hQ1
        simp
      erw [span_singleton_prime hq] at hQ2
      -- ⊢ Submodule.span R {q} = maximalIdeal R
      replace hQ2 := hQ2.irreducible
      -- ⊢ Submodule.span R {q} = maximalIdeal R
      rw [irreducible_iff_uniformizer] at hQ2
      -- ⊢ Submodule.span R {q} = maximalIdeal R
      exact hQ2.symm
      -- 🎉 no goals
  · rintro ⟨RPID, Punique⟩
    -- ⊢ DiscreteValuationRing R
    haveI : LocalRing R := LocalRing.of_unique_nonzero_prime Punique
    -- ⊢ DiscreteValuationRing R
    refine' { not_a_field' := _ }
    -- ⊢ maximalIdeal R ≠ ⊥
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, _⟩
    -- ⊢ maximalIdeal R ≠ ⊥
    have hPM : P ≤ maximalIdeal R := le_maximalIdeal hP2.1
    -- ⊢ maximalIdeal R ≠ ⊥
    intro h
    -- ⊢ False
    rw [h, le_bot_iff] at hPM
    -- ⊢ False
    exact hP1 hPM
    -- 🎉 no goals
#align discrete_valuation_ring.iff_pid_with_one_nonzero_prime DiscreteValuationRing.iff_pid_with_one_nonzero_prime

theorem associated_of_irreducible {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b := by
  rw [irreducible_iff_uniformizer] at ha hb
  -- ⊢ Associated a b
  rw [← span_singleton_eq_span_singleton, ← ha, hb]
  -- 🎉 no goals
#align discrete_valuation_ring.associated_of_irreducible DiscreteValuationRing.associated_of_irreducible

end DiscreteValuationRing

namespace DiscreteValuationRing

variable (R : Type*)

/-- Alternative characterisation of discrete valuation rings. -/
def HasUnitMulPowIrreducibleFactorization [CommRing R] : Prop :=
  ∃ p : R, Irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ n : ℕ, Associated (p ^ n) x
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization

namespace HasUnitMulPowIrreducibleFactorization

variable {R} [CommRing R] (hR : HasUnitMulPowIrreducibleFactorization R)

theorem unique_irreducible ⦃p q : R⦄ (hp : Irreducible p) (hq : Irreducible q) :
    Associated p q := by
  rcases hR with ⟨ϖ, hϖ, hR⟩
  -- ⊢ Associated p q
  suffices ∀ {p : R} (_ : Irreducible p), Associated p ϖ by
    apply Associated.trans (this hp) (this hq).symm
  clear hp hq p q
  -- ⊢ ∀ {p : R}, Irreducible p → Associated p ϖ
  intro p hp
  -- ⊢ Associated p ϖ
  obtain ⟨n, hn⟩ := hR hp.ne_zero
  -- ⊢ Associated p ϖ
  have : Irreducible (ϖ ^ n) := hn.symm.irreducible hp
  -- ⊢ Associated p ϖ
  rcases lt_trichotomy n 1 with (H | rfl | H)
  · obtain rfl : n = 0 := by
      clear hn this
      revert H n
      exact by decide
    simp [not_irreducible_one, pow_zero] at this
    -- 🎉 no goals
  · simpa only [pow_one] using hn.symm
    -- 🎉 no goals
  · obtain ⟨n, rfl⟩ : ∃ k, n = 1 + k + 1 := Nat.exists_eq_add_of_lt H
    -- ⊢ Associated p ϖ
    rw [pow_succ] at this
    -- ⊢ Associated p ϖ
    rcases this.isUnit_or_isUnit rfl with (H0 | H0)
    -- ⊢ Associated p ϖ
    · exact (hϖ.not_unit H0).elim
      -- 🎉 no goals
    · rw [add_comm, pow_succ] at H0
      -- ⊢ Associated p ϖ
      exact (hϖ.not_unit (isUnit_of_mul_isUnit_left H0)).elim
      -- 🎉 no goals
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.unique_irreducible DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.unique_irreducible

variable [IsDomain R]

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique factorization domain.
See `DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`. -/
theorem toUniqueFactorizationMonoid : UniqueFactorizationMonoid R :=
  let p := Classical.choose hR
  let spec := Classical.choose_spec hR
  UniqueFactorizationMonoid.of_exists_prime_factors fun x hx => by
    use Multiset.replicate (Classical.choose (spec.2 hx)) p
    -- ⊢ (∀ (b : R), b ∈ Multiset.replicate (choose (_ : ∃ n, Associated (choose hR ^ …
    constructor
    -- ⊢ ∀ (b : R), b ∈ Multiset.replicate (choose (_ : ∃ n, Associated (choose hR ^  …
    · intro q hq
      -- ⊢ Prime q
      have hpq := Multiset.eq_of_mem_replicate hq
      -- ⊢ Prime q
      rw [hpq]
      -- ⊢ Prime p
      refine' ⟨spec.1.ne_zero, spec.1.not_unit, _⟩
      -- ⊢ ∀ (a b : R), p ∣ a * b → p ∣ a ∨ p ∣ b
      intro a b h
      -- ⊢ p ∣ a ∨ p ∣ b
      by_cases ha : a = 0
      -- ⊢ p ∣ a ∨ p ∣ b
      · rw [ha]
        -- ⊢ p ∣ 0 ∨ p ∣ b
        simp only [true_or_iff, dvd_zero]
        -- 🎉 no goals
      obtain ⟨m, u, rfl⟩ := spec.2 ha
      -- ⊢ p ∣ choose hR ^ m * ↑u ∨ p ∣ b
      rw [mul_assoc, mul_left_comm, IsUnit.dvd_mul_left _ _ _ (Units.isUnit _)] at h
      -- ⊢ p ∣ choose hR ^ m * ↑u ∨ p ∣ b
      rw [IsUnit.dvd_mul_right (Units.isUnit _)]
      -- ⊢ p ∣ choose hR ^ m ∨ p ∣ b
      by_cases hm : m = 0
      -- ⊢ p ∣ choose hR ^ m ∨ p ∣ b
      · simp only [hm, one_mul, pow_zero] at h ⊢
        -- ⊢ choose hR ∣ 1 ∨ choose hR ∣ b
        right
        -- ⊢ choose hR ∣ b
        exact h
        -- 🎉 no goals
      left
      -- ⊢ p ∣ choose hR ^ m
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      -- ⊢ p ∣ choose hR ^ Nat.succ m
      rw [pow_succ]
      -- ⊢ p ∣ choose hR * choose hR ^ m
      apply dvd_mul_of_dvd_left dvd_rfl _
      -- 🎉 no goals
    · rw [Multiset.prod_replicate]
      -- ⊢ Associated (p ^ choose (_ : ∃ n, Associated (choose hR ^ n) x)) x
      exact Classical.choose_spec (spec.2 hx)
      -- 🎉 no goals
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.to_unique_factorization_monoid DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

theorem of_ufd_of_unique_irreducible [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    HasUnitMulPowIrreducibleFactorization R := by
  obtain ⟨p, hp⟩ := h₁
  -- ⊢ HasUnitMulPowIrreducibleFactorization R
  refine' ⟨p, hp, _⟩
  -- ⊢ ∀ {x : R}, x ≠ 0 → ∃ n, Associated (p ^ n) x
  intro x hx
  -- ⊢ ∃ n, Associated (p ^ n) x
  cases' WfDvdMonoid.exists_factors x hx with fx hfx
  -- ⊢ ∃ n, Associated (p ^ n) x
  refine' ⟨Multiset.card fx, _⟩
  -- ⊢ Associated (p ^ ↑Multiset.card fx) x
  have H := hfx.2
  -- ⊢ Associated (p ^ ↑Multiset.card fx) x
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  -- ⊢ Associates.mk (p ^ ↑Multiset.card fx) = Associates.mk x
  rw [← H, ← Associates.prod_mk, Associates.mk_pow, ← Multiset.prod_replicate]
  -- ⊢ Multiset.prod (Multiset.replicate (↑Multiset.card fx) (Associates.mk p)) = M …
  congr 1
  -- ⊢ Multiset.replicate (↑Multiset.card fx) (Associates.mk p) = Multiset.map Asso …
  symm
  -- ⊢ Multiset.map Associates.mk fx = Multiset.replicate (↑Multiset.card fx) (Asso …
  rw [Multiset.eq_replicate]
  -- ⊢ ↑Multiset.card (Multiset.map Associates.mk fx) = ↑Multiset.card fx ∧ ∀ (b :  …
  simp only [true_and_iff, and_imp, Multiset.card_map, eq_self_iff_true, Multiset.mem_map,
    exists_imp]
  rintro _ q hq rfl
  -- ⊢ Associates.mk q = Associates.mk p
  rw [Associates.mk_eq_mk_iff_associated]
  -- ⊢ Associated q p
  apply h₂ (hfx.1 _ hq) hp
  -- 🎉 no goals
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible

end HasUnitMulPowIrreducibleFactorization

theorem aux_pid_of_ufd_of_unique_irreducible (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    IsPrincipalIdealRing R := by
  constructor
  -- ⊢ ∀ (S : Ideal R), Submodule.IsPrincipal S
  intro I
  -- ⊢ Submodule.IsPrincipal I
  by_cases I0 : I = ⊥
  -- ⊢ Submodule.IsPrincipal I
  · rw [I0]
    -- ⊢ Submodule.IsPrincipal ⊥
    use 0
    -- ⊢ ⊥ = Submodule.span R {0}
    simp only [Set.singleton_zero, Submodule.span_zero]
    -- 🎉 no goals
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ (0 : R) := I.ne_bot_iff.mp I0
  -- ⊢ Submodule.IsPrincipal I
  obtain ⟨p, _, H⟩ := HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible h₁ h₂
  -- ⊢ Submodule.IsPrincipal I
  have ex : ∃ n : ℕ, p ^ n ∈ I := by
    obtain ⟨n, u, rfl⟩ := H hx0
    refine' ⟨n, _⟩
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hxI
  constructor
  -- ⊢ ∃ a, I = Submodule.span R {a}
  use p ^ Nat.find ex
  -- ⊢ I = Submodule.span R {p ^ Nat.find ex}
  show I = Ideal.span _
  -- ⊢ I = span {p ^ Nat.find ex}
  apply le_antisymm
  -- ⊢ I ≤ span {p ^ Nat.find ex}
  · intro r hr
    -- ⊢ r ∈ span {p ^ Nat.find ex}
    by_cases hr0 : r = 0
    -- ⊢ r ∈ span {p ^ Nat.find ex}
    · simp only [hr0, Submodule.zero_mem]
      -- 🎉 no goals
    obtain ⟨n, u, rfl⟩ := H hr0
    -- ⊢ p ^ n * ↑u ∈ span {p ^ Nat.find ex}
    simp only [mem_span_singleton, Units.isUnit, IsUnit.dvd_mul_right]
    -- ⊢ p ^ Nat.find ex ∣ p ^ n
    apply pow_dvd_pow
    -- ⊢ Nat.find ex ≤ n
    apply Nat.find_min'
    -- ⊢ p ^ n ∈ I
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hr
    -- 🎉 no goals
  · erw [Submodule.span_singleton_le_iff_mem]
    -- ⊢ p ^ Nat.find ex ∈ I
    exact Nat.find_spec ex
    -- 🎉 no goals
#align discrete_valuation_ring.aux_pid_of_ufd_of_unique_irreducible DiscreteValuationRing.aux_pid_of_ufd_of_unique_irreducible

/-- A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
theorem of_ufd_of_unique_irreducible {R : Type u} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    DiscreteValuationRing R := by
  rw [iff_pid_with_one_nonzero_prime]
  -- ⊢ IsPrincipalIdealRing R ∧ ∃! P, P ≠ ⊥ ∧ IsPrime P
  haveI PID : IsPrincipalIdealRing R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂
  -- ⊢ IsPrincipalIdealRing R ∧ ∃! P, P ≠ ⊥ ∧ IsPrime P
  obtain ⟨p, hp⟩ := h₁
  -- ⊢ IsPrincipalIdealRing R ∧ ∃! P, P ≠ ⊥ ∧ IsPrime P
  refine' ⟨PID, ⟨Ideal.span {p}, ⟨_, _⟩, _⟩⟩
  · rw [Submodule.ne_bot_iff]
    -- ⊢ ∃ x, x ∈ span {p} ∧ x ≠ 0
    refine' ⟨p, Ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩
    -- 🎉 no goals
  · rwa [Ideal.span_singleton_prime hp.ne_zero, ← UniqueFactorizationMonoid.irreducible_iff_prime]
    -- 🎉 no goals
  · intro I
    -- ⊢ (fun P => P ≠ ⊥ ∧ IsPrime P) I → I = span {p}
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    -- ⊢ (fun P => P ≠ ⊥ ∧ IsPrime P) (Submodule.span R {Submodule.IsPrincipal.genera …
    rintro ⟨I0, hI⟩
    -- ⊢ Submodule.span R {Submodule.IsPrincipal.generator I} = span {p}
    apply span_singleton_eq_span_singleton.mpr
    -- ⊢ Associated (Submodule.IsPrincipal.generator I) p
    apply h₂ _ hp
    -- ⊢ Irreducible (Submodule.IsPrincipal.generator I)
    erw [Ne.def, span_singleton_eq_bot] at I0
    -- ⊢ Irreducible (Submodule.IsPrincipal.generator I)
    rwa [UniqueFactorizationMonoid.irreducible_iff_prime, ← Ideal.span_singleton_prime I0]
    -- 🎉 no goals
#align discrete_valuation_ring.of_ufd_of_unique_irreducible DiscreteValuationRing.of_ufd_of_unique_irreducible

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
theorem ofHasUnitMulPowIrreducibleFactorization {R : Type u} [CommRing R] [IsDomain R]
    (hR : HasUnitMulPowIrreducibleFactorization R) : DiscreteValuationRing R := by
  letI : UniqueFactorizationMonoid R := hR.toUniqueFactorizationMonoid
  -- ⊢ DiscreteValuationRing R
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible
  -- ⊢ ∃ p, Irreducible p
  obtain ⟨p, hp, H⟩ := hR
  -- ⊢ ∃ p, Irreducible p
  exact ⟨p, hp⟩
  -- 🎉 no goals
#align discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization

section

variable [CommRing R] [IsDomain R] [DiscreteValuationRing R]

variable {R}

theorem associated_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ n : ℕ, Associated x (ϖ ^ n) := by
  have : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  -- ⊢ ∃ n, Associated x (ϖ ^ n)
  cases' WfDvdMonoid.exists_factors x hx with fx hfx
  -- ⊢ ∃ n, Associated x (ϖ ^ n)
  use Multiset.card fx
  -- ⊢ Associated x (ϖ ^ ↑Multiset.card fx)
  have H := hfx.2
  -- ⊢ Associated x (ϖ ^ ↑Multiset.card fx)
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  -- ⊢ Associates.mk x = Associates.mk (ϖ ^ ↑Multiset.card fx)
  rw [← H, ← Associates.prod_mk, Associates.mk_pow, ← Multiset.prod_replicate]
  -- ⊢ Multiset.prod (Multiset.map Associates.mk fx) = Multiset.prod (Multiset.repl …
  congr 1
  -- ⊢ Multiset.map Associates.mk fx = Multiset.replicate (↑Multiset.card fx) (Asso …
  rw [Multiset.eq_replicate]
  -- ⊢ ↑Multiset.card (Multiset.map Associates.mk fx) = ↑Multiset.card fx ∧ ∀ (b :  …
  simp only [true_and_iff, and_imp, Multiset.card_map, eq_self_iff_true, Multiset.mem_map,
    exists_imp]
  rintro _ _ _ rfl
  -- ⊢ Associates.mk x✝ = Associates.mk ϖ
  rw [Associates.mk_eq_mk_iff_associated]
  -- ⊢ Associated x✝ ϖ
  refine' associated_of_irreducible _ _ hirr
  -- ⊢ Irreducible x✝
  apply hfx.1
  -- ⊢ x✝ ∈ fx
  assumption
  -- 🎉 no goals
#align discrete_valuation_ring.associated_pow_irreducible DiscreteValuationRing.associated_pow_irreducible

theorem eq_unit_mul_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ (n : ℕ) (u : Rˣ), x = u * ϖ ^ n := by
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr
  -- ⊢ ∃ n u, x = ↑u * ϖ ^ n
  obtain ⟨u, rfl⟩ := hn.symm
  -- ⊢ ∃ n_1 u_1, ϖ ^ n * ↑u = ↑u_1 * ϖ ^ n_1
  use n, u
  -- ⊢ ϖ ^ n * ↑u = ↑u * ϖ ^ n
  apply mul_comm
  -- 🎉 no goals
#align discrete_valuation_ring.eq_unit_mul_pow_irreducible DiscreteValuationRing.eq_unit_mul_pow_irreducible

open Submodule.IsPrincipal

theorem ideal_eq_span_pow_irreducible {s : Ideal R} (hs : s ≠ ⊥) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ n : ℕ, s = Ideal.span {ϖ ^ n} := by
  have gen_ne_zero : generator s ≠ 0 := by
    rw [Ne.def, ← eq_bot_iff_generator_eq_zero]
    assumption
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩
  -- ⊢ ∃ n, s = span {ϖ ^ n}
  use n
  -- ⊢ s = span {ϖ ^ n}
  have : span _ = _ := Ideal.span_singleton_generator s
  -- ⊢ s = span {ϖ ^ n}
  rw [← this, ← hnu, span_singleton_eq_span_singleton]
  -- ⊢ Associated (generator s) (generator s * ↑u)
  use u
  -- 🎉 no goals
#align discrete_valuation_ring.ideal_eq_span_pow_irreducible DiscreteValuationRing.ideal_eq_span_pow_irreducible

theorem unit_mul_pow_congr_pow {p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ)
    (m n : ℕ) (h : ↑u * p ^ m = v * q ^ n) : m = n := by
  have key : Associated (Multiset.replicate m p).prod (Multiset.replicate n q).prod := by
    rw [Multiset.prod_replicate, Multiset.prod_replicate, Associated]
    refine' ⟨u * v⁻¹, _⟩
    simp only [Units.val_mul]
    rw [mul_left_comm, ← mul_assoc, h, mul_right_comm, Units.mul_inv, one_mul]
  have := by
    refine' Multiset.card_eq_card_of_rel (UniqueFactorizationMonoid.factors_unique _ _ key)
    all_goals
      intro x hx
      obtain rfl := Multiset.eq_of_mem_replicate hx
      assumption
  simpa only [Multiset.card_replicate]
  -- 🎉 no goals
#align discrete_valuation_ring.unit_mul_pow_congr_pow DiscreteValuationRing.unit_mul_pow_congr_pow

theorem unit_mul_pow_congr_unit {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : ℕ)
    (h : ↑u * ϖ ^ m = v * ϖ ^ n) : u = v := by
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h
  -- ⊢ u = v
  rw [← sub_eq_zero] at h
  -- ⊢ u = v
  rw [← sub_mul, mul_eq_zero] at h
  -- ⊢ u = v
  cases' h with h h
  -- ⊢ u = v
  · rw [sub_eq_zero] at h
    -- ⊢ u = v
    exact_mod_cast h
    -- 🎉 no goals
  · apply (hirr.ne_zero (pow_eq_zero h)).elim
    -- 🎉 no goals
#align discrete_valuation_ring.unit_mul_pow_congr_unit DiscreteValuationRing.unit_mul_pow_congr_unit

/-!
## The additive valuation on a DVR
-/
open multiplicity

/-- The `PartENat`-valued additive valuation on a DVR. -/
noncomputable def addVal (R : Type u) [CommRing R] [IsDomain R] [DiscreteValuationRing R] :
    AddValuation R PartENat :=
  addValuation (Classical.choose_spec (exists_prime R))
#align discrete_valuation_ring.add_val DiscreteValuationRing.addVal

theorem addVal_def (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (hr : r = u * ϖ ^ n) :
    addVal R r = n := by
  rw [addVal, addValuation_apply, hr, eq_of_associated_left
      (associated_of_irreducible R hϖ (Classical.choose_spec (exists_prime R)).irreducible),
    eq_of_associated_right (Associated.symm ⟨u, mul_comm _ _⟩),
    multiplicity_pow_self_of_prime (PrincipalIdealRing.irreducible_iff_prime.1 hϖ)]
#align discrete_valuation_ring.add_val_def DiscreteValuationRing.addVal_def

theorem addVal_def' (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    addVal R ((u : R) * ϖ ^ n) = n :=
  addVal_def _ u hϖ n rfl
#align discrete_valuation_ring.add_val_def' DiscreteValuationRing.addVal_def'

--@[simp] Porting note: simp can prove it
theorem addVal_zero : addVal R 0 = ⊤ :=
  (addVal R).map_zero
#align discrete_valuation_ring.add_val_zero DiscreteValuationRing.addVal_zero

--@[simp] Porting note: simp can prove it
theorem addVal_one : addVal R 1 = 0 :=
  (addVal R).map_one
#align discrete_valuation_ring.add_val_one DiscreteValuationRing.addVal_one

@[simp]
theorem addVal_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) : addVal R ϖ = 1 := by
  simpa only [one_mul, eq_self_iff_true, Units.val_one, pow_one, forall_true_left, Nat.cast_one]
    using addVal_def ϖ 1 hϖ 1
#align discrete_valuation_ring.add_val_uniformizer DiscreteValuationRing.addVal_uniformizer

--@[simp] Porting note: simp can prove it
theorem addVal_mul {a b : R} :
    addVal R (a * b) = addVal R a + addVal R b :=
  (addVal R).map_mul _ _
#align discrete_valuation_ring.add_val_mul DiscreteValuationRing.addVal_mul

theorem addVal_pow (a : R) (n : ℕ) : addVal R (a ^ n) = n • addVal R a :=
  (addVal R).map_pow _ _
#align discrete_valuation_ring.add_val_pow DiscreteValuationRing.addVal_pow

nonrec theorem _root_.Irreducible.addVal_pow {ϖ : R} (h : Irreducible ϖ) (n : ℕ) :
    addVal R (ϖ ^ n) = n := by
  rw [addVal_pow, addVal_uniformizer h, nsmul_one]
  -- 🎉 no goals
#align irreducible.add_val_pow Irreducible.addVal_pow

theorem addVal_eq_top_iff {a : R} : addVal R a = ⊤ ↔ a = 0 := by
  have hi := (Classical.choose_spec (exists_prime R)).irreducible
  -- ⊢ ↑(addVal R) a = ⊤ ↔ a = 0
  constructor
  -- ⊢ ↑(addVal R) a = ⊤ → a = 0
  · contrapose
    -- ⊢ ¬a = 0 → ¬↑(addVal R) a = ⊤
    intro h
    -- ⊢ ¬↑(addVal R) a = ⊤
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi
    -- ⊢ ¬↑(addVal R) a = ⊤
    obtain ⟨u, rfl⟩ := ha.symm
    -- ⊢ ¬↑(addVal R) (choose (_ : ∃ ϖ, Prime ϖ) ^ n * ↑u) = ⊤
    rw [mul_comm, addVal_def' u hi n]
    -- ⊢ ¬↑n = ⊤
    exact PartENat.natCast_ne_top _
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ ↑(addVal R) 0 = ⊤
    exact addVal_zero
    -- 🎉 no goals
#align discrete_valuation_ring.add_val_eq_top_iff DiscreteValuationRing.addVal_eq_top_iff

theorem addVal_le_iff_dvd {a b : R} : addVal R a ≤ addVal R b ↔ a ∣ b := by
  have hp := Classical.choose_spec (exists_prime R)
  -- ⊢ ↑(addVal R) a ≤ ↑(addVal R) b ↔ a ∣ b
  constructor <;> intro h
  -- ⊢ ↑(addVal R) a ≤ ↑(addVal R) b → a ∣ b
                  -- ⊢ a ∣ b
                  -- ⊢ ↑(addVal R) a ≤ ↑(addVal R) b
  · by_cases ha0 : a = 0
    -- ⊢ a ∣ b
    · rw [ha0, addVal_zero, top_le_iff, addVal_eq_top_iff] at h
      -- ⊢ a ∣ b
      rw [h]
      -- ⊢ a ∣ 0
      apply dvd_zero
      -- 🎉 no goals
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible
    -- ⊢ a ∣ b
    rw [addVal, addValuation_apply, addValuation_apply, multiplicity_le_multiplicity_iff] at h
    -- ⊢ a ∣ b
    exact ha.dvd.trans (h n ha.symm.dvd)
    -- 🎉 no goals
  · rw [addVal, addValuation_apply, addValuation_apply]
    -- ⊢ multiplicity (choose (_ : ∃ ϖ, Prime ϖ)) a ≤ multiplicity (choose (_ : ∃ ϖ,  …
    exact multiplicity_le_multiplicity_of_dvd_right h
    -- 🎉 no goals
#align discrete_valuation_ring.add_val_le_iff_dvd DiscreteValuationRing.addVal_le_iff_dvd

theorem addVal_add {a b : R} : min (addVal R a) (addVal R b) ≤ addVal R (a + b) :=
  (addVal R).map_add _ _
#align discrete_valuation_ring.add_val_add DiscreteValuationRing.addVal_add

end

instance (R : Type*) [CommRing R] [IsDomain R] [DiscreteValuationRing R] :
    IsHausdorff (maximalIdeal R) R where
  haus' x hx := by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    -- ⊢ x = 0
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow] at hx
    rwa [← addVal_eq_top_iff, PartENat.eq_top_iff_forall_le]
    -- 🎉 no goals

end DiscreteValuationRing
