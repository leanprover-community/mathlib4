/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Valuation.PrimeMultiplicity
import Mathlib.RingTheory.AdicCompletion.Basic

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


open scoped Classical

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
  refine ⟨h2, ?_⟩
  intro a b hab
  by_contra! h
  obtain ⟨ha : a ∈ maximalIdeal R, hb : b ∈ maximalIdeal R⟩ := h
  rw [h, mem_span_singleton'] at ha hb
  rcases ha with ⟨a, rfl⟩
  rcases hb with ⟨b, rfl⟩
  rw [show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)) by ring] at hab
  apply hϖ
  apply eq_zero_of_mul_eq_self_right _ hab.symm
  exact fun hh => h2 (isUnit_of_dvd_one ⟨_, hh.symm⟩)
#align discrete_valuation_ring.irreducible_of_span_eq_maximal_ideal DiscreteValuationRing.irreducible_of_span_eq_maximalIdeal

/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of `R`. -/
theorem irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ} :=
  ⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,
    fun h => irreducible_of_span_eq_maximalIdeal ϖ
      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩
#align discrete_valuation_ring.irreducible_iff_uniformizer DiscreteValuationRing.irreducible_iff_uniformizer

theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :
    maximalIdeal R = Ideal.span {ϖ} :=
  (irreducible_iff_uniformizer _).mp h
#align irreducible.maximal_ideal_eq Irreducible.maximalIdeal_eq

variable (R)

/-- Uniformizers exist in a DVR. -/
theorem exists_irreducible : ∃ ϖ : R, Irreducible ϖ := by
  simp_rw [irreducible_iff_uniformizer]
  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal
#align discrete_valuation_ring.exists_irreducible DiscreteValuationRing.exists_irreducible

/-- Uniformizers exist in a DVR. -/
theorem exists_prime : ∃ ϖ : R, Prime ϖ :=
  (exists_irreducible R).imp fun _ => irreducible_iff_prime.1
#align discrete_valuation_ring.exists_prime DiscreteValuationRing.exists_prime

/-- An integral domain is a DVR iff it's a PID with a unique non-zero prime ideal. -/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] :
    DiscreteValuationRing R ↔ IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ IsPrime P := by
  constructor
  · intro RDVR
    rcases id RDVR with ⟨Rlocal⟩
    constructor
    · assumption
    use LocalRing.maximalIdeal R
    constructor
    · exact ⟨Rlocal, inferInstance⟩
    · rintro Q ⟨hQ1, hQ2⟩
      obtain ⟨q, rfl⟩ := (IsPrincipalIdealRing.principal Q).1
      have hq : q ≠ 0 := by
        rintro rfl
        apply hQ1
        simp
      erw [span_singleton_prime hq] at hQ2
      replace hQ2 := hQ2.irreducible
      rw [irreducible_iff_uniformizer] at hQ2
      exact hQ2.symm
  · rintro ⟨RPID, Punique⟩
    haveI : LocalRing R := LocalRing.of_unique_nonzero_prime Punique
    refine { not_a_field' := ?_ }
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, _⟩
    have hPM : P ≤ maximalIdeal R := le_maximalIdeal hP2.1
    intro h
    rw [h, le_bot_iff] at hPM
    exact hP1 hPM
#align discrete_valuation_ring.iff_pid_with_one_nonzero_prime DiscreteValuationRing.iff_pid_with_one_nonzero_prime

theorem associated_of_irreducible {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b := by
  rw [irreducible_iff_uniformizer] at ha hb
  rw [← span_singleton_eq_span_singleton, ← ha, hb]
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
  suffices ∀ {p : R} (_ : Irreducible p), Associated p ϖ by
    apply Associated.trans (this hp) (this hq).symm
  clear hp hq p q
  intro p hp
  obtain ⟨n, hn⟩ := hR hp.ne_zero
  have : Irreducible (ϖ ^ n) := hn.symm.irreducible hp
  rcases lt_trichotomy n 1 with (H | rfl | H)
  · obtain rfl : n = 0 := by
      clear hn this
      revert H n
      decide
    simp [not_irreducible_one, pow_zero] at this
  · simpa only [pow_one] using hn.symm
  · obtain ⟨n, rfl⟩ : ∃ k, n = 1 + k + 1 := Nat.exists_eq_add_of_lt H
    rw [pow_succ'] at this
    rcases this.isUnit_or_isUnit rfl with (H0 | H0)
    · exact (hϖ.not_unit H0).elim
    · rw [add_comm, pow_succ'] at H0
      exact (hϖ.not_unit (isUnit_of_mul_isUnit_left H0)).elim
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
    constructor
    · intro q hq
      have hpq := Multiset.eq_of_mem_replicate hq
      rw [hpq]
      refine ⟨spec.1.ne_zero, spec.1.not_unit, ?_⟩
      intro a b h
      by_cases ha : a = 0
      · rw [ha]
        simp only [true_or_iff, dvd_zero]
      obtain ⟨m, u, rfl⟩ := spec.2 ha
      rw [mul_assoc, mul_left_comm, Units.dvd_mul_left] at h
      rw [Units.dvd_mul_right]
      by_cases hm : m = 0
      · simp only [hm, one_mul, pow_zero] at h ⊢
        right
        exact h
      left
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [pow_succ']
      apply dvd_mul_of_dvd_left dvd_rfl _
    · rw [Multiset.prod_replicate]
      exact Classical.choose_spec (spec.2 hx)
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.to_unique_factorization_monoid DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

theorem of_ufd_of_unique_irreducible [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    HasUnitMulPowIrreducibleFactorization R := by
  obtain ⟨p, hp⟩ := h₁
  refine ⟨p, hp, ?_⟩
  intro x hx
  cases' WfDvdMonoid.exists_factors x hx with fx hfx
  refine ⟨Multiset.card fx, ?_⟩
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H, ← Associates.prod_mk, Associates.mk_pow, ← Multiset.prod_replicate]
  congr 1
  symm
  rw [Multiset.eq_replicate]
  simp only [true_and_iff, and_imp, Multiset.card_map, eq_self_iff_true, Multiset.mem_map,
    exists_imp]
  rintro _ q hq rfl
  rw [Associates.mk_eq_mk_iff_associated]
  apply h₂ (hfx.1 _ hq) hp
#align discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible DiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible

end HasUnitMulPowIrreducibleFactorization

theorem aux_pid_of_ufd_of_unique_irreducible (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    IsPrincipalIdealRing R := by
  constructor
  intro I
  by_cases I0 : I = ⊥
  · rw [I0]
    use 0
    simp only [Set.singleton_zero, Submodule.span_zero]
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ (0 : R) := I.ne_bot_iff.mp I0
  obtain ⟨p, _, H⟩ := HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible h₁ h₂
  have ex : ∃ n : ℕ, p ^ n ∈ I := by
    obtain ⟨n, u, rfl⟩ := H hx0
    refine ⟨n, ?_⟩
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hxI
  constructor
  use p ^ Nat.find ex
  show I = Ideal.span _
  apply le_antisymm
  · intro r hr
    by_cases hr0 : r = 0
    · simp only [hr0, Submodule.zero_mem]
    obtain ⟨n, u, rfl⟩ := H hr0
    simp only [mem_span_singleton, Units.isUnit, IsUnit.dvd_mul_right]
    apply pow_dvd_pow
    apply Nat.find_min'
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hr
  · erw [Submodule.span_singleton_le_iff_mem]
    exact Nat.find_spec ex
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
  haveI PID : IsPrincipalIdealRing R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂
  obtain ⟨p, hp⟩ := h₁
  refine ⟨PID, ⟨Ideal.span {p}, ⟨?_, ?_⟩, ?_⟩⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨p, Ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩
  · rwa [Ideal.span_singleton_prime hp.ne_zero, ← UniqueFactorizationMonoid.irreducible_iff_prime]
  · intro I
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    rintro ⟨I0, hI⟩
    apply span_singleton_eq_span_singleton.mpr
    apply h₂ _ hp
    erw [Ne, span_singleton_eq_bot] at I0
    rwa [UniqueFactorizationMonoid.irreducible_iff_prime, ← Ideal.span_singleton_prime I0]
#align discrete_valuation_ring.of_ufd_of_unique_irreducible DiscreteValuationRing.of_ufd_of_unique_irreducible

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
theorem ofHasUnitMulPowIrreducibleFactorization {R : Type u} [CommRing R] [IsDomain R]
    (hR : HasUnitMulPowIrreducibleFactorization R) : DiscreteValuationRing R := by
  letI : UniqueFactorizationMonoid R := hR.toUniqueFactorizationMonoid
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible
  obtain ⟨p, hp, H⟩ := hR
  exact ⟨p, hp⟩
#align discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization

section

variable [CommRing R] [IsDomain R] [DiscreteValuationRing R]
variable {R}

theorem associated_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ n : ℕ, Associated x (ϖ ^ n) := by
  have : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  cases' WfDvdMonoid.exists_factors x hx with fx hfx
  use Multiset.card fx
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H, ← Associates.prod_mk, Associates.mk_pow, ← Multiset.prod_replicate]
  congr 1
  rw [Multiset.eq_replicate]
  simp only [true_and_iff, and_imp, Multiset.card_map, eq_self_iff_true, Multiset.mem_map,
    exists_imp]
  rintro _ _ _ rfl
  rw [Associates.mk_eq_mk_iff_associated]
  refine associated_of_irreducible _ ?_ hirr
  apply hfx.1
  assumption
#align discrete_valuation_ring.associated_pow_irreducible DiscreteValuationRing.associated_pow_irreducible

theorem eq_unit_mul_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ (n : ℕ) (u : Rˣ), x = u * ϖ ^ n := by
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr
  obtain ⟨u, rfl⟩ := hn.symm
  use n, u
  apply mul_comm
#align discrete_valuation_ring.eq_unit_mul_pow_irreducible DiscreteValuationRing.eq_unit_mul_pow_irreducible

open Submodule.IsPrincipal

theorem ideal_eq_span_pow_irreducible {s : Ideal R} (hs : s ≠ ⊥) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ n : ℕ, s = Ideal.span {ϖ ^ n} := by
  have gen_ne_zero : generator s ≠ 0 := by
    rw [Ne, ← eq_bot_iff_generator_eq_zero]
    assumption
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩
  use n
  have : span _ = _ := Ideal.span_singleton_generator s
  rw [← this, ← hnu, span_singleton_eq_span_singleton]
  use u
#align discrete_valuation_ring.ideal_eq_span_pow_irreducible DiscreteValuationRing.ideal_eq_span_pow_irreducible

theorem unit_mul_pow_congr_pow {p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ)
    (m n : ℕ) (h : ↑u * p ^ m = v * q ^ n) : m = n := by
  have key : Associated (Multiset.replicate m p).prod (Multiset.replicate n q).prod := by
    rw [Multiset.prod_replicate, Multiset.prod_replicate, Associated]
    refine ⟨u * v⁻¹, ?_⟩
    simp only [Units.val_mul]
    rw [mul_left_comm, ← mul_assoc, h, mul_right_comm, Units.mul_inv, one_mul]
  have := by
    refine Multiset.card_eq_card_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ key)
    all_goals
      intro x hx
      obtain rfl := Multiset.eq_of_mem_replicate hx
      assumption
  simpa only [Multiset.card_replicate]
#align discrete_valuation_ring.unit_mul_pow_congr_pow DiscreteValuationRing.unit_mul_pow_congr_pow

theorem unit_mul_pow_congr_unit {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : ℕ)
    (h : ↑u * ϖ ^ m = v * ϖ ^ n) : u = v := by
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h
  rw [← sub_eq_zero] at h
  rw [← sub_mul, mul_eq_zero] at h
  cases' h with h h
  · rw [sub_eq_zero] at h
    exact mod_cast h
  · apply (hirr.ne_zero (pow_eq_zero h)).elim
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
    multiplicity_pow_self_of_prime (irreducible_iff_prime.1 hϖ)]
#align discrete_valuation_ring.add_val_def DiscreteValuationRing.addVal_def

theorem addVal_def' (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    addVal R ((u : R) * ϖ ^ n) = n :=
  addVal_def _ u hϖ n rfl
#align discrete_valuation_ring.add_val_def' DiscreteValuationRing.addVal_def'

--@[simp] Porting note (#10618): simp can prove it
theorem addVal_zero : addVal R 0 = ⊤ :=
  (addVal R).map_zero
#align discrete_valuation_ring.add_val_zero DiscreteValuationRing.addVal_zero

--@[simp] Porting note (#10618): simp can prove it
theorem addVal_one : addVal R 1 = 0 :=
  (addVal R).map_one
#align discrete_valuation_ring.add_val_one DiscreteValuationRing.addVal_one

@[simp]
theorem addVal_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) : addVal R ϖ = 1 := by
  simpa only [one_mul, eq_self_iff_true, Units.val_one, pow_one, forall_true_left, Nat.cast_one]
    using addVal_def ϖ 1 hϖ 1
#align discrete_valuation_ring.add_val_uniformizer DiscreteValuationRing.addVal_uniformizer

--@[simp] Porting note (#10618): simp can prove it
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
#align irreducible.add_val_pow Irreducible.addVal_pow

theorem addVal_eq_top_iff {a : R} : addVal R a = ⊤ ↔ a = 0 := by
  have hi := (Classical.choose_spec (exists_prime R)).irreducible
  constructor
  · contrapose
    intro h
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi
    obtain ⟨u, rfl⟩ := ha.symm
    rw [mul_comm, addVal_def' u hi n]
    exact PartENat.natCast_ne_top _
  · rintro rfl
    exact addVal_zero
#align discrete_valuation_ring.add_val_eq_top_iff DiscreteValuationRing.addVal_eq_top_iff

theorem addVal_le_iff_dvd {a b : R} : addVal R a ≤ addVal R b ↔ a ∣ b := by
  have hp := Classical.choose_spec (exists_prime R)
  constructor <;> intro h
  · by_cases ha0 : a = 0
    · rw [ha0, addVal_zero, top_le_iff, addVal_eq_top_iff] at h
      rw [h]
      apply dvd_zero
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible
    rw [addVal, addValuation_apply, addValuation_apply, multiplicity_le_multiplicity_iff] at h
    exact ha.dvd.trans (h n ha.symm.dvd)
  · rw [addVal, addValuation_apply, addValuation_apply]
    exact multiplicity_le_multiplicity_of_dvd_right h
#align discrete_valuation_ring.add_val_le_iff_dvd DiscreteValuationRing.addVal_le_iff_dvd

theorem addVal_add {a b : R} : min (addVal R a) (addVal R b) ≤ addVal R (a + b) :=
  (addVal R).map_add _ _
#align discrete_valuation_ring.add_val_add DiscreteValuationRing.addVal_add

end

instance (R : Type*) [CommRing R] [IsDomain R] [DiscreteValuationRing R] :
    IsHausdorff (maximalIdeal R) R where
  haus' x hx := by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow] at hx
    rwa [← addVal_eq_top_iff, PartENat.eq_top_iff_forall_le]

end DiscreteValuationRing
