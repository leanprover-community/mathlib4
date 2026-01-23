/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Pointwise
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Dedekind domains and invertible ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible,
and prove instances such as the unique factorization of ideals.
Further results on the structure of ideals in a Dedekind domain are found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`.

## Main definitions

- `IsDedekindDomainInv` alternatively defines a Dedekind domain as an integral domain where
  every nonzero fractional ideal is invertible.
- `isDedekindDomainInv_iff` shows that this does note depend on the choice of field of
  fractions.

## Main results:

- `isDedekindDomain_iff_isDedekindDomainInv`
- `Ideal.uniqueFactorizationMonoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

@[expose] public section

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

section Inverse

section IsDedekindDomainInv

variable [IsDomain A]
/-- A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `IsDedekindDomain`.
In particular we provide a `CommGroupWithZero` instance,
assuming `IsDedekindDomain A`, which implies `IsDedekindDomainInv`. For **integral** domain,
`IsDedekindDomain`(`Inv`) implies only `Ideal.isCancelMulZero`.
-/
def IsDedekindDomainInv : Prop :=
  ∀ I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1

open FractionalIdeal

variable {R A K}

theorem isDedekindDomainInv_iff [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomainInv A ↔ ∀ I ≠ (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 := by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h]

theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 := by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : IsIdempotentElem I := by
    apply coeToSubmodule_injective
    simp only [coe_mul, adjoinIntegral_coe, I]
    rw [(Algebra.adjoin A {x}).isIdempotentElem_toSubmodule]
  convert congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_iff_isUnit K).mpr hI, mul_assoc, mul_one]

namespace IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K] (h : IsDedekindDomainInv A) {I J : FractionalIdeal A⁰ K}
include h

/-- `IsDedekindDomainInv A` implies that fractional ideals over it form a commutative group with
zero. -/
noncomputable abbrev commGroupWithZero : CommGroupWithZero (FractionalIdeal A⁰ K) where
  inv_zero := inv_zero' _
  mul_inv_cancel := isDedekindDomainInv_iff.mp h
  div_eq_mul_inv I J := by
    obtain rfl | hJ := eq_or_ne J 0
    · simp [inv_zero']
    refine le_antisymm ?_ ((FractionalIdeal.le_div_iff_mul_le hJ).2 ?_)
    · suffices I / J * J ≤ I by
        simpa [mul_assoc, isDedekindDomainInv_iff.mp h _ hJ] using mul_left_mono (a := J⁻¹) this
      simp [FractionalIdeal.mul_le, mem_div_iff_of_ne_zero hJ]
    · rw [mul_assoc, mul_comm _ J, isDedekindDomainInv_iff.mp h _ hJ, mul_one]

@[deprecated mul_inv_cancel₀ (since := "2025-09-09")]
protected lemma mul_inv_eq_one (hI : I ≠ 0) : I * I⁻¹ = 1 := by
  let := h.commGroupWithZero (K := K); simp [*]

@[deprecated inv_mul_cancel₀ (since := "2025-09-09")]
protected lemma inv_mul_eq_one (hI : I ≠ 0) : I⁻¹ * I = 1 := by
  let := h.commGroupWithZero (K := K); simp [*]

theorem isNoetherianRing : IsNoetherianRing A := by
  let := h.commGroupWithZero (K := FractionRing A)
  refine isNoetherianRing_iff.mpr ⟨fun I : Ideal A => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
  exact I.fg_of_isUnit (IsFractionRing.injective A (FractionRing A)) hI.isUnit

theorem integrallyClosed : IsIntegrallyClosed A := by
  let := h.commGroupWithZero (K := FractionRing A)
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr (fun {x hx} => ?_)
  rw [← Set.mem_range, ← Algebra.mem_bot, ← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot,
    Submodule.one_eq_span, ← coe_spanSingleton A⁰ (1 : FractionRing A), spanSingleton_one, ←
    FractionalIdeal.adjoinIntegral_eq_one_of_isUnit x hx (Ne.isUnit _)]
  · exact mem_adjoinIntegral_self A⁰ x hx
  · exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Algebra.adjoin A {x}).one_mem)

open Ring

theorem dimensionLEOne : DimensionLEOne A := by
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  let := h.commGroupWithZero (K := FractionRing A)
  constructor
  rintro P P_ne hP
  refine Ideal.isMaximal_def.mpr ⟨hP.ne_top, fun M hM => ?_⟩
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hM.ne_bot
  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P ≤ P by
    rw [eq_top_iff, ← coeIdeal_le_coeIdeal (FractionRing A), coeIdeal_top]
    calc
      (1 : FractionalIdeal A⁰ (FractionRing A)) = (↑M)⁻¹ * P * ((↑P)⁻¹ * M) := by
        simp [mul_assoc, *]
      _ ≤ P * ((↑P)⁻¹ * M) := by gcongr
      _ = M := by simp [*]
  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebraMap _ _ y` for some `y`.
  intro x hx
  have le_one : (M⁻¹ : FractionalIdeal A⁰ (FractionRing A)) * P ≤ 1 := by
    rw [← inv_mul_cancel₀ M'_ne]; gcongr
  obtain ⟨y, _hy, rfl⟩ := (mem_coeIdeal _).mp (le_one hx)
  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := mul_mem_mul (mem_coeIdeal_of_mem A⁰ hzM) hx
  rw [← map_mul, ← mul_assoc, mul_inv_cancel₀ M'_ne, one_mul] at zy_mem
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coeIdeal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coeIdeal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)

/-- Showing one side of the equivalence between the definitions
`IsDedekindDomainInv` and `IsDedekindDomain` of Dedekind domains. -/
theorem isDedekindDomain : IsDedekindDomain A :=
  { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }

end IsDedekindDomainInv

end IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

theorem one_mem_inv_coe_ideal [IsDomain A] {I : Ideal A} (hI : I ≠ ⊥) :
    (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

/-- Specialization of `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : Ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
theorem exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsField A)
    {I M : Ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧
        ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I := by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).prod ≠ ⊥}
      ⟨Z₀, hZ₀.1, hZ₀.2⟩
  obtain ⟨_, hPZ', hPM⟩ := hM.isPrime.multiset_prod_le.mp (hZI.trans hIM)
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := Multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase PrimeSpectrum.asIdeal (fun _ _ => PrimeSpectrum.ext) P Z
    obtain ⟨hP0, hZP0⟩ : P.asIdeal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).prod ≠ ⊥ := by
      rwa [Ne, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ
    -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
    have hPM' := (P.isPrime.isMaximal hP0).eq_of_le hM.ne_top hPM
    subst hPM'
    -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
    refine ⟨Z.erase P, ?_, ?_⟩
    · convert hZI
      rw [this, Multiset.cons_erase hPZ']
    · refine fun h => h_eraseZ (Z.erase P) ⟨h, ?_⟩ (Multiset.erase_lt.mpr hPZ)
      exact hZP0

namespace FractionalIdeal
variable [IsDedekindDomain A] {I : Ideal A}

open Ideal

lemma not_inv_le_one_of_ne_bot (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ¬(I⁻¹ : FractionalIdeal A⁰ K) ≤ 1 := by
  have hNF : ¬IsField A := fun h ↦ letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M ≠ ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_ ?_) (this hMbot hmax.ne_top hmax) <;>
      simpa only [coeIdeal_ne_zero, coeIdeal_le_coeIdeal]
  have hI0 : ⊥ < I := I.bot_lt_of_maximal hNF
  obtain ⟨⟨a, haI⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt hI0
  replace ha0 : a ≠ 0 := Subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
  have hJI : J ≤ I := I.span_singleton_le_iff_mem.2 haI
  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJI
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := SetLike.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine Set.not_subset.2 ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff ?_).mpr ?_, ?_⟩
  · exact coeIdeal_ne_zero.mpr hI0.ne'
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coeIdeal _).mp hy₀
    rw [mul_comm, ← mul_assoc, ← map_mul]
    have h_yb : y * b ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, map_mul, mul_assoc, mul_inv_cancel₀ hnz_fa, mul_one]
    apply coe_mem_one
  · refine mt (mem_one_iff _).mp ?_
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← map_mul] at h₂_abs
    have := Ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction

theorem mul_inv_cancel_of_le_one (hI0 : I ≠ ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ ≤ 1) :
    I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show a contradiction with `exists_notMem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_le_one
  by_cases hJ0 : J = ⊥
  · subst hJ0
    refine absurd ?_ hI0
    rw [eq_bot_iff, ← coeIdeal_le_coeIdeal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
  by_cases hJ1 : J = ⊤
  · rw [← hJ, hJ1, coeIdeal_top]
  exact (not_inv_le_one_of_ne_bot (K := K) hJ0 hJ1 (hJ ▸ hI)).elim

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
theorem coe_ideal_mul_inv (I : Ideal A) (hI0 : I ≠ ⊥) : I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot, Set.mem_range,
      ← mem_one_iff] at this
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a Noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integralClosure_iff_mem_fg]
  have x_mul_mem : ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), x * b ∈ (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI0)]
    dsimp only at hx
    rw [val_eq_coe, mem_coe, mem_inv_iff hJ0] at hx
    simp only [mul_assoc, mul_comm b] at hx ⊢
    intro y hy
    exact hx _ (mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine ⟨AlgHom.range (Polynomial.aeval x : A[X] →ₐ[A] K),
    isNoetherian_submodule.mp (isNoetherian (I : FractionalIdeal A⁰ K)⁻¹) _ fun y hy => ?_,
    ⟨Polynomial.X, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  clear hi
  induction i with
  | zero => rw [pow_zero]; exact one_mem_inv_coe_ideal hI0
  | succ i ih => rw [pow_succ']; exact x_mul_mem _ ih

noncomputable instance semifield : Semifield (FractionalIdeal A⁰ K) where
  __ := coeIdeal_injective.nontrivial
  __ : CommSemiring (FractionalIdeal A⁰ K) := inferInstance
  __ := IsDedekindDomainInv.commGroupWithZero fun I hI ↦ by
    obtain ⟨a, J, ha, hJ⟩ := exists_eq_spanSingleton_mul (K := FractionRing A) I
    suffices h₂ : I * (spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹) = 1 by
      rw [mul_inv_cancel_iff]
      exact ⟨spanSingleton A⁰ (algebraMap _ _ a) * (J : FractionalIdeal A⁰ _)⁻¹, h₂⟩
    subst hJ
    rw [mul_assoc, mul_left_comm (J : FractionalIdeal A⁰ _), coe_ideal_mul_inv, mul_one,
      spanSingleton_mul_spanSingleton, inv_mul_cancel₀, spanSingleton_one]
    · exact mt ((injective_iff_map_eq_zero (algebraMap A _)).mp (IsFractionRing.injective A _) _) ha
    · exact coeIdeal_ne_zero.mp (right_ne_zero_of_mul hI)
  nnqsmul := _

instance : PosMulStrictMono (FractionalIdeal A⁰ K) := PosMulMono.toPosMulStrictMono
instance : MulPosStrictMono (FractionalIdeal A⁰ K) := MulPosMono.toMulPosStrictMono

instance : PosMulReflectLE (FractionalIdeal A⁰ K) where
  elim I J K hJK := by simpa [I.2.ne'] using mul_right_mono (a := I.1⁻¹) hJK

instance : MulPosReflectLE (FractionalIdeal A⁰ K) where
  elim I J K hJK := by simpa [I.2.ne'] using mul_left_mono (a := I.1⁻¹) hJK

@[deprecated mul_inv_cancel₀ (since := "2025-09-14")]
protected theorem mul_inv_cancel {I : FractionalIdeal A⁰ K} (hne : I ≠ 0) : I * I⁻¹ = 1 :=
  mul_inv_cancel₀ hne

@[deprecated mul_le_mul_iff_left₀ (since := "2025-09-14")]
theorem mul_right_le_iff {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) {I I'} : I * J ≤ I' * J ↔ I ≤ I' :=
  mul_le_mul_iff_left₀ <| pos_iff_ne_zero.2 hJ

@[deprecated mul_le_mul_iff_left₀ (since := "2025-09-14")]
theorem mul_left_le_iff {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) {I I'} : J * I ≤ J * I' ↔ I ≤ I' :=
  mul_le_mul_iff_right₀ <| pos_iff_ne_zero.2 hJ

lemma mul_left_strictMono {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono (· * I) :=
  fun _J _K hJK ↦ mul_lt_mul_of_pos_right hJK <| pos_iff_ne_zero.2 hI

lemma mul_right_strictMono {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono (I * ·) :=
  fun _J _K hJK ↦ mul_lt_mul_of_pos_left hJK <| pos_iff_ne_zero.2 hI

instance [IsDedekindDomain A] : PosMulReflectLE (Ideal A) where
  elim I J K e := by
    dsimp
    rwa [← FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing A),
      ← mul_le_mul_iff_right₀ (α := FractionalIdeal A⁰ (FractionRing A)) (a := I.1)
        (by simpa [pos_iff_ne_zero] using I.2.ne'),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_le_coeIdeal]

@[deprecated div_eq_mul_inv (since := "2025-09-14")]
protected lemma div_eq_mul_inv (I J : FractionalIdeal A⁰ K) : I / J = I * J⁻¹ := div_eq_mul_inv ..

end FractionalIdeal

/-- `IsDedekindDomain` and `IsDedekindDomainInv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem isDedekindDomain_iff_isDedekindDomainInv [IsDomain A] :
    IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun _h _I => mul_inv_cancel₀, fun h => h.isDedekindDomain⟩

end Inverse

section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal Ideal

noncomputable instance Ideal.isCancelMulZero : IsCancelMulZero (Ideal A) :=
  Function.Injective.isCancelMulZero (coeIdealHom A⁰ (FractionRing A)) coeIdeal_injective
    (map_zero _) (map_mul _)

instance Ideal.isDomain : IsDomain (Ideal A) where

instance : PosMulStrictMono (Ideal A) := PosMulMono.toPosMulStrictMono

instance : MulPosStrictMono (Ideal A) := MulPosMono.toMulPosStrictMono

/-- For ideals in a Dedekind domain, to divide is to contain. -/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI, hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J ≤ 1 := by
      rw [← inv_mul_cancel₀ hI']; gcongr
    obtain ⟨H, hH⟩ := le_one_iff_exists_coeIdeal.mp this
    use H
    refine coeIdeal_injective (show (J : FractionalIdeal A⁰ (FractionRing A)) = ↑(I * H) from ?_)
    rw [coeIdeal_mul, hH, ← mul_assoc, mul_inv_cancel₀ hI', one_mul]⟩

theorem Ideal.liesOver_iff_dvd_map [Algebra R A] {p : Ideal R} {P : Ideal A} (hP : P ≠ ⊤)
    [p.IsMaximal] :
    P.LiesOver p ↔ P ∣ Ideal.map (algebraMap R A) p := by
  rw [liesOver_iff, dvd_iff_le, under_def, map_le_iff_le_comap,
    IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

theorem Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_lt h))
      (mt Ideal.dvd_iff_le.mp (not_le_of_gt h))⟩

instance : WfDvdMonoid (Ideal A) where
  wf := by
    have : WellFoundedGT (Ideal A) := inferInstance
    convert this.wf using 3
    exact Ideal.dvdNotUnit_iff_lt

instance Ideal.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Ideal A) :=
  { irreducible_iff_prime := by
      intro P
      exact ⟨fun hirr => ⟨hirr.ne_zero, hirr.not_isUnit, fun I J => by
        have : P.IsMaximal := by
          refine ⟨⟨mt Ideal.isUnit_iff.mpr hirr.not_isUnit, ?_⟩⟩
          intro J hJ
          obtain ⟨_J_ne, H, hunit, P_eq⟩ := Ideal.dvdNotUnit_iff_lt.mpr hJ
          exact Ideal.isUnit_iff.mp ((hirr.isUnit_or_isUnit P_eq).resolve_right hunit)
        rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, SetLike.le_def, SetLike.le_def,
          SetLike.le_def]
        contrapose!
        rintro ⟨⟨x, x_mem, x_notMem⟩, ⟨y, y_mem, y_notMem⟩⟩
        exact
          ⟨x * y, Ideal.mul_mem_mul x_mem y_mem,
            mt this.isPrime.mem_or_mem (not_or_intro x_notMem y_notMem)⟩⟩, Prime.irreducible⟩ }

noncomputable instance Ideal.normalizationMonoid : NormalizationMonoid (Ideal A) := .ofUniqueUnits

end IsDedekindDomain
