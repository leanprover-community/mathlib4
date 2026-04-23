/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Nat.Lattice
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Ramification index

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx p P` is the multiplicity of `P` in `map f p`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`.

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index of `P` over `p`, leaving `p` and `P` implicit.

-/

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramificationIdx` is
defined to be 0.
-/
noncomputable def ramificationIdx : ℕ := sSup {n | map f p ≤ P ^ n}

variable {p P}

theorem ramificationIdx_eq_find [DecidablePred fun n ↦ ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n]
    (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
    ramificationIdx p P = Nat.find h := by
  convert Nat.sSup_def h

theorem ramificationIdx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
    ramificationIdx p P = 0 :=
  dif_neg (by push Not; exact h)

theorem ramificationIdx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx p P = n := by
  classical
  let Q : ℕ → Prop := fun m => ∀ k : ℕ, map f p ≤ P ^ k → k ≤ m
  have : Q n := by
    intro k hk
    refine le_of_not_gt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [ramificationIdx_eq_find ⟨n, this⟩]
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  obtain this' := Nat.find_spec ⟨n, this⟩
  exact h.not_ge (this' _ hle)

theorem ramificationIdx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx p P < n := by
  classical
  rcases n with - | n
  · simp at hgt
  · rw [Nat.lt_succ_iff]
    have : ∀ k, map f p ≤ P ^ k → k ≤ n := by
      refine fun k hk => le_of_not_gt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
    rw [ramificationIdx_eq_find ⟨n, this⟩]
    exact Nat.find_min' ⟨n, this⟩ this

@[simp]
theorem ramificationIdx_bot : ramificationIdx (⊥ : Ideal R) P = 0 :=
  dif_neg <| not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))

@[simp]
theorem ramificationIdx_of_not_le (h : ¬map f p ≤ P) : ramificationIdx p P = 0 :=
  ramificationIdx_spec (by simp) (by simpa using h)

theorem ramificationIdx_bot' (hp : p ≠ ⊥) (hf : Function.Injective f) :
    ramificationIdx p (⊥ : Ideal S) = 0 :=
  ramificationIdx_of_not_le <| le_bot_iff.not.mpr <| (map_eq_bot_iff_of_injective hf).not.mpr hp

theorem ramificationIdx_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e)
    (hnle : ¬map f p ≤ P ^ (e + 1)) : ramificationIdx p P ≠ 0 := by
  rwa [ramificationIdx_spec hle hnle]

theorem le_pow_of_le_ramificationIdx {n : ℕ} (hn : n ≤ ramificationIdx p P) :
    map f p ≤ P ^ n := by
  contrapose! hn
  exact ramificationIdx_lt hn

theorem le_pow_ramificationIdx : map f p ≤ P ^ ramificationIdx p P :=
  le_pow_of_le_ramificationIdx (le_refl _)

theorem le_comap_pow_ramificationIdx : p ≤ comap f (P ^ ramificationIdx p P) :=
  map_le_iff_le_comap.mp le_pow_ramificationIdx

theorem le_comap_of_ramificationIdx_ne_zero (h : ramificationIdx p P ≠ 0) : p ≤ comap f P :=
  Ideal.map_le_iff_le_comap.mp <| le_pow_ramificationIdx.trans <| Ideal.pow_le_self <| h

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

variable (p) in
lemma ramificationIdx_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    ramificationIdx p (P.comap e) = ramificationIdx p P := by
  dsimp only [ramificationIdx]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, Ideal.map_le_iff_le_comap]
  rw [← comap_coe e, ← e.toRingEquiv_toRingHom, comap_coe, ← RingEquiv.symm_symm (e : S ≃+* S₁),
    ← map_comap_of_equiv, ← Ideal.map_pow, map_comap_of_equiv, ← comap_coe (RingEquiv.symm _),
    comap_comap, RingEquiv.symm_symm, e.toRingEquiv_toRingHom, ← e.toAlgHom_toRingHom,
    AlgHom.comp_algebraMap]

variable (p) in
lemma ramificationIdx_map_eq {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁]
    (P : Ideal S) (e : E) :
    ramificationIdx p (P.map e) = ramificationIdx p P := by
  rw [show P.map e = _ from P.map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.ramificationIdx_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

lemma ramificationIdx_ne_one_iff (hp : map f p ≤ P) :
    ramificationIdx p P ≠ 1 ↔ p.map f ≤ P ^ 2 := by
  classical
  by_cases! H : ∀ n : ℕ, ∃ k, p.map f ≤ P ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  rw [Ideal.ramificationIdx_eq_find H]
  constructor
  · intro he
    have : 1 ≤ Nat.find H := Nat.find_spec H 1 (by simpa)
    have := Nat.find_min H (m := 1) (by lia)
    push Not at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    lia

open IsLocalRing in
/-- The converse is true when `S` is a Dedekind domain.
See `Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain`. -/
lemma ramificationIdx_eq_one_of_map_localization
    {p : Ideal R} {P : Ideal S} [P.IsPrime] [IsNoetherianRing S]
    (hpP : map (algebraMap R S) p ≤ P) (hp : P ≠ ⊥) (hp' : P.primeCompl ≤ nonZeroDivisors S)
    (H : p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P)) :
    ramificationIdx p P = 1 := by
  rw [← not_ne_iff (b := 1), Ideal.ramificationIdx_ne_one_iff hpP]
  intro h₂
  replace h₂ := Ideal.map_mono («f» := algebraMap S (Localization.AtPrime P)) h₂
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, H, pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

theorem ramificationIdx_map_self_eq_one [IsDedekindDomain S] (h₁ : map f p ≠ ⊤) (h₂ : map f p ≠ ⊥) :
    ramificationIdx p (map f p) = 1 := by
  refine ramificationIdx_spec (by simp) fun h ↦ ?_
  have : map f p ^ 1 = (map f p) ^ 2 := by
    rw [pow_one]
    exact le_antisymm h <| pow_le_self two_ne_zero
  have := IsMulTorsionFree.pow_right_injective₀ (by rwa [one_eq_top]) h₂ this
  simp_all

variable (p P) in
theorem ramificationIdx_le_ramificationIdx {T : Type*} [CommRing T] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (Q : Ideal T) (hp : p = comap f P)
    (h : ramificationIdx p Q ≠ 0) : ramificationIdx P Q ≤ ramificationIdx p Q := by
  simp_rw [ramificationIdx, Ne] at *
  refine csSup_le_csSup' (h.imp_symm Nat.sSup_of_not_bddAbove) fun n hn ↦ ?_
  simp_rw [hp, IsScalarTower.algebraMap_eq R S T, ← map_map, map_le_iff_le_comap]
  exact comap_mono <| by rwa [← map_le_iff_le_comap]

namespace IsDedekindDomain

variable [IsDedekindDomain S]

theorem ramificationIdx_eq_normalizedFactors_count
    (hp0 : map f p ≠ ⊥) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : ramificationIdx p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  refine ramificationIdx_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
      normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge

theorem ramificationIdx_eq_multiplicity (hp : map f p ≠ ⊥) (hP : P.IsPrime) :
    ramificationIdx p P = multiplicity P (Ideal.map f p) := by
  classical
  by_cases hP₂ : P = ⊥
  · rw [hP₂, ← Ideal.zero_eq_bot, multiplicity_zero_eq_zero_of_ne_zero _ hp]
    exact Ideal.ramificationIdx_of_not_le (mt le_bot_iff.mp hp)
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [ramificationIdx_eq_normalizedFactors_count hp hP hP₂, ← normalize_eq P,
    ← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp, normalize_eq]
  exact irreducible_iff_prime.mpr <| prime_of_isPrime hP₂ hP

theorem ramificationIdx_eq_factors_count
    (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx p P = (factors (map f p)).count P := by
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0,
    factors_eq_normalizedFactors]

theorem ramificationIdx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) :
    ramificationIdx p P ≠ 0 := by
  classical
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hp0 (le_bot_iff.mp le)
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

theorem ramificationIdx_ne_zero_of_liesOver [IsDomain R] [IsTorsionFree R S]
    (P : Ideal S) [hP : P.IsPrime] {p : Ideal R} (hp : p ≠ ⊥) [hPp : P.LiesOver p] :
    ramificationIdx p P ≠ 0 :=
  IsDedekindDomain.ramificationIdx_ne_zero (map_ne_bot_of_ne_bot hp) hP <|
    map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff _ _).mp hPp

open IsLocalRing in
lemma ramificationIdx_eq_one_iff
    {p : Ideal R} {P : Ideal S} [P.IsPrime]
    (hp : P ≠ ⊥) (hpP : p.map (algebraMap R S) ≤ P) :
    ramificationIdx p P = 1 ↔
      p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P) := by
  refine ⟨?_, ramificationIdx_eq_one_of_map_localization hpP hp (primeCompl_le_nonZeroDivisors _)⟩
  let Sₚ := Localization.AtPrime P
  rw [← not_ne_iff (b := 1), ramificationIdx_ne_one_iff hpP, pow_two]
  intro H₁
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr hpP
  have ha' : ¬ a ≤ P := fun h ↦ H₁ (ha.trans_le (Ideal.mul_mono_right h))
  rw [IsScalarTower.algebraMap_eq _ S, ← Ideal.map_map, ha, Ideal.map_mul,
    Localization.AtPrime.map_eq_maximalIdeal]
  convert Ideal.mul_top _
  on_goal 2 => infer_instance
  rw [← not_ne_iff, IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl]
  simpa [primeCompl, Set.disjoint_compl_left_iff_subset]

theorem ramificationIdx_le_ramificationIdx [IsDomain R] [IsTorsionFree R S] {S₀ : Type*}
    [CommRing S₀] [Algebra R S₀] [Algebra S₀ S] [IsScalarTower R S₀ S] (p : Ideal R)
    (P : Ideal S₀) (Q : Ideal S) [Q.LiesOver p] [hP : P.LiesOver p] [Q.IsPrime] (hp : p ≠ ⊥) :
    Ideal.ramificationIdx P Q ≤ Ideal.ramificationIdx p Q :=
  p.ramificationIdx_le_ramificationIdx P Q ((liesOver_iff ..).mp hP) <|
    ramificationIdx_ne_zero_of_liesOver _ hp

theorem emultiplicity_map_eq_zero_of_ne [IsDedekindDomain R] {v : Ideal R}
    {w : Ideal S} {p : Ideal R} (hv : Irreducible v) (hp : Prime p) (hvp : v ≠ p) [w.LiesOver v] :
    emultiplicity w (p.map (algebraMap R S)) = 0 := by
  refine emultiplicity_eq_zero.2 fun h ↦ hvp.symm ?_
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← under_def, ← Ideal.over_def w v] at h
  exact ((isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le (isPrime_of_prime hv.prime).ne_top h

/-- Use the more general result `emultiplicity_map_eq_ramificationIdx_mul`.
This is a helper lemma. -/
private theorem emultiplicity_map_eq_ramificationIdx_mul_of_prime [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {p : Ideal R}
    (hv : Irreducible v) (hp : Prime p) (hw : Irreducible w) (hw_bot : w ≠ ⊥)
    [w.LiesOver v] : emultiplicity w (p.map (algebraMap R S)) =
      v.ramificationIdx w * emultiplicity v p := by
  have hp_bot : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp.ne_zero
  by_cases hvp : v = p
  · simp [hvp, (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self,
      ramificationIdx_eq_normalizedFactors_count hp_bot (isPrime_of_prime hw.prime) hw_bot,
      emultiplicity_eq_count_normalizedFactors hw hp_bot]
  · rw [emultiplicity_eq_zero_of_irreducible_ne hv hp.irreducible hvp, mul_zero,
      emultiplicity_map_eq_zero_of_ne hv hp hvp]

/-- If `v` is an irreducible ideal of `R`, `w` is an irreducible ideal of `S` lying over `v`, and
`I` is an ideal of `R`, then the multiplicity of `w` in `I.map (algebraMap R S)` is given by
the multiplicity of `v` in `I` multiplied by the ramification index of `w` over `v`. -/
theorem emultiplicity_map_eq_ramificationIdx_mul [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {I : Ideal R} (h : I ≠ ⊥)
    (hv : Irreducible v) (hw : Irreducible w) (hw_bot : w ≠ ⊥) [w.LiesOver v] :
    emultiplicity w (I.map (algebraMap R S)) =
      v.ramificationIdx w * emultiplicity v I := by
  induction I using induction_on_prime with
  | h₁ => aesop
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp_rw [Ideal.map_top, emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
      emultiplicity_eq_count_normalizedFactors hv h, ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  | h₃ I p hI hp IH =>
    rw [Ideal.map_mul, emultiplicity_mul hw.prime, emultiplicity_mul hv.prime, IH hI, mul_add,
      emultiplicity_map_eq_ramificationIdx_mul_of_prime hv hp hw hw_bot]

end IsDedekindDomain

end DecEq

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Let `T / S / R` be a tower of algebras, `p, P, Q` be ideals in `R, S, T` respectively,
  and `P` and `Q` are prime. If `P = Q ∩ S`, then `e (Q | p) = e (P | p) * e (Q | P)`. -/
theorem ramificationIdx_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm : Q.IsPrime]
    (hg0 : map (algebraMap S T) P ≠ ⊥)
    (hfg : map (algebraMap R T) p ≠ ⊥) (hg : map (algebraMap S T) P ≤ Q) :
    ramificationIdx p Q =
    ramificationIdx p P * ramificationIdx P Q := by
  classical
  have hf0 : map (algebraMap R S) p ≠ ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S T, ← map_map] at hfg
    exact ne_bot_of_map_ne_bot hfg
  have hp0 : P ≠ ⊥ := ne_bot_of_map_ne_bot hg0
  have hq0 : Q ≠ ⊥ := ne_bot_of_le_ne_bot hg0 hg
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpm
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hf0 hpm hp0,
    IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hg0 hqm hq0,
    IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hfg hqm hq0,
    IsScalarTower.algebraMap_eq R S T, ← map_map]
  rcases eq_prime_pow_mul_coprime hf0 P with ⟨I, hcp, heq⟩
  have hcp : ⊤ = map (algebraMap S T) P ⊔ map (algebraMap S T) I := by rw [← map_sup, hcp, map_top]
  have hntq : ¬ ⊤ ≤ Q := fun ht ↦ IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, Ideal.map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) <| by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, bot_le, sup_of_le_left] at hcp
    exact hntq (hcp.trans_le hg), Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul]
  exact add_eq_left.mpr <| Decidable.byContradiction fun h ↦ hntq <| hcp.trans_le <|
    sup_le hg <| le_of_dvd <| dvd_of_mem_normalizedFactors <| Multiset.count_ne_zero.mp h

@[deprecated (since := "2026-03-25")] alias ramificationIdx_tower := ramificationIdx_algebra_tower

theorem ramificationIdx_algebra_tower' [IsDedekindDomain S] [IsDedekindDomain T] [IsDomain R]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree S T] (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    ramificationIdx p Q =
      ramificationIdx p P * ramificationIdx P Q := by
  obtain rfl | hp := eq_or_ne p ⊥
  · simp
  have : P.IsPrime := isPrime_of_liesOver Q P
  have : Module.IsTorsionFree R T := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦ ?_
    rwa [algebra_compatible_smul S, smul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at h
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  exact ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
    <| map_le_iff_le_comap.mpr <| le_of_eq <| over_def Q P

end tower

end Ideal
