/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `Ideal.inertiaDeg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Main results

The main theorem `Ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index and `f` for the inertia degree of `P` over `p`,
leaving `p` and `P` implicit.

-/


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] (f : R →+* S)
variable (p : Ideal R) (P : Ideal S)

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

variable {f p P}

theorem ramificationIdx_eq_find [DecidablePred fun n ↦ ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n]
    (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
    ramificationIdx f p P = Nat.find h := by
  convert Nat.sSup_def h

theorem ramificationIdx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
    ramificationIdx f p P = 0 :=
  dif_neg (by push_neg; exact h)

theorem ramificationIdx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx f p P = n := by
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

theorem ramificationIdx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx f p P < n := by
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
theorem ramificationIdx_bot : ramificationIdx f ⊥ P = 0 :=
  dif_neg <| not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))

@[simp]
theorem ramificationIdx_of_not_le (h : ¬map f p ≤ P) : ramificationIdx f p P = 0 :=
  ramificationIdx_spec (by simp) (by simpa using h)

theorem ramificationIdx_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e)
    (hnle : ¬map f p ≤ P ^ (e + 1)) : ramificationIdx f p P ≠ 0 := by
  rwa [ramificationIdx_spec hle hnle]

theorem le_pow_of_le_ramificationIdx {n : ℕ} (hn : n ≤ ramificationIdx f p P) :
    map f p ≤ P ^ n := by
  contrapose! hn
  exact ramificationIdx_lt hn

theorem le_pow_ramificationIdx : map f p ≤ P ^ ramificationIdx f p P :=
  le_pow_of_le_ramificationIdx (le_refl _)

theorem le_comap_pow_ramificationIdx : p ≤ comap f (P ^ ramificationIdx f p P) :=
  map_le_iff_le_comap.mp le_pow_ramificationIdx

theorem le_comap_of_ramificationIdx_ne_zero (h : ramificationIdx f p P ≠ 0) : p ≤ comap f P :=
  Ideal.map_le_iff_le_comap.mp <| le_pow_ramificationIdx.trans <| Ideal.pow_le_self <| h

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

variable (p) in
lemma ramificationIdx_comap_eq [Algebra R S] (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    ramificationIdx (algebraMap R S) p (P.comap e) = ramificationIdx (algebraMap R S₁) p P := by
  dsimp only [ramificationIdx]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, Ideal.map_le_iff_le_comap]
  rw [← comap_coe e, ← e.toRingEquiv_toRingHom, comap_coe, ← RingEquiv.symm_symm (e : S ≃+* S₁),
    ← map_comap_of_equiv, ← Ideal.map_pow, map_comap_of_equiv, ← comap_coe (RingEquiv.symm _),
    comap_comap, RingEquiv.symm_symm, e.toRingEquiv_toRingHom, ← e.toAlgHom_toRingHom,
    AlgHom.comp_algebraMap]

variable (p) in
lemma ramificationIdx_map_eq [Algebra R S] {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁]
    (P : Ideal S) (e : E) :
    ramificationIdx (algebraMap R S₁) p (P.map e) = ramificationIdx (algebraMap R S) p P := by
  rw [show P.map e = _ from P.map_comap_of_equiv (e : S ≃+* S₁)]
  exact p.ramificationIdx_comap_eq (e : S ≃ₐ[R] S₁).symm P

lemma ramificationIdx_ne_one_iff (hp : map f p ≤ P) :
    ramificationIdx f p P ≠ 1 ↔ p.map f ≤ P ^ 2 := by
  classical
  by_cases H : ∀ n : ℕ, ∃ k, p.map f ≤ P ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  push_neg at H
  rw [Ideal.ramificationIdx_eq_find H]
  constructor
  · intro he
    have : 1 ≤ Nat.find H := Nat.find_spec H 1 (by simpa)
    have := Nat.find_min H (m := 1) (by omega)
    push_neg at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    omega

open IsLocalRing in
/-- The converse is true when `S` is a Dedekind domain.
See `Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain`. -/
lemma ramificationIdx_eq_one_of_map_localization
    [Algebra R S] {p : Ideal R} {P : Ideal S} [P.IsPrime] [IsNoetherianRing S]
    (hpP : map (algebraMap R S) p ≤ P) (hp : P ≠ ⊥) (hp' : P.primeCompl ≤ nonZeroDivisors S)
    (H : p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P)) :
    ramificationIdx (algebraMap R S) p P = 1 := by
  rw [← not_ne_iff (b := 1), Ideal.ramificationIdx_ne_one_iff hpP]
  intro h₂
  replace h₂ := Ideal.map_mono (f := algebraMap S (Localization.AtPrime P)) h₂
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, H, pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

namespace IsDedekindDomain

variable [IsDedekindDomain S]

theorem ramificationIdx_eq_normalizedFactors_count [DecidableEq (Ideal S)]
    (hp0 : map f p ≠ ⊥) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : ramificationIdx f p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  refine ramificationIdx_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
      normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge

theorem ramificationIdx_eq_multiplicity (hp : map f p ≠ ⊥) (hP : P.IsPrime) :
    ramificationIdx f p P = multiplicity P (Ideal.map f p) := by
  classical
  by_cases hP₂ : P = ⊥
  · rw [hP₂, ← Ideal.zero_eq_bot, multiplicity_zero_eq_zero_of_ne_zero _ hp]
    exact Ideal.ramificationIdx_of_not_le (mt le_bot_iff.mp hp)
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [ramificationIdx_eq_normalizedFactors_count hp hP hP₂, ← normalize_eq P,
    ← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp, normalize_eq]
  exact irreducible_iff_prime.mpr <| prime_of_isPrime hP₂ hP

theorem ramificationIdx_eq_factors_count [DecidableEq (Ideal S)]
    (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (factors (map f p)).count P := by
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0,
    factors_eq_normalizedFactors]

theorem ramificationIdx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) :
    ramificationIdx f p P ≠ 0 := by
  classical
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hp0 (le_bot_iff.mp le)
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

theorem ramificationIdx_ne_zero_of_liesOver [Algebra R S] [NoZeroSMulDivisors R S]
    (P : Ideal S) [hP : P.IsPrime] {p : Ideal R} (hp : p ≠ ⊥) [hPp : P.LiesOver p] :
    ramificationIdx (algebraMap R S) p P ≠ 0 :=
  IsDedekindDomain.ramificationIdx_ne_zero (map_ne_bot_of_ne_bot hp) hP <|
    map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff _ _).mp hPp

open IsLocalRing in
lemma ramificationIdx_eq_one_iff
    [Algebra R S] {p : Ideal R} {P : Ideal S} [P.IsPrime]
    (hp : P ≠ ⊥) (hpP : p.map (algebraMap R S) ≤ P) :
    ramificationIdx (algebraMap R S) p P = 1 ↔
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

end IsDedekindDomain

variable (f p P) [Algebra R S]

local notation "f" => algebraMap R S

open Classical in
/-- The inertia degree of `P : Ideal S` lying over `p : Ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertiaDeg_algebraMap` for the common case where `f = algebraMap R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertiaDeg : ℕ :=
  if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
theorem inertiaDeg_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg p P = 0 := by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top

@[simp]
theorem inertiaDeg_algebraMap [P.LiesOver p] [p.IsMaximal] :
    inertiaDeg p P = finrank (R ⧸ p) (S ⧸ P) := by
  nontriviality S ⧸ P using inertiaDeg_of_subsingleton, finrank_zero_of_subsingleton
  rw [inertiaDeg, dif_pos (over_def P p).symm]

theorem inertiaDeg_pos [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg p P :=
  haveI : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg_algebraMap p P).symm

theorem inertiaDeg_ne_zero [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : inertiaDeg p P ≠ 0 :=
  (Nat.ne_of_lt (inertiaDeg_pos p P)).symm

lemma inertiaDeg_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) [p.IsMaximal] :
    inertiaDeg p (P.comap e) = inertiaDeg p P := by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e, comap_comap, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
    exact (Quotient.algEquivOfEqComap p e rfl).toLinearEquiv.finrank_eq
  · rw [inertiaDeg, dif_neg (fun eq => h ⟨(he.mp eq).symm⟩)]
    rw [inertiaDeg, dif_neg (fun eq => h ⟨eq.symm⟩)]

lemma inertiaDeg_map_eq [p.IsMaximal] (P : Ideal S)
    {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁] (e : E) :
    inertiaDeg p (P.map e) = inertiaDeg p P := by
  rw [show P.map e = _ from map_comap_of_equiv (e : S ≃+* S₁)]
  exact p.inertiaDeg_comap_eq (e : S ≃ₐ[R] S₁).symm P

end DecEq


section absNorm

/-- The absolute norm of an ideal `P` above a rational prime `p` is
`|p| ^ ((span {p}).inertiaDeg P)`.
See `absNorm_eq_pow_inertiaDeg'` for a version with `p` of type `ℕ`. -/
lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℤ}
    (P : Ideal R) [P.LiesOver (span {p})] (hp : Prime p) :
    absNorm P = p.natAbs ^ ((span {p}).inertiaDeg P) := by
  have : (span {p}).IsMaximal :=
    (isPrime_of_prime (prime_span_singleton_iff.mpr hp)).isMaximal (by simp [hp.ne_zero])
  have h : Module.Finite (ℤ ⧸ span {p}) (R ⧸ P) := module_finite_of_liesOver P (span {p})
  let _ : Field (ℤ ⧸ span {p}) := Quotient.field (span {p})
  rw [inertiaDeg_algebraMap, absNorm_apply, Submodule.cardQuot_apply,
    Module.natCard_eq_pow_finrank (K := ℤ ⧸ span {p})]
  simp [Nat.card_congr (Int.quotientSpanEquivZMod p).toEquiv]

/-- The absolute norm of an ideal `P` above a rational (positive) prime `p` is
`p ^ ((span {p}).inertiaDeg P)`.
See `absNorm_eq_pow_inertiaDeg` for a version with `p` of type `ℤ`. -/
lemma absNorm_eq_pow_inertiaDeg' [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℕ}
    (P : Ideal R) [P.LiesOver (span {(p : ℤ)})] (hp : p.Prime) :
    absNorm P = p ^ ((span {(p : ℤ)}).inertiaDeg P) :=
  absNorm_eq_pow_inertiaDeg P ( Nat.prime_iff_prime_int.mp hp)

end absNorm
section FinrankQuotientMap

open scoped nonZeroDivisors

variable [Algebra R S]
variable {K : Type*} [Field K] [Algebra R K]
variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]
variable {V V' V'' : Type*}
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V']
variable [AddCommGroup V''] [Module R V'']
variable (K)

open scoped Matrix

variable {K} in
/-- If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `K`-space.

Here,
* `p` is an ideal of `R` such that `R / p` is nontrivial
* `K` is a field that has an embedding of `R` (in particular we can take `K = Frac(R)`)
* `L` is a field extension of `K`
* `S` is the integral closure of `R` in `L`

More precisely, we avoid quotients in this statement and instead require that `b ∪ pS` spans `S`.
-/
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [Module.Finite R S]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Algebra.IsAlgebraic R S]
    [NoZeroSMulDivisors R K] (hp : p ≠ ⊤) (b : Set S)
    (hb' : Submodule.span R b ⊔ (p.map (algebraMap R S)).restrictScalars R = ⊤) :
    Submodule.span K (algebraMap S L '' b) = ⊤ := by
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective R K)
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  let M : Submodule R S := Submodule.span R b
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  obtain ⟨n, a, ha⟩ := @Module.Finite.exists_fin R (S ⧸ M) _ _ _ _
  -- Because the image of `p` in `S / M` is `⊤`,
  have smul_top_eq : p • (⊤ : Submodule R (S ⧸ M)) = ⊤ := by
    calc
      p • ⊤ = Submodule.map M.mkQ (p • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, M.range_mkQ]
      _ = ⊤ := by rw [Ideal.smul_top_eq_map, (Submodule.map_mkQ_eq_top M _).mpr hb']
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : S ⧸ M, ∃ a' : Fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x := by
    intro x
    obtain ⟨a'', ha'', hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1
      (by { rw [ha, smul_top_eq]; exact Submodule.mem_top } :
        x ∈ p • Submodule.span R (Set.range a))
    · refine ⟨fun i => a'' i, fun i => ha'' _, ?_⟩
      rw [← hx, Finsupp.sum_fintype]
      exact fun _ => zero_smul _ _
  choose A' hA'p hA' using fun i => exists_sum (a i)
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ (M = span R b)`,
  let A : Matrix (Fin n) (Fin n) R := Matrix.of A' - 1
  let B := A.adjugate
  have A_smul : ∀ i, ∑ j, A i j • a j = 0 := by
    intros
    simp [A, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, sub_smul,
      Finset.sum_sub_distrib, hA', sub_self]
  -- since `span S {det A} / M = 0`.
  have d_smul : ∀ i, A.det • a i = 0 := by
    intro i
    calc
      A.det • a i = ∑ j, (B * A) i j • a j := ?_
      _ = ∑ k, B i k • ∑ j, A k j • a j := ?_
      _ = 0 := Finset.sum_eq_zero fun k _ => ?_
    · simp only [B, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    · rw [A_smul, smul_zero]
  -- In the rings of integers we have the desired inclusion.
  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul, mul_comm, ← Algebra.smul_def] at hx ⊢
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (Submodule.Quotient.mk x')
    rw [← quot_x_eq, Finset.smul_sum]
    conv =>
      lhs; congr; next => skip
      intro x; rw [smul_comm A.det, d_smul, smul_zero]
    exact Finset.sum_const_zero
  refine top_le_iff.mp
      (calc
        ⊤ = (Ideal.span {algebraMap R L A.det}).restrictScalars K := ?_
        _ ≤ Submodule.span K (algebraMap S L '' b) := ?_)
  -- Because `det A ≠ 0`, we have `span L {det A} = ⊤`.
  · rw [eq_comm, Submodule.restrictScalars_eq_top_iff, Ideal.span_singleton_eq_top]
    refine IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R L) hRL).mpr ?_)
    refine ne_zero_of_map (f := Ideal.Quotient.mk p) ?_
    haveI := Ideal.Quotient.nontrivial hp
    calc
      Ideal.Quotient.mk p A.det = Matrix.det ((Ideal.Quotient.mk p).mapMatrix A) := by
        rw [RingHom.map_det]
      _ = Matrix.det ((Ideal.Quotient.mk p).mapMatrix (Matrix.of A' - 1)) := rfl
      _ = Matrix.det fun i j =>
          (Ideal.Quotient.mk p) (A' i j) - (1 : Matrix (Fin n) (Fin n) (R ⧸ p)) i j := ?_
      _ = Matrix.det (-1 : Matrix (Fin n) (Fin n) (R ⧸ p)) := ?_
      _ = (-1 : R ⧸ p) ^ n := by rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      _ ≠ 0 := IsUnit.ne_zero (isUnit_one.neg.pow _)
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      rw [map_sub, RingHom.mapMatrix_apply, map_one]
      rfl
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hA'p i j), zero_sub]
      rfl
  -- And we conclude `L = span L {det A} ≤ span K b`, so `span K b` spans everything.
  · intro x hx
    rw [Submodule.restrictScalars_mem, IsScalarTower.algebraMap_apply R S L] at hx
    exact IsFractionRing.ideal_span_singleton_map_subset R hRL span_d hx

variable [hRK : IsFractionRing R K]

/-- Let `V` be a vector space over `K = Frac(R)`, `S / R` a ring extension
and `V'` a module over `S`. If `b`, in the intersection `V''` of `V` and `V'`,
is linear independent over `S` in `V'`, then it is linear independent over `R` in `V`.

The statement we prove is actually slightly more general:
* it suffices that the inclusion `algebraMap R S : R → S` is nontrivial
* the function `f' : V'' → V'` doesn't need to be injective
-/
theorem FinrankQuotientMap.linearIndependent_of_nontrivial [IsDedekindDomain R]
    (hRS : RingHom.ker (algebraMap R S) ≠ ⊤) (f : V'' →ₗ[R] V) (hf : Function.Injective f)
    (f' : V'' →ₗ[R] V') {ι : Type*} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (f ∘ b) := by
  contrapose! hb' with hb
  -- Informally, if we have a nontrivial linear dependence with coefficients `g` in `K`,
  -- then we can find a linear dependence with coefficients `I.Quotient.mk g'` in `R/I`,
  -- where `I = ker (algebraMap R S)`.
  -- We make use of the same principle but stay in `R` everywhere.
  simp only [linearIndependent_iff', not_forall] at hb ⊢
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  use s
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_notMem hRS s g hj's hj'g
  choose g'' hg'' using hag
  letI := Classical.propDecidable
  let g' i := if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi; exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  -- Because `R/I` is nontrivial, we can lift `g` to a nontrivial linear dependence in `S`.
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coeIdeal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine ⟨fun i => algebraMap R S (g' i), ?_, j, hjs, hgI⟩
  have eq : f (∑ i ∈ s, g' i • b i) = 0 := by
    rw [map_sum, ← smul_zero a, ← eq, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [LinearMap.map_smul, ← IsScalarTower.algebraMap_smul K, hg' i hi, ← smul_assoc,
      smul_eq_mul, Function.comp_apply]
  simp only [IsScalarTower.algebraMap_smul, ← map_smul, ← map_sum,
    (f.map_eq_zero_iff hf).mp eq, LinearMap.map_zero, (· ∘ ·)]

variable (L)

/-- If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
theorem finrank_quotient_map [IsDomain S] [IsDedekindDomain R] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [hp : p.IsMaximal] [Module.Finite R S] :
    finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L := by
  -- Choose an arbitrary basis `b` for `[S/pS : R/p]`.
  -- We'll use the previous results to turn it into a basis on `[Frac(S) : Frac(R)]`.
  let ι := Module.Free.ChooseBasisIndex (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  let b : Basis ι (R ⧸ p) (S ⧸ map (algebraMap R S) p) := Module.Free.chooseBasis _ _
  -- Namely, choose a representative `b' i : S` for each `b i : S / pS`.
  let b' : ι → S := fun i => (Ideal.Quotient.mk_surjective (b i)).choose
  have b_eq_b' : ⇑b = (Submodule.mkQ (map (algebraMap R S) p)).restrictScalars R ∘ b' :=
    funext fun i => (Ideal.Quotient.mk_surjective (b i)).choose_spec.symm
  -- We claim `b'` is a basis for `Frac(S)` over `Frac(R)` because it is linear independent
  -- and spans the whole of `Frac(S)`.
  let b'' : ι → L := algebraMap S L ∘ b'
  have b''_li : LinearIndependent K b'' := ?_
  · have b''_sp : Submodule.span K (Set.range b'') = ⊤ := ?_
    -- Since the two bases have the same index set, the spaces have the same dimension.
    · let c : Basis ι K L := Basis.mk b''_li b''_sp.ge
      rw [finrank_eq_card_basis b, finrank_eq_card_basis c]
    -- It remains to show that the basis is indeed linear independent and spans the whole space.
    · rw [Set.range_comp]
      refine FinrankQuotientMap.span_eq_top p hp.ne_top _ (top_le_iff.mp ?_)
      -- The nicest way to show `S ≤ span b' ⊔ pS` is by reducing both sides modulo pS.
      -- However, this would imply distinguishing between `pS` as `S`-ideal,
      -- and `pS` as `R`-submodule, since they have different (non-defeq) quotients.
      -- Instead we'll lift `x mod pS ∈ span b` to `y ∈ span b'` for some `y - x ∈ pS`.
      intro x _
      have mem_span_b : ((Submodule.mkQ (map (algebraMap R S) p)) x : S ⧸ map (algebraMap R S) p) ∈
          Submodule.span (R ⧸ p) (Set.range b) := b.mem_span _
      rw [← @Submodule.restrictScalars_mem R,
        Submodule.restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective, b_eq_b',
        Set.range_comp, ← Submodule.map_span] at mem_span_b
      obtain ⟨y, y_mem, y_eq⟩ := Submodule.mem_map.mp mem_span_b
      suffices y + -(y - x) ∈ _ by simpa
      rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at y_eq
      exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
  · have := b.linearIndependent; rw [b_eq_b'] at this
    convert FinrankQuotientMap.linearIndependent_of_nontrivial K _
        ((Algebra.linearMap S L).restrictScalars R) _ ((Submodule.mkQ _).restrictScalars R) this
    · rw [Quotient.algebraMap_eq, Ideal.mk_ker]
      exact hp.ne_top
    · exact IsFractionRing.injective S L

end FinrankQuotientMap

section FactLeComap

variable [Algebra R S]

local notation "f" => algebraMap R S
local notation "e" => ramificationIdx f p P

/-- `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
of `P` over `p`. -/
noncomputable instance Quotient.algebraQuotientPowRamificationIdx : Algebra (R ⧸ p) (S ⧸ P ^ e) :=
  Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx)

@[simp]
theorem Quotient.algebraMap_quotient_pow_ramificationIdx (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk (P ^ e) (f x) := rfl

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferable.
-/
def Quotient.algebraQuotientOfRamificationIdxNeZero [hfp : NeZero e] :
    Algebra (R ⧸ p) (S ⧸ P) :=
  Quotient.algebraQuotientOfLEComap (le_comap_of_ramificationIdx_ne_zero hfp.out)

attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

@[simp]
theorem Quotient.algebraMap_quotient_of_ramificationIdx_neZero
    [NeZero e] (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (f x) := rfl

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
noncomputable def powQuotSuccInclusion (i : ℕ) :
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)) →ₗ[R ⧸ p]
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i) where
  toFun x := ⟨x, Ideal.map_mono (Ideal.pow_le_pow_right i.le_succ) x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem powQuotSuccInclusion_injective (i : ℕ) :
    Function.Injective (powQuotSuccInclusion p P i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hx⟩ hx0
  rw [Subtype.ext_iff] at hx0 ⊢
  rwa [powQuotSuccInclusion_apply_coe] at hx0

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
See `quotientToQuotientRangePowQuotSucc` for this as a linear map,
and `quotientRangePowQuotSuccInclusionEquiv` for this as a linear equivalence.
-/
noncomputable def quotientToQuotientRangePowQuotSuccAux {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) :=
  Quotient.map' (fun x : S => ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩)
    fun x y h => by
    rw [Submodule.quotientRel_def] at h ⊢
    simp only [map_mul, LinearMap.mem_range]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul a_mem h)⟩, ?_⟩
    ext
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.coe_sub, Subtype.coe_mk,
      Subtype.coe_mk, map_mul, map_sub, mul_sub]

theorem quotientToQuotientRangePowQuotSuccAux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSuccAux p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ := by
  apply Quotient.map'_mk''

section
variable [hfp : NeZero (ramificationIdx (algebraMap R S) p P)]

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
noncomputable def quotientToQuotientRangePowQuotSucc
    {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →ₗ[R ⧸ p]
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) where
  toFun := quotientToQuotientRangePowQuotSuccAux p P a_mem
  map_add' := by
    intro x y; refine Quotient.inductionOn' x fun x => Quotient.inductionOn' y fun y => ?_
    simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_add,
      quotientToQuotientRangePowQuotSuccAux_mk, mul_add]
    exact congr_arg Submodule.Quotient.mk rfl
  map_smul' := by
    intro x y; refine Quotient.inductionOn' x fun x => Quotient.inductionOn' y fun y => ?_
    simp only [Submodule.Quotient.mk''_eq_mk, RingHom.id_apply,
      quotientToQuotientRangePowQuotSuccAux_mk]
    refine congr_arg Submodule.Quotient.mk ?_
    ext
    simp only [map_mul, Quotient.mk_eq_mk, Submodule.coe_smul_of_tower,
      Algebra.smul_def, Quotient.algebraMap_quotient_pow_ramificationIdx]
    ring

theorem quotientToQuotientRangePowQuotSucc_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ :=
  quotientToQuotientRangePowQuotSuccAux_mk p P a_mem x

theorem quotientToQuotientRangePowQuotSucc_injective [IsDedekindDomain S] [P.IsPrime]
    {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Injective (quotientToQuotientRangePowQuotSucc p P a_mem) := fun x =>
  Quotient.inductionOn' x fun x y =>
    Quotient.inductionOn' y fun y h => by
      have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow_right hi
      simp only [Submodule.Quotient.mk''_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
        Submodule.coe_sub] at h ⊢
      rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩
      rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
        sup_eq_left.mpr Pe_le_Pi1] at hz
      rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.Quotient.quot_mk_eq_mk,
        Ideal.Quotient.mk_eq_mk, ← map_sub, Ideal.Quotient.eq, ← mul_sub] at h
      exact
        (Ideal.IsPrime.mem_pow_mul _
              ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_left
          a_notMem

theorem quotientToQuotientRangePowQuotSucc_surjective [IsDedekindDomain S]
    (hP0 : P ≠ ⊥) [hP : P.IsPrime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Surjective (quotientToQuotientRangePowQuotSucc p P a_mem) := by
  rintro ⟨⟨⟨x⟩, hx⟩⟩
  have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow_right hi.le
  rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr Pe_le_Pi] at hx
  suffices hx' : x ∈ Ideal.span {a} ⊔ P ^ (i + 1) by
    obtain ⟨y', hy', z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
      Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
      Submodule.coe_sub]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩, ?_⟩
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Ideal.Quotient.mk_eq_mk, map_add,
      sub_add_cancel_left, map_neg]
  letI := Classical.decEq (Ideal S)
  rw [sup_eq_prod_inf_factors _ (pow_ne_zero _ hP0), normalizedFactors_pow,
    normalizedFactors_irreducible ((Ideal.prime_iff_isPrime hP0).mpr hP).irreducible, normalize_eq,
    Multiset.nsmul_singleton, Multiset.inter_replicate, Multiset.prod_replicate]
  · rw [← Submodule.span_singleton_le_iff_mem, Ideal.submodule_span_eq] at a_mem a_notMem
    rwa [Ideal.count_normalizedFactors_eq a_mem a_notMem, min_eq_left i.le_succ]
  · intro ha
    rw [Ideal.span_singleton_eq_bot.mp ha] at a_notMem
    have := (P ^ (i + 1)).zero_mem
    contradiction

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDedekindDomain S]
    [P.IsPrime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    ((P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i))
      ≃ₗ[R ⧸ p] S ⧸ P := by
  choose a a_mem a_notMem using
    SetLike.exists_of_lt
      (Ideal.pow_right_strictAnti P hP (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
  refine (LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩).symm
  · exact quotientToQuotientRangePowQuotSucc p P a_mem
  · exact quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem
  · exact quotientToQuotientRangePowQuotSucc_surjective p P hP hi a_mem a_notMem

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
theorem rank_pow_quot_aux [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    {i : ℕ} (hi : i < e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      Module.rank (R ⧸ p) (S ⧸ P) +
        Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1))) := by
  rw [← rank_range_of_injective _ (powQuotSuccInclusion_injective p P i),
    (quotientRangePowQuotSuccInclusionEquiv p P hP0 hi).symm.rank_eq]
  exact (Submodule.rank_quotient_add_rank (LinearMap.range (powQuotSuccInclusion p P i))).symm

theorem rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    (i : ℕ) (hi : i ≤ e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      (e - i) • Module.rank (R ⧸ p) (S ⧸ P) := by
  let Q : ℕ → Prop :=
    fun i => Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ i) }
      = (e - i) • Module.rank (R ⧸ p) (S ⧸ P)
  refine Nat.decreasingInduction' (P := Q) (fun j lt_e _le_j ih => ?_) hi ?_
  · dsimp only [Q]
    rw [rank_pow_quot_aux p P _ lt_e, ih, ← succ_nsmul', Nat.sub_succ, ← Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt_e)]
    assumption
  · dsimp only [Q]
    rw [Nat.sub_self, zero_nsmul, map_quotient_self]
    exact rank_bot (R ⧸ p) (S ⧸ P ^ e)

end

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
theorem rank_prime_pow_ramificationIdx [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime]
    (hP0 : P ≠ ⊥) (he : e ≠ 0) :
    Module.rank (R ⧸ p) (S ⧸ P ^ e) =
      e •
        @Module.rank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  letI : NeZero e := ⟨he⟩
  have := rank_pow_quot p P hP0 0 (Nat.zero_le e)
  rw [pow_zero, Nat.sub_zero, Ideal.one_eq_top, Ideal.map_top] at this
  exact (rank_top (R ⧸ p) _).symm.trans this

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
theorem finrank_prime_pow_ramificationIdx [IsDedekindDomain S] (hP0 : P ≠ ⊥)
    [p.IsMaximal] [P.IsPrime] (he : e ≠ 0) :
    finrank (R ⧸ p) (S ⧸ P ^ e) =
      e *
        @finrank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  letI : NeZero e := ⟨he⟩
  letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfRamificationIdxNeZero p P
  have hdim := rank_prime_pow_ramificationIdx _ _ hP0 he
  by_cases hP : FiniteDimensional (R ⧸ p) (S ⧸ P)
  · haveI := (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
    apply @Nat.cast_injective Cardinal
    rw [finrank_eq_rank', Nat.cast_mul, finrank_eq_rank', hdim, nsmul_eq_mul]
  have hPe := mt (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mp hP
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe,
    mul_zero]

end FactLeComap

section FactorsMap

/-! ## Properties of the factors of `p.map (algebraMap R S)` -/


variable [IsDedekindDomain S] [Algebra R S]

open scoped Classical in
theorem Factors.ne_bot (P : (factors (map (algebraMap R S) p)).toFinset) : (P : Ideal S) ≠ ⊥ :=
  (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero

open scoped Classical in
instance Factors.isPrime (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsPrime (P : Ideal S) :=
  Ideal.isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))

open scoped Classical in
theorem Factors.ramificationIdx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    ramificationIdx (algebraMap R S) p P ≠ 0 :=
  IsDedekindDomain.ramificationIdx_ne_zero (ne_zero_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    (Factors.isPrime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2)))

open scoped Classical in
instance Factors.fact_ramificationIdx_neZero (P : (factors (map (algebraMap R S) p)).toFinset) :
    NeZero (ramificationIdx (algebraMap R S) p P) :=
  ⟨Factors.ramificationIdx_ne_zero p P⟩

attribute [local instance] Quotient.algebraQuotientOfRamificationIdxNeZero

open scoped Classical in
instance Factors.isScalarTower (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsScalarTower R (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
instance Factors.liesOver [p.IsMaximal] (P : (factors (map (algebraMap R S) p)).toFinset) :
    P.1.LiesOver p :=
  ⟨(comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P.1)).injective).symm⟩

open scoped Classical in
theorem Factors.finrank_pow_ramificationIdx [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) =
      ramificationIdx (algebraMap R S) p P * inertiaDeg p (P : Ideal S) := by
  rw [finrank_prime_pow_ramificationIdx, inertiaDeg_algebraMap]
  exacts [Factors.ne_bot p P, NeZero.ne _]

open scoped Classical in
instance Factors.finiteDimensional_quotient_pow [Module.Finite R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) := by
  refine .of_finrank_pos ?_
  rw [pos_iff_ne_zero, Factors.finrank_pow_ramificationIdx]
  exact mul_ne_zero (Factors.ramificationIdx_ne_zero p P) (inertiaDeg_pos p P.1).ne'

universe w

open scoped Classical in
/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Ideal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    S ⧸ map (algebraMap R S) p ≃+*
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
    @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
      (fun P => S ⧸ (P : Ideal S) ^ (factors (map (algebraMap R S) p)).count (P : Ideal S))
      (fun P => S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) _ _
      fun P : (factors (map (algebraMap R S) p)).toFinset =>
      Ideal.quotEquivOfEq <| by
        rw [IsDedekindDomain.ramificationIdx_eq_factors_count hp (Factors.isPrime p P)
            (Factors.ne_bot p P)]

@[simp]
theorem Factors.piQuotientEquiv_mk (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x) = fun _ => Ideal.Quotient.mk _ x := rfl

@[simp]
theorem Factors.piQuotientEquiv_map (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : R) :
    Factors.piQuotientEquiv p hp (algebraMap _ _ x) = fun _ =>
      Ideal.Quotient.mk _ (algebraMap _ _ x) := rfl

variable (S)

open scoped Classical in
/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Ideal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientLinearEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  { Factors.piQuotientEquiv p hp with
    map_smul' := by
      rintro ⟨c⟩ ⟨x⟩; ext P
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, Algebra.smul_def,
        Quotient.algebraMap_quotient_map_quotient, Quotient.mk_algebraMap,
        RingHomCompTriple.comp_apply, Pi.mul_apply, Pi.algebraMap_apply]
      congr }

open scoped Classical in
/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extension) and `p`
is maximal. -/
theorem sum_ramification_inertia (K L : Type*) [Field K] [Field L] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p S,
        ramificationIdx (algebraMap R S) p P * inertiaDeg p P = finrank K L := by
  set e := ramificationIdx (algebraMap R S) p
  set f := inertiaDeg p (S := S)
  calc
    (∑ P ∈ (factors (map (algebraMap R S) p)).toFinset, e P * f P) =
        ∑ P ∈ (factors (map (algebraMap R S) p)).toFinset.attach,
          finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ e P) := ?_
    _ = finrank (R ⧸ p)
          (∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ e P) :=
      (finrank_pi_fintype (R ⧸ p)).symm
    _ = finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) := ?_
    _ = finrank K L := ?_
  · rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Factors.finrank_pow_ramificationIdx]
  · refine LinearEquiv.finrank_eq (Factors.piQuotientLinearEquiv S p ?_).symm
    rwa [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp <|
      algebraMap_injective_of_field_isFractionRing R S K L, le_bot_iff]
  · exact finrank_quotient_map p K L

/-- `Ideal.sum_ramification_inertia`, in the local (DVR) case. -/
lemma ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (K L : Type*) [Field K] [Field L] [IsLocalRing S]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L] [Module.Finite R S] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ramificationIdx (algebraMap R S) p (IsLocalRing.maximalIdeal S) *
      p.inertiaDeg (IsLocalRing.maximalIdeal S) = Module.finrank K L := by
  have := FaithfulSMul.of_field_isFractionRing R S K L
  simp_rw [← sum_ramification_inertia S K L hp0, IsLocalRing.primesOverFinset_eq S hp0,
    Finset.sum_singleton]

end FactorsMap

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem ramificationIdx_tower [IsDedekindDomain S] [IsDedekindDomain T] {f : R →+* S} {g : S →+* T}
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm : Q.IsPrime]
    (hg0 : map g P ≠ ⊥) (hfg : map (g.comp f) p ≠ ⊥) (hg : map g P ≤ Q) :
    ramificationIdx (g.comp f) p Q = ramificationIdx f p P * ramificationIdx g P Q := by
  classical
  have hf0 : map f p ≠ ⊥ :=
    ne_bot_of_map_ne_bot (Eq.mp (congrArg (fun I ↦ I ≠ ⊥) (map_map f g).symm) hfg)
  have hp0 : P ≠ ⊥ := ne_bot_of_map_ne_bot hg0
  have hq0 : Q ≠ ⊥ := ne_bot_of_le_ne_bot hg0 hg
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpm
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hf0 hpm hp0,
    IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hg0 hqm hq0,
    IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hfg hqm hq0, ← map_map]
  rcases eq_prime_pow_mul_coprime hf0 P with ⟨I, hcp, heq⟩
  have hcp : ⊤ = map g P ⊔ map g I := by rw [← map_sup, hcp, map_top g]
  have hntq : ¬ ⊤ ≤ Q := fun ht ↦ IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, Ideal.map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) <| by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, bot_le, sup_of_le_left] at hcp
    exact hntq (hcp.trans_le hg), Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul]
  exact add_eq_left.mpr <| Decidable.byContradiction fun h ↦ hntq <| hcp.trans_le <|
    sup_le hg <| le_of_dvd <| dvd_of_mem_normalizedFactors <| Multiset.count_ne_zero.mp h

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Let `T / S / R` be a tower of algebras, `p, P, Q` be ideals in `R, S, T` respectively,
  and `P` and `Q` are prime. If `P = Q ∩ S`, then `e (Q | p) = e (P | p) * e (Q | P)`. -/
theorem ramificationIdx_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm : Q.IsPrime]
    (hg0 : map (algebraMap S T) P ≠ ⊥)
    (hfg : map (algebraMap R T) p ≠ ⊥) (hg : map (algebraMap S T) P ≤ Q) :
    ramificationIdx (algebraMap R T) p Q =
    ramificationIdx (algebraMap R S) p P * ramificationIdx (algebraMap S T) P Q := by
  rw [IsScalarTower.algebraMap_eq R S T] at hfg ⊢
  exact ramificationIdx_tower hg0 hfg hg

/-- Let `T / S / R` be a tower of algebras, `p, P, I` be ideals in `R, S, T`, respectively,
  and `p` and `P` are maximal. If `p = P ∩ S` and `P = I ∩ S`,
  then `f (I | p) = f (P | p) * f (I | P)`. -/
theorem inertiaDeg_algebra_tower (p : Ideal R) (P : Ideal S) (I : Ideal T) [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] : inertiaDeg p I =
    inertiaDeg p P * inertiaDeg P I := by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg, dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  letI : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  letI : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₂.le
  letI : Algebra (R ⧸ p) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₃.le
  letI : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact (finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm

end tower

end Ideal
