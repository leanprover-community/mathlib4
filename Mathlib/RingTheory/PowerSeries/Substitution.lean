/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Evaluation

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

Because of the special API for `PowerSeries`, some results for `MvPowerSeries`
do not immediately apply and a “primed” version is provided here.

-/

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

/-- (Possibly multivariate) power series which can be substituted in a `PowerSeries`. -/
abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff τ S a)

theorem hasSubst_iff {a : MvPowerSeries τ S} :
    HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha ↦ (ha.const_coeff ())⟩

theorem HasSubst.const {a : MvPowerSeries τ S} (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun () ↦ a) :=
  hasSubst_iff.mp ha

theorem hasSubst_iff_hasEval_of_discreteTopology
    [TopologicalSpace S] [DiscreteTopology S] {a : MvPowerSeries τ S} :
    HasSubst a ↔ PowerSeries.HasEval a := by
  rw [hasSubst_iff, MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology, hasEval_iff,
    Function.const_def]

theorem HasSubst.hasEval [TopologicalSpace S] {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasEval a := by
  rw [hasEval_iff]
  apply MvPowerSeries.HasSubst.hasEval
  simpa [hasSubst_iff] using ha

theorem HasSubst.of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) : HasSubst a := by
  simp [HasSubst, ha]

/-- A variant of `HasSubst.of_constantCoeff_zero` for `PowerSeries`
to avoid the expansion of `Unit`. -/
theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}
    (ha : PowerSeries.constantCoeff S a = 0) : HasSubst a :=
  HasSubst.of_constantCoeff_zero ha

protected theorem HasSubst.X (t : τ) :
    HasSubst (MvPowerSeries.X t : MvPowerSeries τ S) := by
  simp [HasSubst]

/-- The univariate `X : R⟦X⟧` can be substituted in power series

This lemma is added because `simp` doesn't find it from `HasSubst.X`. -/
protected theorem HasSubst.X' : HasSubst (X : R⟦X⟧) :=
  HasSubst.X _

protected theorem HasSubst.X_pow {n : ℕ} (hn : n ≠ 0) : HasSubst (X ^ n : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp [hn])

protected theorem HasSubst.monomial {n : τ →₀ ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (MvPowerSeries.monomial S n s) := by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
    if_neg hn.symm]

/-- A variant of `HasSubst.monomial` to avoid the expansion of `Unit`. -/
protected theorem HasSubst.monomial' {n : ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (monomial S n s) :=
  HasSubst.monomial (Finsupp.single_ne_zero.mpr hn) s

theorem HasSubst.zero : HasSubst (0 : MvPowerSeries τ R) := by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero

/-- A variant of `HasSubst.zero` to avoid the expansion of `Unit`. -/
theorem HasSubst.zero' : HasSubst (0 : PowerSeries R) :=
  PowerSeries.HasSubst.zero

variable {f g : MvPowerSeries τ R}

theorem HasSubst.add (hf : HasSubst f) (hg : HasSubst g) :
    HasSubst (f + g) :=
  (Commute.all _ _).isNilpotent_add hf hg


theorem HasSubst.mul_left (hf : HasSubst f) :
    HasSubst (f * g) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf

theorem HasSubst.mul_right (hf : HasSubst f) :
    HasSubst (g * f) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right hf

theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S}
    (ha : HasSubst a) :
  HasSubst (r • a) := ha.mul_right

/-- Families of `PowerSeries` that can be substituted, as an `Ideal`. -/
noncomputable def HasSubst.ideal : Ideal (MvPowerSeries τ S) where
  carrier := setOf HasSubst
  add_mem' := HasSubst.add
  zero_mem' := HasSubst.zero
  smul_mem' := HasSubst.smul

/-- A more general version of `HasSubst.smul`. -/
theorem HasSubst.smul' (a : A) (hf : HasSubst f) :
    HasSubst (a • f) := by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

theorem HasSubst.smul_X (a : A) (t : τ) :
    HasSubst (a • (MvPowerSeries.X t) : MvPowerSeries τ R) :=
  (HasSubst.X t).smul' _

theorem HasSubst.smul_X' (a : A) : HasSubst (a • X : R⟦X⟧) :=
  HasSubst.X'.smul' _

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

/-- Substitution of power series into a power series. -/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S} {b : S⟦X⟧}

/-- Substitution of power series into a power series, as an `AlgHom`. -/
noncomputable def substAlgHom (ha : HasSubst a) :
    PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

attribute [local instance] DiscreteTopology.instContinuousSMul in
/-- Rewrite `PowerSeries.substAlgHom` as `PowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons. -/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : R⟦X⟧ →ₐ[R] MvPowerSeries τ S) = PowerSeries.aeval ha.hasEval := by
  ext1 f
  simpa [substAlgHom] using congr_fun (MvPowerSeries.substAlgHom_eq_aeval ha.const) f

theorem subst_add (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul [Algebra A S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : ℕ) ↦ (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))).support := by
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]

theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) :
    Set.Finite (fun (d : ℕ) ↦ (coeff R d f) • (PowerSeries.coeff S e (b ^ d))).support :=
  coeff_subst_finite hb f  _

theorem coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff S e (subst a f) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))) := by
  rw [subst, MvPowerSeries.coeff_subst ha.const f e, ← finsum_comp_equiv
    (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro
  congr <;> simp

theorem coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : ℕ) :
    coeff S e (f.subst b) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (PowerSeries.coeff S e (b ^ d))) := by
  simp [PowerSeries.coeff, coeff_subst hb]

theorem constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (MvPowerSeries.constantCoeff τ S (a ^ d))) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f

theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) :
    (p : PowerSeries R) =
      ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) := by
  suffices (Polynomial.coeToPowerSeries.algHom R) p =
    (MvPolynomial.coeToMvPowerSeries.algHom R)
      (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R) p) by simpa
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp [X]

theorem substAlgHom_coe (ha : HasSubst a) (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries, substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_coe, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp

theorem substAlgHom_X (ha : HasSubst a) :
    substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, substAlgHom_coe, Polynomial.aeval_X]

theorem subst_coe (ha : HasSubst a) (p : Polynomial R) :
    subst a (p : PowerSeries R) = (Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

theorem HasSubst.comp {a : PowerSeries S} (ha : HasSubst a)
  {b : MvPowerSeries υ T} (hb : HasSubst b) :
    HasSubst (substAlgHom hb a) :=
  MvPowerSeries.IsNilpotent_subst hb.const ha

variable {a : PowerSeries S} {b : MvPowerSeries υ T} {a' : MvPowerSeries τ S}
  {b' : τ → MvPowerSeries υ T} [IsScalarTower R S T]

theorem substAlgHom_comp_substAlgHom
  (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha)
      = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply
  (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom  ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa [funext_iff, DFunLike.ext_iff, coe_substAlgHom] using substAlgHom_comp_substAlgHom ha hb

theorem subst_comp_subst_apply
  (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst ha hb) f

theorem _root_.MvPowerSeries.rescaleUnit (a : R) (f : R⟦X⟧) :
    MvPowerSeries.rescale (Function.const _ a) f = rescale a f := by
  ext d
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp

section substInv

variable (P : R⟦X⟧) (hP : P.constantCoeff _ = 0) [Invertible (coeff _ 1 P)]

open PowerSeries

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the construction of a power series `Q` such that `P(Q(X)) = X`. -/
noncomputable
def substInvFun : ℕ → R
  | 0 => 0
  | 1 => ⅟ (coeff _ 1 P)
  | n + 1 => - ⅟ (coeff _ 1 P) *
      (coeff _ (n + 1) (P.subst (∑ i : Fin (n + 1), C _ (substInvFun i.1) * X ^ i.1)))

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the power series `Q` such that `P(Q(X)) = X`. See `PowerSeries.subst_substInv`. -/
noncomputable
def substInv : PowerSeries R := .mk (substInvFun P)

include hP in
lemma coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X (n : ℕ) :
    coeff _ n (P.subst (∑ i : Fin (n + 1), C _ (substInvFun P i.1) * X ^ i.1) - X) = 0 := by
  obtain (_|_|n) := n
  · rw [map_sub, coeff_subst']
    · simp +contextual [finsum_eq_single (a := 0), substInvFun, zero_pow_eq, hP]
    · simp [substInvFun, HasSubst]
  · simp only [map_sub, coeff_one_X]
    rw [coeff_subst']
    · rw [finsum_eq_single (a := 1)]
      · simp [substInvFun]
      · rintro (_|_|_) _ <;> simp_all [substInvFun, mul_pow, coeff_mul_X_pow']
    · simp [HasSubst, X, substInvFun]
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, map_sub, substInvFun]
    generalize hB : ∑ i : Fin (n + 2), C R (substInvFun P i) * X ^ i.1 = B
    have hB' : constantCoeff R B = 0 := by simp [← hB, zero_pow_eq, substInvFun]
    simp only [neg_mul, map_neg, map_mul, coeff_X, Nat.add_eq_right, Nat.add_eq_zero, one_ne_zero,
      and_false, ↓reduceIte, sub_zero]
    rw [coeff_subst']
    · simp only [smul_eq_mul, ← map_mul]
      generalize hk : ⅟ (coeff R 1 P) * coeff R (n + 1 + 1) (subst B P) = k
      trans ∑ᶠ d, coeff R d P * (coeff R (n + 1 + 1) (B ^ d) - if d = 1 then k else 0)
      · refine finsum_congr fun i ↦ ?_
        · congr 1
          obtain (_|_|i) := i
          · simp
          · simp [← sub_eq_add_neg, ← map_mul]
          · simp only [add_assoc, Nat.reduceAdd, sub_zero]
            rw [add_comm B, add_pow, map_sum, Finset.sum_eq_single (a := 0)]
            · simp
            · rintro (_|_|j) hj hj'
              · simp at hj'
              · simp [mul_comm (C R k), hB', mul_assoc, coeff_X_pow_mul']
              · rw [← neg_mul, mul_pow, ← pow_mul, mul_comm (_ ^ _)]
                simp [mul_assoc, coeff_X_pow_mul']
            · simp
      · simp_rw [mul_sub]
        rw [finsum_sub_distrib]
        · simp only [mul_ite, mul_zero]
          nth_rw 2 [finsum_eq_single (a := 1)]
          · simp only [↓reduceIte, ← hk, mul_invOf_cancel_left', sub_eq_zero]
            rw [coeff_subst']
            · rfl
            · change IsNilpotent (constantCoeff _ B)
              simp [hB']
          · simp +contextual
        · refine .subset (Set.finite_Iio (n + 3)) fun i ↦ ?_
          obtain ⟨B, rfl⟩ : X ∣ B := by rwa [X_dvd_iff]
          simp +contextual [mul_pow, coeff_X_pow_mul', Nat.lt_succ]
        · exact .subset (Set.finite_singleton 1) (fun _ ↦ by simp +contextual)
    · simp [HasSubst, X, show MvPowerSeries.constantCoeff Unit R B = 0 from hB']

include hP in
lemma subst_substInv :
    P.subst (substInv P) = X := by
  ext n
  have := coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X P hP n
  rw [map_sub, sub_eq_zero] at this
  rw [← this, coeff_subst', coeff_subst']
  · congr! 3 with m
    generalize hB : (∑ i : Fin (n + 1), (C R) (substInvFun P ↑i) * X ^ i.1) = B
    have : X ^ (n + 1) ∣ mk (substInvFun P) - B := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp +contextual [← hB, coeff_X_pow, Finset.sum_eq_single (⟨m, hm⟩ : Fin (n + 1)),
        Fin.ext_iff, @eq_comm _ m]
    obtain ⟨Q, hQ⟩ := this.trans (sub_dvd_pow_sub_pow _ _ m)
    simp [substInv, sub_eq_iff_eq_add.mp hQ, coeff_X_pow_mul']
  · simp [HasSubst, X, zero_pow_eq, C, substInvFun]
  · show IsNilpotent (mk (substInvFun P) 0)
    simp [HasSubst, mk, substInvFun]

end substInv

end PowerSeries
