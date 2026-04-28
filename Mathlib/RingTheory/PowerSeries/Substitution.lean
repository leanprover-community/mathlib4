/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic.Ring.NamePowerVars

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

Because of the special API for `PowerSeries`, some results for `MvPowerSeries`
do not immediately apply and a “primed” version is provided here.

-/

@[expose] public section

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

/-- (Possibly multivariate) power series which can be substituted in a `PowerSeries`. -/
abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff a)

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
    HasEval a := isTopologicallyNilpotent_of_constantCoeff_isNilpotent ha

theorem HasSubst.of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff a = 0) : HasSubst a := by
  simp [HasSubst, ha]

/-- A variant of `HasSubst.of_constantCoeff_zero` for `PowerSeries`
to avoid the expansion of `Unit`. -/
theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}
    (ha : PowerSeries.constantCoeff a = 0) : HasSubst a :=
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
    HasSubst (MvPowerSeries.monomial n s) := by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
    if_neg hn.symm]

/-- A variant of `HasSubst.monomial` to avoid the expansion of `Unit`. -/
protected theorem HasSubst.monomial' {n : ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (monomial n s) :=
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
  exact (Commute.all _ _).isNilpotent_mul_right hf

theorem HasSubst.mul_right (hf : HasSubst f) :
    HasSubst (g * f) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf

theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) :=
  ha.mul_right

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

lemma HasSubst.eventually_coeff_pow_eq_zero {f : A⟦X⟧} (hf : HasSubst f) (n : ℕ) :
    ∀ᶠ m in .atTop, ∀ n' ≤ n, coeff n' (f ^ m) = 0 := by
  obtain ⟨k, hk⟩ := id hf
  refine Filter.eventually_of_mem (Filter.Ici_mem_atTop (k * (n + 1))) fun m hm n' hn' ↦
    coeff_of_lt_order _ ?_
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp (Set.mem_Ici.mp hm)
  grw [pow_add, ← order_mul_ge, pow_mul, ← le_order_pow_of_constantCoeff_eq_zero _
    (by rwa [map_pow]), ← _root_.le_add_right le_rfl, Nat.cast_lt]
  lia

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

/-- Substitution of power series into a power series. -/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

lemma subst_def (a : MvPowerSeries τ S) (f : PowerSeries R) :
    subst a f = MvPowerSeries.subst (fun _ ↦ a) f := rfl

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

theorem subst_sub (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f - g) = subst a f - subst a g := by
  rw [← coe_substAlgHom ha, map_sub]

theorem subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul [Algebra A S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    (fun (d : ℕ) ↦ coeff d f • MvPowerSeries.coeff e (a ^ d)).HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]

theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) :
    (fun (d : ℕ) ↦ coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport :=
  coeff_subst_finite hb f _

theorem coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (subst a f) =
      finsum (fun (d : ℕ) ↦
        coeff d f • (MvPowerSeries.coeff e (a ^ d))) := by
  rw [subst, MvPowerSeries.coeff_subst ha.const f e, ← finsum_comp_equiv
    (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro
  congr <;> simp

theorem coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : ℕ) :
    coeff e (f.subst b) =
      finsum (fun (d : ℕ) ↦
        coeff d f • PowerSeries.coeff e (b ^ d)) := by
  simp [PowerSeries.coeff, coeff_subst hb]

theorem constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (subst a f) =
      finsum (fun d ↦ coeff d f • MvPowerSeries.constantCoeff (a ^ d)) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

@[simp]
theorem coeff_subst_X_pow {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) (n : ℕ) :
    coeff n (subst (X ^ k) f) = ite (k ∣ n) (algebraMap R S (coeff (n / k) f)) 0 := by
  split_ifs with h
  · rw [coeff_subst' (.X_pow hk), finsum_eq_single _ (n / k), ← pow_mul, Nat.mul_div_cancel' h,
      coeff_X_pow_self, Algebra.algebraMap_eq_smul_one]
    intro j hj
    rw [← pow_mul, coeff_X_pow, if_neg, smul_zero]
    contrapose hj
    rw [hj, Nat.mul_div_cancel_left j hk.pos]
  · rw [coeff_subst' (.X_pow hk), finsum_eq_zero_of_forall_eq_zero]
    intro j
    rw [← pow_mul, coeff_X_pow, if_neg, smul_zero]
    contrapose h
    use j

@[simp]
theorem constantCoeff_subst_X_pow {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    constantCoeff (subst (X ^ k) f) = algebraMap R S f.constantCoeff := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst_X_pow hk, if_pos (dvd_zero k),
    Nat.zero_div, coeff_zero_eq_constantCoeff]

theorem constantCoeff_subst_eq_zero (ha : a.constantCoeff = 0) (f : PowerSeries R)
    (hf : f.constantCoeff = 0) : MvPowerSeries.constantCoeff (subst a f) = 0 := by
  have := MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_iff.mp <| HasSubst.of_constantCoeff_zero ha) (fun _ ↦ ha) hf
  simpa [hasSubst_iff]

theorem map_algebraMap_eq_subst_X (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f

lemma coeff_subst_single {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (subst (MvPowerSeries.X s) f) =
      if e = Finsupp.single s (e s) then coeff (e s) f else 0 := by
  rw [coeff_subst (HasSubst.X s), finsum_eq_single _ (e s)] <;>
  grind [MvPowerSeries.coeff_X_pow, smul_eq_mul]

@[simp]
theorem X_subst (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f := by
  rw [← map_algebraMap_eq_subst_X (S := R), Algebra.algebraMap_self]
  exact congr_fun map_id f

theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) : (p : PowerSeries R) =
    ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) :=
  Polynomial.pUnitAlgEquiv_symm_toPowerSeries

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

@[simp]
theorem subst_C (r : S) : (C r).subst a = MvPowerSeries.C r := MvPowerSeries.subst_C _

theorem subst_X (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

omit [Algebra R S] in
theorem map_subst {a : MvPowerSeries τ R} (ha : HasSubst a) {h : R →+* S} (f : PowerSeries R) :
    (f.subst a).map h = (f.map h).subst (a.map h) :=
  MvPowerSeries.map_subst (HasSubst.const ha) f

section

theorem le_weightedOrder_subst (w : τ → ℕ) (ha : HasSubst a) (f : PowerSeries R) :
    f.order * a.weightedOrder w ≤ (f.subst a).weightedOrder w := by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ (PowerSeries.hasSubst_iff.mp ha) _)
  simp only [ne_eq, Function.comp_const, le_iInf_iff]
  intro i hi
  trans i () * MvPowerSeries.weightedOrder w a
  · exact mul_le_mul_left (f.order_le (i ()) (by delta PowerSeries.coeff; convert hi; aesop)) _
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype]

theorem le_order_subst (a : MvPowerSeries τ S) (ha : HasSubst a) (f : PowerSeries R) :
    a.order * f.order ≤ (f.subst a).order := by
  refine .trans ?_ (MvPowerSeries.le_order_subst (PowerSeries.hasSubst_iff.mp ha) _)
  simp [order_eq_order]

theorem le_order_subst_left {f : MvPowerSeries τ R} {φ : PowerSeries R}
    (hf : f.constantCoeff = 0) : φ.order ≤ (φ.subst f).order :=
  .trans (ENat.self_le_mul_left φ.order (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

theorem le_order_subst_right {f : MvPowerSeries τ R} {φ : PowerSeries R}
    (hf : f.constantCoeff = 0) (hφ : φ.constantCoeff = 0) : f.order ≤ (φ.subst f).order :=
  .trans (ENat.self_le_mul_right _ (order_ne_zero_iff_constCoeff_eq_zero.mpr hφ))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

theorem le_order_subst_left' {f φ : PowerSeries R} (hf : f.constantCoeff = 0) :
    φ.order ≤ PowerSeries.order (φ.subst f) := by
  conv_rhs => rw [order_eq_order]
  exact le_order_subst_left hf

theorem le_order_subst_right' {f φ : PowerSeries R} (hf : f.constantCoeff = 0)
    (hφ : φ.constantCoeff = 0) : f.order ≤ PowerSeries.order (φ.subst f) := by
  simp_rw [order_eq_order]
  exact le_order_subst_right hf hφ

end

theorem HasSubst.comp
    {a : PowerSeries S} (ha : HasSubst a) {b : MvPowerSeries υ T} (hb : HasSubst b) :
    HasSubst (substAlgHom hb a) :=
  MvPowerSeries.IsNilpotent_subst hb.const ha

variable {a : PowerSeries S} {b : MvPowerSeries υ T} {a' : MvPowerSeries τ S}
  {b' : τ → MvPowerSeries υ T} [IsScalarTower R S T]

theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa [funext_iff, DFunLike.ext_iff, coe_substAlgHom] using substAlgHom_comp_substAlgHom ha hb

theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst ha hb) f

lemma rescale_eq (r : R) (f : PowerSeries R) :
    rescale r f = MvPowerSeries.rescale (fun _ ↦ r) f := by
  ext n
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp [pow_zero, Finsupp.prod_single_index]

@[deprecated (since := "2026-02-27")] alias _root_.MvPowerSeries.rescaleUnit := rescale_eq

lemma rescale_eq_subst (r : R) (f : PowerSeries R) :
    PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f := by
  rw [rescale_eq, MvPowerSeries.rescale_eq_subst, X, subst, Pi.smul_def']

/-- Rescale power series, as an `AlgHom` -/
noncomputable abbrev rescaleAlgHom (r : R) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.rescaleAlgHom (fun _ ↦ r)

theorem coe_rescaleAlgHom (r : R) : rescaleAlgHom r = rescale r := by
  ext f
  rw [rescale_eq, RingHom.coe_coe, MvPowerSeries.rescaleAlgHom_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Substitution by `p` commutes with scalar homothety. -/
lemma subst_rescale_of_degree_eq_one (a : R) {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin : ∀ d ∈ Function.support p, d.degree = 1) (f : PowerSeries R) :
    subst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply HasSubst.of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
    have : (p 0 ≠ 0) → (0 : σ →₀ ℕ).degree = 1 := hp_lin 0
    grind
  rw [rescale_eq_subst, MvPowerSeries.rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' a) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.HasSubst.smul_X _),
    funext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X,
    ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_homogeneous_eq_smul hp_lin,
    subst, pow_one]

section substInv

variable (P : R⟦X⟧) (hP : P.constantCoeff = 0) [Invertible (coeff 1 P)]

open PowerSeries

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the construction of a power series `Q` such that `P(Q(X)) = X`. -/
noncomputable
def substInvFun : ℕ → R
  | 0 => 0
  | 1 => ⅟(P.coeff 1)
  | n + 1 => - ⅟(P.coeff 1) *
      (coeff (n + 1) (P.subst (∑ i : Fin (n + 1), C (substInvFun i.1) * X ^ i.1)))

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the power series `Q` such that `P(Q(X)) = X`. See `PowerSeries.subst_substInv`. -/
noncomputable
def substInv : PowerSeries R := .mk (substInvFun P)

include hP in
lemma coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X (n : ℕ) :
    coeff n (P.subst (∑ i : Fin (n + 1), C (substInvFun P i.1) * X ^ i.1) - X) = 0 := by
  obtain (_ | _ | n) := n
  · rw [map_sub, coeff_subst']
    · simp +contextual [finsum_eq_single (a := 0), substInvFun, zero_pow_eq, hP]
    · simp [substInvFun, HasSubst]
  · rw [map_sub, coeff_subst']
    · rw [finsum_eq_single (a := 1)]
      · simp [substInvFun]
      · rintro (_ | _ | _) _ <;> simp_all [substInvFun, mul_pow, coeff_mul_X_pow']
    · simp [HasSubst, X, substInvFun]
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, map_sub, substInvFun]
    generalize hB : ∑ i : Fin (n + 2), C (substInvFun P i) * X ^ i.1 = B
    have hB' : B.constantCoeff = 0 := by simp [← hB, zero_pow_eq, substInvFun]
    simp only [neg_mul, map_neg, map_mul, coeff_X, Nat.add_eq_right, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, sub_zero]
    rw [coeff_subst']
    · simp only [smul_eq_mul, ← map_mul]
      generalize hk : ⅟(P.coeff 1) * coeff (n + 1 + 1) (subst B P) = k
      trans ∑ᶠ d, P.coeff d * (coeff (n + 1 + 1) (B ^ d) - if d = 1 then k else 0)
      · refine finsum_congr fun i ↦ ?_
        · congr 1
          obtain (_ | _ | i) := i
          · simp
          · simp [← sub_eq_add_neg]
          · simp only [add_assoc, Nat.reduceAdd]
            rw [add_comm B, add_pow, map_sum, Finset.sum_eq_single (a := 0)]
            · simp
            · rintro (_ | _ | j) hj hj'
              · simp at hj'
              · simp [mul_comm (C k), hB', mul_assoc, coeff_X_pow_mul']
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
            · simp [HasSubst, ← PowerSeries.constantCoeff.eq_def, hB']
          · simp +contextual
        · refine .subset (Set.finite_Iio (n + 3)) fun i ↦ ?_
          obtain ⟨B, rfl⟩ : X ∣ B := by rwa [X_dvd_iff]
          simp +contextual [mul_pow, coeff_X_pow_mul', Nat.lt_succ_iff]
        · exact .subset (Set.finite_singleton 1) (fun _ ↦ by simp +contextual)
    · simp [HasSubst, ← PowerSeries.constantCoeff.eq_def, hB']

include hP in
lemma subst_substInv_right :
    P.subst (substInv P) = X := by
  ext n
  have := coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X P hP n
  rw [map_sub, sub_eq_zero] at this
  rw [← this, coeff_subst', coeff_subst']
  · congr! 3 with m
    generalize hB : (∑ i : Fin (n + 1), C (substInvFun P ↑i) * X ^ i.1) = B
    have : X ^ (n + 1) ∣ mk (substInvFun P) - B := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp +contextual [← hB, coeff_X_pow, Finset.sum_eq_single (⟨m, hm⟩ : Fin (n + 1)),
        Fin.ext_iff, @eq_comm _ m]
    obtain ⟨Q, hQ⟩ := this.trans (sub_dvd_pow_sub_pow _ _ m)
    simp [substInv, sub_eq_iff_eq_add.mp hQ, coeff_X_pow_mul']
  · simp [HasSubst, X, zero_pow_eq, C, substInvFun]
  · simp [HasSubst, ← constantCoeff.eq_def, substInvFun, substInv]

@[simp]
lemma constantCoeff_substInv : P.substInv.constantCoeff = 0 := by
  simp [substInv, substInvFun]

lemma hasSubst_substInv : HasSubst P.substInv := by simp [HasSubst, ← constantCoeff.eq_def]

@[simp]
lemma coeff_one_substInv : P.substInv.coeff 1 = ⅟(P.coeff 1) := by
  simp [substInv, substInvFun]

include hP in
lemma subst_substInv_left : P.substInv.subst P = X := by
  have hP' : HasSubst P := by simp [HasSubst, ← constantCoeff.eq_def, hP]
  let Q : PowerSeries R := P.substInv.subst P
  have : Invertible (Q.coeff 1) := by
    refine IsUnit.invertible ?_
    rw [PowerSeries.coeff_subst' (hb := hP'), finsum_eq_single (a := 1)]
    · simp
    · have (n : ℕ) : (P ^ (n + 1 + 1)).coeff 1 = 0 := by
        obtain ⟨P, rfl⟩ := X_dvd_iff.mpr hP
        simp [mul_pow, coeff_X_pow_mul']
      rintro (_ | _ | n) hn <;> simp_all
  have hQ : Q.constantCoeff = 0 := by
    trans coeff 0 (P.substInv.subst P)
    · simp [Q]
    simp +contextual [PowerSeries.coeff_subst' hP', hP, zero_pow_eq, finsum_eq_single _ 0]
  have hQ' : HasSubst Q := by simp [HasSubst, ← constantCoeff.eq_def, hQ]
  have : Q.subst Q = Q := by
    rw [subst_comp_subst_apply (ha := hP') (hb := hQ'), ← subst_comp_subst_apply
      (ha := hasSubst_substInv _) (hb := hP'), PowerSeries.subst_substInv_right _ hP, subst_X hP']
  convert congr(PowerSeries.subst Q.substInv $this) using 1
  · rw [PowerSeries.subst_comp_subst_apply (ha := hQ') (hb := hasSubst_substInv _)]
    refine (PowerSeries.map_algebraMap_eq_subst_X (S := R) Q).trans ?_
    simp only [PowerSeries.subst]
    congr! with ⟨⟩
    exact (PowerSeries.subst_substInv_right Q hQ).symm
  · exact (PowerSeries.subst_substInv_right Q hQ).symm

end substInv

section Bivariate

open Finset Finsupp Nat

name_power_vars X₀, X₁ over R

lemma coeff_subst_X_zero_add_X_one (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff e) (subst (X₀ + X₁) f) =
      (e 0 + e 1).choose (e 0) * coeff (e 0 + e 1) f := by
  rw [PowerSeries.subst, MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ ↦ by simp))]
  simp_rw [Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
    MvPolynomial.coeff_coe]
  rw [finsum_eq_single _ (single () (e 0 + e 1)), mul_comm]
  · simp [MvPolynomial.coeff_add_pow, coeff]
  · simp only [MvPolynomial.coeff_add_pow, mem_antidiagonal, cast_ite]
    grind

lemma coeff_subst_X_zero_mul_X_one (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (subst X₀ f * subst X₁ f) = coeff (e 0) f * coeff (e 1) f := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (single 0 (e 0), single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← mem_antidiagonal.mp hb, h0.1, h1.1]
    simp
  · intro he
    have he' : single 0 (e 0) + single 1 (e 1) = e := by
      ext i
      fin_cases i <;> simp
    exact absurd (mem_antidiagonal.mpr he') he

end Bivariate

end PowerSeries
