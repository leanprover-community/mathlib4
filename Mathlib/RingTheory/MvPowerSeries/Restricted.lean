/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Order.Antidiag.Tendsto
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Multivariate restricted power series

`IsRestricted` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

namespace MvPowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] {σ : Type*}

/-- A multivariate power series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter. -/
def IsRestricted (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]
lemma isRestricted_abs_iff (c : σ → ℝ) (f : MvPowerSeries σ R) :
    IsRestricted |c| f ↔ IsRestricted c f := by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

lemma isRestricted_zero (c : σ → ℝ) : IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

lemma isRestricted_monomial (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  simp [Set.Subsingleton, coeff_monomial]

lemma isRestricted_one (c : σ → ℝ) : IsRestricted c (1 : MvPowerSeries σ R) :=
  isRestricted_monomial c 0 1

lemma isRestricted_C (c : σ → ℝ) (a : R) : IsRestricted c (C a) := by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a

lemma isRestricted_X (c : σ → ℝ) (s : σ) : IsRestricted c (X s : MvPowerSeries σ R) := by
  simpa [X_def] using isRestricted_monomial c (Finsupp.single s 1) 1

lemma isRestricted.add (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ hf.add hg) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)

lemma isRestricted.neg (c : σ → ℝ) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (-f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  simpa [IsRestricted] using hf

lemma isRestricted_of_finite_support (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : (Function.support fun t ↦ coeff t f).Finite) : IsRestricted c f :=
  tendsto_nhds_of_eventually_eq <| eventually_cofinite.mpr <| hf.subset fun t ht ↦
    Function.mem_support.mpr fun h0 ↦ ht (by simp [h0])

lemma isRestricted.smul (c : σ → ℝ) (r : R) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (r • f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (mul_zero ‖r‖ ▸ hf.const_mul ‖r‖) (fun t ↦ ?_) fun t ↦ ?_
  · dsimp [Finsupp.prod]; positivity
  · rw [coeff_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mul_le ..) (by dsimp [Finsupp.prod]; positivity)

open IsUltrametricDist

open Finset.HasAntidiagonal in
lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M → ℝ} (hC : ∀ a b, C (a + b) = C a * C b) {f g : M → S}
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  wlog hC' : 0 ≤ C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x ↦ mul_nonneg (by simp) (hC' x)) fun a ↦ ?_
  have : 0 ≤ C a := hC' a
  grw [(nonempty_antidiagonal _).norm_sum_le_sup'_norm, Finset.sup'_mul₀ this]
  refine Finset.sup'_mono_fun fun x hx ↦ ?_
  grw [mul_mul_mul_comm, ← hC, Finset.mem_antidiagonal.mp hx, ← norm_mul_le]

lemma isRestricted.mul [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  rw [← isRestricted_abs_iff, IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

lemma isRestricted_map {S : Type*} [NormedRing S] (c : σ → ℝ) (π : R → S) (C : ℝ)
    (hCπ : ∀ x, ‖π x‖ ≤ C * ‖x‖) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (fun t ↦ π (coeff t f) : MvPowerSeries σ S) := by
  rw [← isRestricted_abs_iff, IsRestricted] at hf
  refine (isRestricted_abs_iff ..).mp <| tendsto_const_nhds.squeeze
    (mul_zero C ▸ hf.const_mul C) (fun t ↦ ?_) fun t ↦ ?_
  · dsimp [Finsupp.prod]; positivity
  · rw [coeff_apply, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hCπ _) (by dsimp [Finsupp.prod]; positivity)

namespace IsRestricted

/-- Restricted power series as an additive subgroup of `MvPowerSeries σ R`. -/
protected def addSubgroup (c : σ → ℝ) : AddSubgroup (MvPowerSeries σ R) where
  carrier := {f | IsRestricted c f}
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

variable [IsUltrametricDist R]

/-- Restricted power series as a subring of `MvPowerSeries σ R`. -/
protected def subring (c : σ → ℝ) : Subring (MvPowerSeries σ R) where
  __ := IsRestricted.addSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

end IsRestricted

lemma isRestricted.sub (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f - g) :=
  show f - g ∈ IsRestricted.addSubgroup c from sub_mem hf hg

lemma isRestricted.sum (c : σ → ℝ) {ι : Type*} {s : Finset ι} {f : ι → MvPowerSeries σ R}
    (hf : ∀ i ∈ s, IsRestricted c (f i)) : IsRestricted c (∑ i ∈ s, f i) :=
  show ∑ i ∈ s, f i ∈ IsRestricted.addSubgroup c from sum_mem hf

lemma isRestricted.pow [IsUltrametricDist R] (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (n : ℕ) : IsRestricted c (f ^ n) :=
  show f ^ n ∈ IsRestricted.subring c from pow_mem hf n


variable [IsUltrametricDist R]

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : σ → ℝ) : Type _ := MvPowerSeries.IsRestricted.subring (R := R) c

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : σ → ℝ) : Ring (Restricted R c) :=
  Subring.toRing (MvPowerSeries.IsRestricted.subring c)

/-- Commutative ring structure on `Restricted R c` when `R` is commutative. -/
noncomputable instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] (c : σ → ℝ) :
    CommRing (Restricted S c) :=
  { (inferInstance : Ring (Restricted S c)) with
    mul_comm := fun f g ↦ Subtype.ext (mul_comm f.1 g.1) }

namespace Restricted

@[ext]
lemma ext {c : σ → ℝ} {f g : Restricted R c} (h : f.1 = g.1) : f = g := Subtype.ext h

variable (c : σ → ℝ)

@[simp]
lemma val_zero : (0 : Restricted R c).1 = 0 := rfl

@[simp]
lemma val_one : (1 : Restricted R c).1 = 1 := rfl

@[simp]
lemma val_add (f g : Restricted R c) : (f + g).1 = f.1 + g.1 := rfl

@[simp]
lemma val_neg (f : Restricted R c) : (-f).1 = -f.1 := rfl

@[simp]
lemma val_sub (f g : Restricted R c) : (f - g).1 = f.1 - g.1 := rfl

@[simp]
lemma val_mul (f g : Restricted R c) : (f * g).1 = f.1 * g.1 := rfl

@[simp]
lemma val_pow (f : Restricted R c) (n : ℕ) : (f ^ n).1 = f.1 ^ n := rfl

@[simp]
lemma val_sum {ι : Type*} (s : Finset ι) (g : ι → Restricted R c) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, val_add, ih]

/-- `MvPowerSeries.monomial n a` as an element of `Restricted R c`. -/
noncomputable
def monomial (n : σ →₀ ℕ) (a : R) : Restricted R c :=
  ⟨MvPowerSeries.monomial n a, isRestricted_monomial c n a⟩

@[simp]
lemma val_monomial (n : σ →₀ ℕ) (a : R) : (monomial c n a).1 = MvPowerSeries.monomial n a := rfl

variable (R) in
/-- `MvPowerSeries.X s` as an element of `Restricted R c`. -/
noncomputable def X (s : σ) : Restricted R c := ⟨MvPowerSeries.X s, isRestricted_X c s⟩

@[simp]
lemma val_X (s : σ) : (X R c s).1 = MvPowerSeries.X s := rfl

/-- The constant `MvPowerSeries.C a` as an element of `Restricted R c`, bundled as a ring
homomorphism. -/
noncomputable
def C : R →+* Restricted R c :=
  RingHom.codRestrict MvPowerSeries.C (IsRestricted.subring c) (isRestricted_C c)

@[simp]
lemma val_C (a : R) : (C c a).1 = MvPowerSeries.C a := rfl

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

/-- The map between restricted power series induced by a map on the coefficients. -/
noncomputable
def map {φ : R →+* S} (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) :
    Restricted R c →+* Restricted S c :=
  RingHom.codRestrict ((MvPowerSeries.map φ).comp (IsRestricted.subring c).subtype)
    (IsRestricted.subring c) fun f ↦ isRestricted_map c _ C hφ f.2

@[simp]
lemma val_map {φ : R →+* S} (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (f : Restricted R c) :
    (map c C hφ f).1 = MvPowerSeries.map φ f.1 := rfl

lemma map_injective {φ : R →+* S} (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)
    (hφinj : Function.Injective φ) : Function.Injective (map c C hφ) := fun a b h ↦
  Restricted.ext <| MvPowerSeries.ext fun t ↦ hφinj <| by
    simpa only [val_map, MvPowerSeries.coeff_map] using
      congrArg (fun r : Restricted S c ↦ MvPowerSeries.coeff t r.1) h

/-- A version of `MvPowerSeries.Restricted.map` where we take `π` only being additve (not
neccesarily multiplicative), this gives an additive map between restricted power series. -/
noncomputable def mapRetraction (π : S →+ R) {C : ℝ} (hC : ∀ x, ‖π x‖ ≤ C * ‖x‖) :
    Restricted S c →+ Restricted R c where
  toFun A := ⟨fun t ↦ π (coeff t A.1), isRestricted_map c π C hC A.2⟩
  map_zero' := Restricted.ext (MvPowerSeries.ext fun t ↦ by aesop)
  map_add' A B := Restricted.ext (MvPowerSeries.ext fun t ↦ by aesop)

@[simp]
lemma val_mapRetraction (π : S →+ R) {C : ℝ} (hC : ∀ x, ‖π x‖ ≤ C * ‖x‖)
    (A : Restricted S c) : (mapRetraction c π hC A).1 = fun t ↦ π (coeff t A.1) := rfl

end Restricted

end MvPowerSeries

namespace MvPolynomial

variable {R : Type*} [NormedCommRing R] {σ : Type*}

lemma isRestricted (c : σ → ℝ) (p : MvPolynomial σ R) :
    MvPowerSeries.IsRestricted c (p : MvPowerSeries σ R) :=
  MvPowerSeries.isRestricted_of_finite_support c <| p.support.finite_toSet.subset fun t ht ↦ by
    simpa [mem_support_iff, coeff_coe] using Function.mem_support.mp ht

variable [IsUltrametricDist R] (c : σ → ℝ)

/-- The map from multivariate polynomials to restricted power series. -/
noncomputable
def toRestricted : MvPolynomial σ R →+* MvPowerSeries.Restricted R c :=
  RingHom.codRestrict coeToMvPowerSeries.ringHom (MvPowerSeries.IsRestricted.subring c)
    fun p ↦ isRestricted c p

@[simp]
lemma val_toRestricted (p : MvPolynomial σ R) : (toRestricted c p).1 = (p : MvPowerSeries σ R) :=
  rfl

@[simp]
lemma toRestricted_monomial (n : σ →₀ ℕ) (a : R) :
    toRestricted c (monomial n a) = MvPowerSeries.Restricted.monomial c n a :=
  MvPowerSeries.Restricted.ext (by simp [coe_monomial])

@[simp]
lemma toRestricted_X (s : σ) : toRestricted c (X s) = MvPowerSeries.Restricted.X R c s :=
  MvPowerSeries.Restricted.ext (by simp [coe_X])

@[simp]
lemma toRestricted_C (a : R) : toRestricted c (C a) = MvPowerSeries.Restricted.C c a :=
  MvPowerSeries.Restricted.ext (by simp [coe_C])

lemma toRestricted_injective : Function.Injective (toRestricted (R := R) c) :=
  fun _ _ h ↦ coe_injective σ R (congrArg Subtype.val h)

@[simp]
lemma toRestricted_inj {p q : MvPolynomial σ R} : toRestricted c p = toRestricted c q ↔ p = q :=
  (toRestricted_injective c).eq_iff

@[simp]
lemma toRestricted_eq_zero_iff {p : MvPolynomial σ R} : toRestricted c p = 0 ↔ p = 0 :=
  (toRestricted_injective c).eq_iff' (map_zero _)

@[simp]
lemma toRestricted_eq_one_iff {p : MvPolynomial σ R} : toRestricted c p = 1 ↔ p = 1 :=
  (toRestricted_injective c).eq_iff' (map_one _)

end MvPolynomial
