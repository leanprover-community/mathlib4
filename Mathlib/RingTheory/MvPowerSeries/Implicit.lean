/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.MvPowerSeries.LinearMap
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The formal implicit function theorem for infinitely many equations

Let `F(X, Y)` be a family of power series with `F(0, 0) = 0`, where the variables `X`, `Y` and
the equations are indexed by possibly infinite types `σ`, `τ`, `ι`, and every monomial occurs in
only finitely many `Fᵢ`. Consider the Jacobian `implicitJacobian F hF : (τ →₀ R) →ₗ[R] (ι →₀ R)`.

* If the Jacobian is surjective, then `F(X, α(X)) = 0` has a substitutable solution `α` with
  `α(0) = 0`, namely `implicitFunction F hF hJ`.
* If the Jacobian is moreover injective, then this is the only such solution.

## Main results

* `MvPowerSeries.subst_implicitFunction`: existence, for a surjective Jacobian.
* `MvPowerSeries.eq_implicitFunction`: uniqueness, for a bijective Jacobian.
* `MvPowerSeries.bijective_implicitJacobian_of_isUnit` and
  `MvPowerSeries.bijective_implicitJacobian_of_isUnit_det`: in the finite-dimensional case, an
  invertible Jacobian matrix, or a Jacobian determinant that is a unit, gives a bijective Jacobian.
-/

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ : Type*}

/-! ### Coefficientwise fixed points

If `T` preserves admissible families (substitutable, with zero constant coefficients) and raises
the order of the difference of two admissible families by one, then `iterLimit T` is an
admissible fixed point of `T`. -/

section FixedPoint

variable (T : (ι → MvPowerSeries τ R) → ι → MvPowerSeries τ R)

def iterLimit (i : ι) : MvPowerSeries τ R :=
  fun d ↦ coeff d ((T^[d.degree + 1]) 0 i)

variable (hT0 : ∀ a, (HasSubst a ∧ ∀ i, constantCoeff (a i) = 0) →
  HasSubst (T a) ∧ ∀ i, constantCoeff (T a i) = 0)

include hT0

theorem iterate_admissible (n : ℕ) :
    HasSubst ((T^[n]) 0) ∧ ∀ i, constantCoeff ((T^[n]) 0 i) = 0 := by
  induction n with
  | zero => simp [hasSubst_def]
  | succ n ih =>
    rw [iterate_succ_apply']
    exact hT0 _ ih

theorem iterLimit_admissible :
    HasSubst (iterLimit T) ∧ ∀ i, constantCoeff (iterLimit T i) = 0 := by
  have h0 (i : ι) : constantCoeff (iterLimit T i) = 0 := by
    simpa [iterLimit, ← coeff_zero_eq_constantCoeff_apply, coeff_apply] using
      (iterate_admissible T hT0 1).2 i
  exact ⟨⟨fun i ↦ by simp [h0 i], fun d ↦ (iterate_admissible T hT0 (d.degree + 1)).1.coeff_zero d⟩,
    h0⟩

variable (hT : ∀ (n : ℕ) a b, (HasSubst a ∧ (∀ i, constantCoeff (a i) = 0)) →
  (HasSubst b ∧ (∀ i, constantCoeff (b i) = 0)) →
  (∀ i, (n : ℕ∞) ≤ (a i - b i).order) →
  ∀ i, ((n + 1 : ℕ) : ℕ∞) ≤ (T a i - T b i).order)

include hT

theorem le_order_iterate_sub (m k : ℕ) (i : ι) :
    k ≤ ((T^[m + k]) 0 i - (T^[k]) 0 i).order := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iterate_succ_apply', iterate_succ_apply']
    exact hT k _ _ (iterate_admissible T hT0 _) (iterate_admissible T hT0 _) ih i

theorem le_order_iterLimit_sub (n : ℕ) (i : ι) :
    n ≤ (iterLimit T i - (T^[n]) 0 i).order := by
  refine nat_le_order fun d hd ↦ ?_
  rw [map_sub, sub_eq_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  exact (coeff_eq_of_lt_order_sub
    ((Nat.cast_lt.mpr (lt_add_one _)).trans_le (le_order_iterate_sub T hT0 hT m _ i))).symm

theorem map_iterLimit : T (iterLimit T) = iterLimit T := by
  funext i
  ext d
  have h := hT _ _ _ (iterLimit_admissible T hT0) (iterate_admissible T hT0 _)
    (le_order_iterLimit_sub T hT0 hT (d.degree + 1)) i
  rw [← iterate_succ_apply' T] at h
  rw [coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr (by omega)).trans_le h),
    coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr (by omega)).trans_le
      (le_order_iterLimit_sub T hT0 hT (d.degree + 1 + 1) i))]

end FixedPoint

/-! ### Jacobians -/

section Jacobian

variable (F : ι → MvPowerSeries (σ ⊕ τ) R) (hF : HasSubst F)

/-- The Jacobian of `F` in the second variable block, as a linear map: `eⱼ` is sent to the
vector of coefficients of `Yⱼ` in the `Fᵢ`. -/
@[expose] public def implicitJacobian : (τ →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.linearCombination R fun j ↦ vecCoeff F hF.coeff_zero (single (Sum.inr j) 1)

variable {F}

public theorem implicitJacobian_single (j : τ) (r : R) :
    implicitJacobian F hF (single j r) =
      r • vecCoeff F hF.coeff_zero (single (Sum.inr j) 1) :=
  Finsupp.linearCombination_single ..

@[simp]
public theorem implicitJacobian_single_one_apply (j : τ) (i : ι) :
    implicitJacobian F hF (single j 1) i = coeff (single (Sum.inr j) 1) (F i) := by
  simp [implicitJacobian_single]

public theorem implicitJacobian_apply (v : τ →₀ R) (i : ι) :
    implicitJacobian F hF v i = v.sum fun j r ↦ coeff (single (Sum.inr j) 1) (F i) * r := by
  simp [implicitJacobian, Finsupp.linearCombination_apply, Finsupp.sum_apply, mul_comm]

end Jacobian

/-! ### The implicit function theorem

Write `J` for the Jacobian `implicitJacobian F hF`. If a power series has no linear terms in `Y`,
then substituting `(X, a)` and `(X, b)` with `a - b` of order `n` gives results that agree up to
order `n + 1`. This one estimate gives both halves of the theorem.

* Existence only needs `J` to be surjective. For a right inverse `K` of `J`, the step map
  `T a = (K J)(a) - (K F)(X, a)` has no linear terms in `Y`, so it is a contraction. Applying `J`
  to `T a = a` gives `F(X, a) = 0`.
* Uniqueness needs `J` to be injective. `J Y - F` has no linear terms in `Y`, so
  `F(X, a) = F(X, b)` forces `J a` and `J b`, hence `a` and `b`, to agree one degree further. -/

section Implicit

variable {F : ι → MvPowerSeries (σ ⊕ τ) R} (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  {a b : τ → MvPowerSeries σ R}

theorem vecCoeff_X_inr (k : τ) : vecCoeff (X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R)
    (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero (single (Sum.inr k) 1) =
      single k 1 := by
  classical
  ext j
  simp [coeff_index_single_X, Finsupp.single_apply]

theorem subst_mapVecCoeff_X_inr (L : (τ →₀ R) →ₗ[R] (ι →₀ R)) (ha : HasSubst a) (i : ι) :
    (mapVecCoeff L (X ∘ Sum.inr) (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero
      i).subst (Sum.elim X a) = mapVecCoeff L a ha.coeff_zero i := by
  rw [subst_mapVecCoeff L (HasSubst.X.comp_injective Sum.inr_injective)
    (HasSubst.X.sumElim ha) i]
  congr 1
  funext j
  simp [subst_X (HasSubst.X.sumElim ha)]

/-- If `f` has no linear terms in `Y`, then substituting `(X, a)` and `(X, b)` for families `a`, `b`
that agree up to order `n` gives power series that agree up to order `n + 1`. -/
theorem le_order_subst_sumElim_sub_subst {f : MvPowerSeries (σ ⊕ τ) R}
    (hf : ∀ k, coeff (single (Sum.inr k) 1) f = 0) (n : ℕ)
    (ha : HasSubst a ∧ ∀ j, constantCoeff (a j) = 0)
    (hb : HasSubst b ∧ ∀ j, constantCoeff (b j) = 0) (h : ∀ j, n ≤ (a j - b j).order) :
    n + 1 ≤ (f.subst (Sum.elim X a) - f.subst (Sum.elim X b)).order := by
  refine add_le_order_subst_sub_subst f (HasSubst.X.sumElim ha.1) (HasSubst.X.sumElim hb.1)
    (fun s ↦ ?_) (fun s ↦ ?_) (by simp [h]) (by rintro (s | k) <;> simp [hf])
  · exact one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [ha.2])
  · exact one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [hb.2])

section Existence

variable (hJ : Surjective (implicitJacobian F hF))

variable (F) in
/-- The implicit function, an explicit solution `α` of `F(X, α(X)) = 0` when the Jacobian `J` is
surjective. -/
@[expose] public def implicitFunction (j : τ) : MvPowerSeries σ R :=
  /- Let `K` be a right inverse of `J` and `T a = (K J)(a) - (K F)(X, a)`. The coefficient
    of `X^d` in `α` is the coefficient of `X^d` in `T^[deg d + 1] 0`. -/
  fun d ↦ coeff d (((fun a j ↦
    (mapVecCoeff (LinearMap.splittingOfFinsuppSurjective _ hJ ∘ₗ implicitJacobian F hF)
        (X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R)
        (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero j -
      mapVecCoeff (LinearMap.splittingOfFinsuppSurjective _ hJ) F hF.coeff_zero j).subst
      (Sum.elim X a))^[d.degree + 1]) 0 j)

variable (F) in
/-- The step map `a ↦ (K J)(a) - (K F)(X, a)`, written as a substitution so that it is defined
on all families. -/
def implicitStep (K : (ι →₀ R) →ₗ[R] (τ →₀ R)) (a : τ → MvPowerSeries σ R) (j : τ) :
    MvPowerSeries σ R :=
  (mapVecCoeff (K ∘ₗ implicitJacobian F hF) (X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R)
      (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero j -
    mapVecCoeff K F hF.coeff_zero j).subst (Sum.elim X a)

theorem implicitFunction_apply : implicitFunction F hF hJ =
    iterLimit (implicitStep F hF (LinearMap.splittingOfFinsuppSurjective _ hJ)) :=
  rfl

variable {K : (ι →₀ R) →ₗ[R] (τ →₀ R)}

include hF0 in
theorem implicitStep_admissible (ha : HasSubst a ∧ ∀ j, constantCoeff (a j) = 0) :
    HasSubst (implicitStep F hF K a) ∧ ∀ j, constantCoeff (implicitStep F hF K a j) = 0 := by
  have hp := HasSubst.X.sumElim ha.1
  have hX0 (j : τ) : constantCoeff ((X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R) j) = 0 := by
    simp
  refine ⟨((HasSubst.mapVecCoeff _ (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero
    hX0).sub (HasSubst.mapVecCoeff K hF.coeff_zero hF0)).subst hp, fun j ↦ ?_⟩
  refine constantCoeff_subst_eq_zero hp (by rintro (s | t) <;> simp [ha.2]) ?_
  rw [map_sub, constantCoeff_mapVecCoeff _ _ hX0, constantCoeff_mapVecCoeff _ _ hF0,
    sub_zero]

theorem implicitStep_contract (n : ℕ) (ha : HasSubst a ∧ ∀ j, constantCoeff (a j) = 0)
    (hb : HasSubst b ∧ ∀ j, constantCoeff (b j) = 0) (h : ∀ j, n ≤ (a j - b j).order) (j : τ) :
    n + 1 ≤ (implicitStep F hF K a j - implicitStep F hF K b j).order := by
  refine le_order_subst_sumElim_sub_subst (fun k ↦ ?_) n ha hb h
  rw [map_sub, coeff_mapVecCoeff, coeff_mapVecCoeff, vecCoeff_X_inr,
    LinearMap.comp_apply, implicitJacobian_single, one_smul, sub_self]

theorem implicitStep_eq (ha : HasSubst a) (j : τ) :
    implicitStep F hF K a j = mapVecCoeff (K ∘ₗ implicitJacobian F hF) a ha.coeff_zero j -
      mapVecCoeff K (fun i ↦ (F i).subst (Sum.elim X a))
        (hF.subst (HasSubst.X.sumElim ha)).coeff_zero j := by
  rw [implicitStep, subst_sub (HasSubst.X.sumElim ha), subst_mapVecCoeff_X_inr _ ha,
    subst_mapVecCoeff K hF (HasSubst.X.sumElim ha)]

include hF0 hJ

@[simp]
public theorem constantCoeff_implicitFunction (j : τ) :
    constantCoeff (implicitFunction F hF hJ j) = 0 := by
  rw [implicitFunction_apply]
  exact (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF ha).2 j

public theorem HasSubst.implicitFunction : HasSubst (implicitFunction F hF hJ) := by
  rw [implicitFunction_apply]
  exact (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF ha).1

/-- **Implicit functions theorem**: if the Jacobian is surjective, then `implicitFunction`
solves `F(X, α(X)) = 0`. -/
@[simp]
public theorem subst_implicitFunction (i : ι) :
    (F i).subst (Sum.elim X (implicitFunction F hF hJ)) = 0 := by
  -- `implicitFunction` is a fixed point `a` of the step map `T`. Since `K` is a right inverse of
  -- `J`, applying `J` to `T a = a` gives `F(X, a) = 0`.
  have hJK : ∀ v, implicitJacobian F hF (LinearMap.splittingOfFinsuppSurjective _ hJ v) = v :=
    LinearMap.leftInverse_splittingOfFinsuppSurjective _ hJ
  have ha := HasSubst.implicitFunction hF0 hF hJ
  rw [implicitFunction_apply] at ha ⊢
  have hfix := map_iterLimit (implicitStep F hF (LinearMap.splittingOfFinsuppSurjective _ hJ))
    (fun _ ha ↦ implicitStep_admissible hF0 hF ha)
    (fun n _ _ ha hb h ↦ implicitStep_contract hF n ha hb h)
  generalize LinearMap.splittingOfFinsuppSurjective _ hJ = K at hJK ha hfix ⊢
  generalize iterLimit (implicitStep F hF K) = a at ha hfix ⊢
  ext d
  have h : K (implicitJacobian F hF (vecCoeff a ha.coeff_zero d)) -
      K (vecCoeff _ (hF.subst (HasSubst.X.sumElim ha)).coeff_zero d) =
      vecCoeff a ha.coeff_zero d := by
    ext j
    simpa [implicitStep_eq hF ha, coeff_mapVecCoeff] using
      congrArg (coeff d) (congrFun hfix j)
  have := congrArg (implicitJacobian F hF) h
  rw [map_sub, hJK, hJK, sub_eq_self] at this
  simpa using DFunLike.congr_fun this i

end Existence

section Bijective

variable (hJ : Bijective (implicitJacobian F hF))

include hF0 hJ

/-- **Uniqueness of implicit functions**: if the Jacobian is moreover injective, then
`implicitFunction` is the unique solution: every substitutable family `a` with zero constant
coefficients and `F(X, a) = 0` equals it. -/
public theorem eq_implicitFunction (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim X a) = 0) :
    a = implicitFunction F hF hJ.2 := by
  have hb := HasSubst.implicitFunction hF0 hF hJ.2
  have hb0 := constantCoeff_implicitFunction hF0 hF hJ.2
  have hab (i : ι) := (h i).trans (subst_implicitFunction hF0 hF hJ.2 i).symm
  generalize implicitFunction F hF hJ.2 = b at hb hb0 hab ⊢
  have hlin (i : ι) (k : τ) : coeff (single (Sum.inr k) 1) (mapVecCoeff (implicitJacobian F hF)
      (X ∘ Sum.inr) (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero i - F i) = 0 := by
    simp [coeff_mapVecCoeff, vecCoeff_X_inr]
  have key (n : ℕ) : ∀ j, (n : ℕ∞) ≤ (a j - b j).order := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc (d : σ →₀ ℕ) (hd : d.degree < n + 1) :
          vecCoeff a ha.coeff_zero d = vecCoeff b hb.coeff_zero d := by
        refine hJ.1 (Finsupp.ext fun i ↦ ?_)
        have := le_order_subst_sumElim_sub_subst (hlin i) n ⟨ha, ha0⟩ ⟨hb, hb0⟩ ih
        rw [subst_sub (HasSubst.X.sumElim ha), subst_sub (HasSubst.X.sumElim hb), hab i,
          sub_sub_sub_cancel_right, subst_mapVecCoeff_X_inr _ ha,
          subst_mapVecCoeff_X_inr _ hb] at this
        exact coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr hd).trans_le this)
      intro j
      refine nat_le_order fun d hd ↦ ?_
      rw [map_sub, sub_eq_zero]
      exact congr($(hc d hd) j)
  funext j
  ext d
  exact coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr (lt_add_one _)).trans_le (key _ j))

end Bijective

end Implicit

/-! ### Finite-dimensional case

In this section we deduce the classical version of the formal implicit function theorem. Consider
finitely many power series `F(X, Y)`, indexed by the same finite type `τ` as the variables `Y`.
The Jacobian `implicitJacobian F hF` is then given by a square matrix, whose `(i, j)` entry is the
coefficient of `Yⱼ` in `Fᵢ`. If this matrix is invertible, or equivalently its determinant is a
unit in `R`, then the Jacobian is bijective. Hence, by `subst_implicitFunction` and
`eq_implicitFunction`, `implicitFunction` is the unique substitutable solution `α` of
`F(X, α(X)) = 0` with `α(0) = 0`.

Note that the variables `X` may still be indexed by an infinite type `σ`. -/

section Finite

variable [Fintype τ] [DecidableEq τ] {F : τ → MvPowerSeries (σ ⊕ τ) R} (hF : HasSubst F)

/-- The Jacobian is bijective if its matrix is invertible. -/
public theorem bijective_implicitJacobian_of_isUnit
    (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i))) :
    Bijective (implicitJacobian F hF) := by
  have h : LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne (implicitJacobian F hF) =
      Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i) := by
    ext i j
    simp [LinearMap.toMatrixAlgEquiv_apply]
  rw [← h, isUnit_map_iff] at hJ
  exact (Module.End.isUnit_iff _).mp hJ

/-- The Jacobian is bijective if its determinant is a unit. -/
public theorem bijective_implicitJacobian_of_isUnit_det
    (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i)).det) :
    Bijective (implicitJacobian F hF) :=
  bijective_implicitJacobian_of_isUnit hF ((Matrix.isUnit_iff_isUnit_det _).mpr hJ)

end Finite

end MvPowerSeries
