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
* If the Jacobian is injective, then there is at most one such solution.

## Main results

* `MvPowerSeries.subst_implicitFunction`: existence, for a surjective Jacobian.
* `MvPowerSeries.eq_of_subst_eq_subst`: uniqueness, for an injective Jacobian.
* `MvPowerSeries.eq_implicitFunction`: every solution equals `implicitFunction`, for a bijective
  Jacobian.
* `MvPowerSeries.subst_implicitFunctionLeft` and `MvPowerSeries.eq_implicitFunctionLeft`: existence
  and uniqueness, solving for the first variable block.
* `MvPowerSeries.bijective_implicitJacobian_of_isUnit_det`: an invertible Jacobian determinant
  gives a bijective Jacobian for finitely many equations.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ υ : Type*}

/-! ### Coefficientwise fixed points

If `T` preserves admissible families (substitutable, with zero constant coefficients) and raises
the order of the difference of two admissible families by one, then `iterLimit T` is an
admissible fixed point of `T`. -/

section FixedPoint

variable (T : (ι → MvPowerSeries τ R) → ι → MvPowerSeries τ R)

private def iterLimit (i : ι) : MvPowerSeries τ R :=
  fun d ↦ coeff d ((T^[d.degree + 1]) 0 i)

variable (hT0 : ∀ a, (HasSubst a ∧ ∀ i, constantCoeff (a i) = 0) →
  HasSubst (T a) ∧ ∀ i, constantCoeff (T a i) = 0)

include hT0

private theorem iterate_admissible (n : ℕ) :
    HasSubst ((T^[n]) 0) ∧ ∀ i, constantCoeff ((T^[n]) 0 i) = 0 := by
  induction n with
  | zero => simp [hasSubst_def]
  | succ n ih =>
    rw [iterate_succ_apply']
    exact hT0 _ ih

private theorem iterLimit_admissible :
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

private theorem le_order_iterate_sub (m k : ℕ) (i : ι) :
    k ≤ ((T^[m + k]) 0 i - (T^[k]) 0 i).order := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iterate_succ_apply', iterate_succ_apply']
    exact hT k _ _ (iterate_admissible T hT0 _) (iterate_admissible T hT0 _) ih i

private theorem le_order_iterLimit_sub (n : ℕ) (i : ι) :
    n ≤ (iterLimit T i - (T^[n]) 0 i).order := by
  refine nat_le_order fun d hd ↦ ?_
  rw [map_sub, sub_eq_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  exact (coeff_eq_of_lt_order_sub
    ((Nat.cast_lt.mpr (lt_add_one _)).trans_le (le_order_iterate_sub T hT0 hT m _ i))).symm

private theorem map_iterLimit : T (iterLimit T) = iterLimit T := by
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
def implicitJacobian : (τ →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.linearCombination R fun j ↦ vecCoeff F hF.coeff_zero (single (Sum.inr j) 1)

variable {F}

theorem implicitJacobian_single (j : τ) (r : R) :
    implicitJacobian F hF (single j r) =
      r • vecCoeff F hF.coeff_zero (single (Sum.inr j) 1) :=
  Finsupp.linearCombination_single ..

@[simp]
theorem implicitJacobian_single_one_apply (j : τ) (i : ι) :
    implicitJacobian F hF (single j 1) i = coeff (single (Sum.inr j) 1) (F i) := by
  simp [implicitJacobian_single]

theorem implicitJacobian_apply (v : τ →₀ R) (i : ι) :
    implicitJacobian F hF v i = v.sum fun j r ↦ coeff (single (Sum.inr j) 1) (F i) * r := by
  simp [implicitJacobian, Finsupp.linearCombination_apply, Finsupp.sum_apply, mul_comm]

end Jacobian

section JacobianLeft

variable (F : ι → MvPowerSeries (τ ⊕ σ) R) (hF : HasSubst F)

/-- The Jacobian of `F` in the first variable block, as a linear map. -/
def implicitJacobianLeft : (τ →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.linearCombination R fun j ↦ vecCoeff F hF.coeff_zero (single (Sum.inl j) 1)

variable {F}

theorem implicitJacobianLeft_single (j : τ) (r : R) :
    implicitJacobianLeft F hF (single j r) =
      r • vecCoeff F hF.coeff_zero (single (Sum.inl j) 1) :=
  Finsupp.linearCombination_single ..

@[simp]
theorem implicitJacobianLeft_single_one_apply (j : τ) (i : ι) :
    implicitJacobianLeft F hF (single j 1) i = coeff (single (Sum.inl j) 1) (F i) := by
  simp [implicitJacobianLeft_single]

include hF in
theorem HasSubst.rename_sumComm : HasSubst fun i ↦ rename (Equiv.sumComm τ σ) (F i) := by
  simpa only [rename_eq_subst] using hF.subst (HasSubst.X_comp (Equiv.sumComm τ σ))

@[simp]
theorem implicitJacobian_rename_sumComm :
    implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm =
      implicitJacobianLeft F hF := by
  ext j i
  simpa using
    coeff_embDomain_rename (Equiv.sumComm τ σ).toEmbedding (F i) (single (Sum.inl j) 1)

variable {hF}

theorem surjective_implicitJacobian_rename_sumComm (hJ : Surjective (implicitJacobianLeft F hF)) :
    Surjective (implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm) := by
  rwa [implicitJacobian_rename_sumComm]

theorem injective_implicitJacobian_rename_sumComm (hJ : Injective (implicitJacobianLeft F hF)) :
    Injective (implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm) := by
  rwa [implicitJacobian_rename_sumComm]

end JacobianLeft

/-! ### The implicit function theorem

Write `J` for the Jacobian `implicitJacobian F hF`. If a power series has no linear terms in `Y`,
then substituting `(X, a)` and `(X, b)` with `a - b` of order `n` gives results that agree up to
order `n + 1`. This one estimate gives both halves of the theorem.

* Uniqueness only needs `J` to be injective. `J Y - F` has no linear terms in `Y`, so
  `F(X, a) = F(X, b)` forces `J a` and `J b`, hence `a` and `b`, to agree one degree further.
* Existence only needs `J` to be surjective. For a right inverse `K` of `J`, the step map
  `T a = (K J)(a) - (K F)(X, a)` has no linear terms in `Y`, so it is a contraction. Applying `J`
  to `T a = a` gives `F(X, a) = 0`. -/

section Implicit

variable {F : ι → MvPowerSeries (σ ⊕ τ) R} (hF0 : ∀ i, constantCoeff (F i) = 0)
  (hF : HasSubst F)

private theorem vecCoeff_X_inr (k : τ) :
    vecCoeff (X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R)
      (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero (single (Sum.inr k) 1) =
      single k 1 := by
  classical
  ext j
  simp [coeff_index_single_X, Finsupp.single_apply]

private theorem subst_mapVecCoeff_X_inr (L : (τ →₀ R) →ₗ[R] (ι →₀ R))
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) (i : ι) :
    (mapVecCoeff L (X ∘ Sum.inr) (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero
      i).subst (Sum.elim X a) = mapVecCoeff L a ha.coeff_zero i := by
  rw [subst_mapVecCoeff L (HasSubst.X.comp_injective Sum.inr_injective)
    (HasSubst.X.sumElim ha) i]
  congr 1
  funext j
  simp [subst_X (HasSubst.X.sumElim ha)]

/-- If `f` has no linear terms in `Y`, then substituting `(X, a)` and `(X, b)` for families `a`, `b`
that agree up to order `n` gives power series that agree up to order `n + 1`. -/
private theorem le_order_subst_sub_subst {f : MvPowerSeries (σ ⊕ τ) R}
    (hf : ∀ k, coeff (single (Sum.inr k) 1) f = 0) (n : ℕ) {a b : τ → MvPowerSeries σ R}
    (ha : HasSubst a ∧ ∀ j, constantCoeff (a j) = 0)
    (hb : HasSubst b ∧ ∀ j, constantCoeff (b j) = 0) (h : ∀ j, n ≤ (a j - b j).order) :
    n + 1 ≤ (f.subst (Sum.elim X a) - f.subst (Sum.elim X b)).order := by
  refine add_le_order_subst_sub (HasSubst.X.sumElim ha.1) (HasSubst.X.sumElim hb.1)
    (fun s ↦ ?_) (fun s ↦ ?_) (by simp [h]) ?_
  · exact one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [ha.2])
  · exact one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [hb.2])
  rintro (s | k) hs
  · simp at hs
  · exact hf k

/-! #### Uniqueness -/

/-- **Uniqueness of implicit functions**: if the Jacobian is injective, then `F(X, a) = F(X, b)`
implies `a = b` for substitutable families `a`, `b` with zero constant coefficients. -/
theorem eq_of_subst_eq_subst (hJ : Injective (implicitJacobian F hF))
    {a b : τ → MvPowerSeries σ R} (ha : HasSubst a) (ha0 : ∀ j, constantCoeff (a j) = 0)
    (hb : HasSubst b) (hb0 : ∀ j, constantCoeff (b j) = 0)
    (h : ∀ i, (F i).subst (Sum.elim X a) = (F i).subst (Sum.elim X b)) : a = b := by
  have hlin (i : ι) (k : τ) : coeff (single (Sum.inr k) 1)
      (mapVecCoeff (implicitJacobian F hF) (X ∘ Sum.inr)
        (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero i - F i) = 0 := by
    rw [map_sub, coeff_mapVecCoeff, vecCoeff_X_inr, implicitJacobian_single_one_apply,
      sub_self]
  have key (n : ℕ) : ∀ j, (n : ℕ∞) ≤ (a j - b j).order := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc (d : σ →₀ ℕ) (hd : d.degree < n + 1) :
          vecCoeff a ha.coeff_zero d = vecCoeff b hb.coeff_zero d := by
        refine hJ (Finsupp.ext fun i ↦ ?_)
        have := le_order_subst_sub_subst (hlin i) n ⟨ha, ha0⟩ ⟨hb, hb0⟩ ih
        rw [subst_sub (HasSubst.X.sumElim ha), subst_sub (HasSubst.X.sumElim hb), h i,
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

/-! #### Existence -/

section Existence

variable (hJ : Surjective (implicitJacobian F hF))

variable (F) in
/-- The implicit function, an explicit solution `α` of `F(X, α(X)) = 0` when the Jacobian `J` is
surjective. -/
def implicitFunction (j : τ) : MvPowerSeries σ R :=
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
private def implicitStep (K : (ι →₀ R) →ₗ[R] (τ →₀ R)) (a : τ → MvPowerSeries σ R) (j : τ) :
    MvPowerSeries σ R :=
  (mapVecCoeff (K ∘ₗ implicitJacobian F hF) (X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R)
      (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero j -
    mapVecCoeff K F hF.coeff_zero j).subst (Sum.elim X a)

private theorem implicitFunction_eq : implicitFunction F hF hJ =
    iterLimit (implicitStep F hF (LinearMap.splittingOfFinsuppSurjective _ hJ)) :=
  rfl

variable {K : (ι →₀ R) →ₗ[R] (τ →₀ R)}

include hF0 in
private theorem implicitStep_admissible {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a ∧ ∀ j, constantCoeff (a j) = 0) :
    HasSubst (implicitStep F hF K a) ∧ ∀ j, constantCoeff (implicitStep F hF K a j) = 0 := by
  have hp := HasSubst.X.sumElim ha.1
  have hX0 (j : τ) : constantCoeff ((X ∘ Sum.inr : τ → MvPowerSeries (σ ⊕ τ) R) j) = 0 := by
    simp
  refine ⟨((HasSubst.mapVecCoeff _ (HasSubst.X.comp_injective Sum.inr_injective).coeff_zero
    hX0).sub (HasSubst.mapVecCoeff K hF.coeff_zero hF0)).subst hp, fun j ↦ ?_⟩
  refine constantCoeff_subst_eq_zero hp (by rintro (s | t) <;> simp [ha.2]) ?_
  rw [map_sub, constantCoeff_mapVecCoeff _ _ hX0, constantCoeff_mapVecCoeff _ _ hF0,
    sub_zero]

private theorem implicitStep_contract (n : ℕ) {a b : τ → MvPowerSeries σ R}
    (ha : HasSubst a ∧ ∀ j, constantCoeff (a j) = 0)
    (hb : HasSubst b ∧ ∀ j, constantCoeff (b j) = 0) (h : ∀ j, n ≤ (a j - b j).order) (j : τ) :
    n + 1 ≤ (implicitStep F hF K a j - implicitStep F hF K b j).order := by
  refine le_order_subst_sub_subst (fun k ↦ ?_) n ha hb h
  rw [map_sub, coeff_mapVecCoeff, coeff_mapVecCoeff, vecCoeff_X_inr,
    LinearMap.comp_apply, implicitJacobian_single, one_smul, sub_self]

private theorem implicitStep_eq {a : τ → MvPowerSeries σ R} (ha : HasSubst a) (j : τ) :
    implicitStep F hF K a j = mapVecCoeff (K ∘ₗ implicitJacobian F hF) a ha.coeff_zero j -
      mapVecCoeff K (fun i ↦ (F i).subst (Sum.elim X a))
        (hF.subst (HasSubst.X.sumElim ha)).coeff_zero j := by
  rw [implicitStep, subst_sub (HasSubst.X.sumElim ha), subst_mapVecCoeff_X_inr _ ha,
    subst_mapVecCoeff K hF (HasSubst.X.sumElim ha)]

/-- A fixed point of the step map is a solution, as soon as `K` is a right inverse of `J`. -/
private theorem subst_eq_zero_of_implicitStep_eq (hJK : ∀ v, implicitJacobian F hF (K v) = v)
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) (hfix : implicitStep F hF K a = a) (i : ι) :
    (F i).subst (Sum.elim X a) = 0 := by
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

include hF0 hJ

@[simp]
theorem constantCoeff_implicitFunction (j : τ) :
    constantCoeff (implicitFunction F hF hJ j) = 0 := by
  rw [implicitFunction_eq]
  exact (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF ha).2 j

theorem HasSubst.implicitFunction : HasSubst (implicitFunction F hF hJ) := by
  rw [implicitFunction_eq]
  exact (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF ha).1

/-- **Existence of implicit functions**: if the Jacobian is surjective, then `implicitFunction`
solves `F(X, α(X)) = 0`. -/
@[simp]
theorem subst_implicitFunction (i : ι) :
    (F i).subst (Sum.elim X (implicitFunction F hF hJ)) = 0 := by
  have ha := HasSubst.implicitFunction hF0 hF hJ
  rw [implicitFunction_eq] at ha ⊢
  exact subst_eq_zero_of_implicitStep_eq hF
    (LinearMap.leftInverse_splittingOfFinsuppSurjective _ hJ) ha
    (map_iterLimit _ (fun _ ha ↦ implicitStep_admissible hF0 hF ha)
      (fun n _ _ ha hb h ↦ implicitStep_contract hF n ha hb h)) i

end Existence

/-! #### Bijective Jacobian -/

section Bijective

variable (hJ : Bijective (implicitJacobian F hF))

include hF0 hJ

theorem eq_implicitFunction (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim X a) = 0) :
    a = implicitFunction F hF hJ.2 :=
  eq_of_subst_eq_subst hF hJ.1 ha ha0 (HasSubst.implicitFunction hF0 hF hJ.2)
    (constantCoeff_implicitFunction hF0 hF hJ.2) fun i ↦ by
      rw [h, subst_implicitFunction hF0 hF hJ.2]

end Bijective

end Implicit

/-! ### Solving for the first variable block -/

section ImplicitLeft

private theorem subst_rename_sumComm_of_hasSubst (f : MvPowerSeries (τ ⊕ σ) R)
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) :
    (rename (Equiv.sumComm τ σ) f).subst (Sum.elim X a) = f.subst (Sum.elim a X) := by
  have hs := HasSubst.X.sumElim ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  ext (j | j) : 1 <;> simp [subst_X hs]

variable {F : ι → MvPowerSeries (τ ⊕ σ) R} (hF0 : ∀ i, constantCoeff (F i) = 0)
  (hF : HasSubst F)

/-- **Uniqueness** for `F(α(X), X) = 0`, for an injective Jacobian. -/
theorem eq_of_subst_eq_subst_left (hJ : Injective (implicitJacobianLeft F hF))
    {a b : τ → MvPowerSeries σ R} (ha : HasSubst a) (ha0 : ∀ j, constantCoeff (a j) = 0)
    (hb : HasSubst b) (hb0 : ∀ j, constantCoeff (b j) = 0)
    (h : ∀ i, (F i).subst (Sum.elim a X) = (F i).subst (Sum.elim b X)) : a = b :=
  eq_of_subst_eq_subst hF.rename_sumComm (injective_implicitJacobian_rename_sumComm hJ) ha ha0
    hb hb0 fun i ↦ by
      rw [subst_rename_sumComm_of_hasSubst _ ha, subst_rename_sumComm_of_hasSubst _ hb, h i]

section Existence

variable (hJ : Surjective (implicitJacobianLeft F hF))

variable (F) in
/-- The left implicit function, a solution `α` of `F(α(X), X) = 0` when the Jacobian is
surjective: the implicit function of `F` with its two variable blocks exchanged. -/
def implicitFunctionLeft : τ → MvPowerSeries σ R :=
  implicitFunction (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm
    (surjective_implicitJacobian_rename_sumComm hJ)

include hF0 hJ

@[simp]
theorem constantCoeff_implicitFunctionLeft (i : τ) :
    constantCoeff (implicitFunctionLeft F hF hJ i) = 0 :=
  constantCoeff_implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _ i

theorem HasSubst.implicitFunctionLeft : HasSubst (implicitFunctionLeft F hF hJ) :=
  HasSubst.implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _

/-- **Existence** for `F(α(X), X) = 0`, for a surjective Jacobian. -/
@[simp]
theorem subst_implicitFunctionLeft (i : ι) :
    (F i).subst (Sum.elim (implicitFunctionLeft F hF hJ) X) = 0 :=
  (subst_rename_sumComm_of_hasSubst _ (HasSubst.implicitFunctionLeft hF0 hF hJ)).symm.trans
    (subst_implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _ i)

end Existence

section Bijective

variable (hJ : Bijective (implicitJacobianLeft F hF))

include hF0 hJ

theorem eq_implicitFunctionLeft (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim a X) = 0) :
    a = implicitFunctionLeft F hF hJ.2 :=
  eq_of_subst_eq_subst_left hF hJ.1 ha ha0 (HasSubst.implicitFunctionLeft hF0 hF hJ.2)
    (constantCoeff_implicitFunctionLeft hF0 hF hJ.2) fun i ↦ by
      rw [h, subst_implicitFunctionLeft hF0 hF hJ.2]

end Bijective

end ImplicitLeft

/-! ### Finitely many equations -/

section Finite

variable [Fintype τ] [DecidableEq τ]

section

variable {F : τ → MvPowerSeries (σ ⊕ τ) R} (hF : HasSubst F)
  (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i)).det)

include hJ

/-- The Jacobian is bijective if its determinant is a unit. -/
theorem bijective_implicitJacobian_of_isUnit_det : Bijective (implicitJacobian F hF) := by
  have h : LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
      (implicitJacobian F hF) = Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← h] at hJ
  exact (LinearEquiv.ofIsUnitDet hJ).bijective

end

section

variable {F : τ → MvPowerSeries (τ ⊕ σ) R} (hF : HasSubst F)
  (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inl j) 1) (F i)).det)

include hJ

/-- The left Jacobian is bijective if its determinant is a unit. -/
theorem bijective_implicitJacobianLeft_of_isUnit_det : Bijective (implicitJacobianLeft F hF) := by
  have h : LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
      (implicitJacobianLeft F hF) = Matrix.of fun i j ↦ coeff (single (Sum.inl j) 1) (F i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← h] at hJ
  exact (LinearEquiv.ofIsUnitDet hJ).bijective

end

end Finite

end MvPowerSeries
