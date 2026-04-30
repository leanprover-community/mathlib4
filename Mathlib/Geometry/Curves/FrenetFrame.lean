/-
Copyright (c) 2026 Miraj Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miraj Samarakkody
-/
import Mathlib.Geometry.Curves.Basic

/-!
# Frenet frame of space curves
-/

namespace Curves
open scoped InnerProductSpace

/--
**Reference:** Do Carmo, *Differential Geometry of Curves & Surfaces*, §1-2. -/
structure ParametrizedDifferentiableCurve3 where
  /-- Left endpoint `a` of the open interval `(a, b)`. -/
  a : ℝ
  /-- Right endpoint `b` of the open interval `(a, b)`. -/
  b : ℝ
  /-- The interval is non-degenerate: `a < b`. -/
  hab : a < b
  /-- The curve map `α : ℝ → ℝ³`, evaluated on `(a, b)`. -/
  toFun : ℝ → ℝ^3
  /-- `α` is smooth (`C^∞`) on the open interval `(a, b)`. -/
  contDiffOn : ContDiffOn ℝ ⊤ toFun (Set.Ioo a b)

/-- A parametrized differentiable curve `α : I → ℝ³` is **regular** if `α'(t) ≠ 0`
for all `t ∈ (a, b)`. -/
def regularCurve3 (α : ParametrizedDifferentiableCurve3) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, deriv α.toFun t ≠ 0

/-- The arc length of `α` measured from `α.a` to `t`, defined by `s(t) = ∫_a^t ‖α'(u)‖ du`. -/
noncomputable def arcLength3 (α : ParametrizedDifferentiableCurve3) (t : ℝ) : ℝ :=
  ∫ u in α.a..t, ‖deriv α.toFun u‖

/-- `α` is **parametrized by arc length** if `‖α'(t)‖ = 1` for all `t ∈ (a, b)`. -/
def isArcLengthParametrized3 (α : ParametrizedDifferentiableCurve3) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, ‖deriv α.toFun t‖ = 1

/-- The **curvature** `κ(t) = ‖α''(t)‖` of a curve `α` parametrized by arc length. -/
@[nolint unusedArguments]
noncomputable def Curvature3
  (α : ParametrizedDifferentiableCurve3)
  (_h : isArcLengthParametrized3 α) (t : ℝ) : ℝ :=
    ‖deriv (deriv α.toFun) t‖

/-- The **unit tangent vector** `T(t) = α'(t)` of a curve `α` parametrized by arc length. -/
@[nolint unusedArguments]
noncomputable def curveTangent3 (α : ParametrizedDifferentiableCurve3)
    (_h : isArcLengthParametrized3 α) (t : ℝ) : ℝ^3 :=
    deriv α.toFun t

/-- The **principal normal vector** `N(t) = α''(t) / κ(t)` of a curve
  `α` parametrized by arc length. -/
noncomputable def curveNormal3 (α : ParametrizedDifferentiableCurve3)
    (_h : isArcLengthParametrized3 α) (t : ℝ) : ℝ^3 :=
  (1 / Curvature3 α _h t) • deriv (deriv α.toFun) t

/-- The **binormal vector** `B(t) = T(t) × N(t)` of a curve `α` parametrized by arc length. -/
noncomputable def curveBinormal3 (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ) : ℝ^3 :=
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  e.symm (crossProduct (e (curveTangent3 α h t)) (e (curveNormal3 α h t)))


/-- The **torsion** `τ(t) = ‖B'(t)‖` of a curve `α` parametrized by arc length. -/
noncomputable def Torsion3 (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ) : ℝ :=
  ‖deriv (curveBinormal3 α h) t‖

/-- The **Frenet trihedron** (moving frame) at a point on a curve, consisting of the
unit tangent `T`, principal normal `N`, and binormal `B` vectors. -/
structure FrenetFrame where
  /-- Unit tangent vector `T(t) = α'(t)`. -/
  tangent : ℝ^3
  /-- Principal normal vector `N(t) = α''(t) / κ(t)`. -/
  normal : ℝ^3
  /-- Binormal vector `B(t) = T(t) × N(t)`. -/
  binormal : ℝ^3

/-- The **Frenet trihedron** `{T(t), N(t), B(t)}` of a curve `α`
  parametrized by arc length at `t`. -/
noncomputable def frenetTrihedron (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ) : FrenetFrame where
  tangent  := curveTangent3 α h t
  normal   := curveNormal3 α h t
  binormal := curveBinormal3 α h t

/-! ## Frenet-Serret Formulas

For a curve `α` parametrized by arc length, the derivatives of the Frenet trihedron satisfy:
- `T'(t) = κ(t) · N(t)`
- `N'(t) = -κ(t) · T(t) + τ(t) · B(t)`
- `B'(t) = -τ(t) · N(t)`
-/

/-- **Frenet formula for T**: the derivative of the unit tangent is `κ(t) • N(t)`. -/
theorem derivTangent (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α)
    (t : ℝ) (hκ : Curvature3 α h t ≠ 0) :
    deriv (curveTangent3 α h) t = (Curvature3 α h) t • (curveNormal3 α h) t := by
  -- T'(s) = d/ds(α'(s)) = α''(s) by definition of curveTangent
  have lhs : deriv (curveTangent3 α h) t = deriv (deriv α.toFun) t := rfl
  -- κ(s) · N(s) = ‖α''(s)‖ · (1/‖α''(s)‖ · α''(s)) = α''(s)
  have rhs : Curvature3 α h t • curveNormal3 α h t = deriv (deriv α.toFun) t := by
    simp only [curveNormal3, Curvature3] at hκ ⊢
    simp only [smul_smul, mul_one_div_cancel hκ, one_smul]
  rw [lhs, rhs]

private lemma dot_tangent (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ) (ht : t ∈ Set.Ioo α.a α.b) :
    ⟪curveTangent3 α h t, curveTangent3 α h t⟫_ℝ = 1 := by
  simp only [curveTangent3]
  have h1 : ‖deriv α.toFun t‖ = 1 := h t ht
  rw [real_inner_self_eq_norm_sq, h1, one_pow]


private lemma orthogonality_tangent_normal (α : ParametrizedDifferentiableCurve3)
      (h : isArcLengthParametrized3 α) (t : ℝ) (ht : t ∈ Set.Ioo α.a α.b) :
    ⟪curveTangent3 α h t, curveNormal3 α h t⟫_ℝ = 0 := by
    simp only [curveTangent3, curveNormal3]
    rw [real_inner_smul_right]
    apply mul_eq_zero_of_right
    -- T is differentiable at t (from C^∞ of α)
    have hdiff : DifferentiableAt ℝ (curveTangent3 α h) t := by
      -- ContDiffOn ℝ ⊤ α implies ContDiffOn ℝ 1 (deriv α) on the open interval
      have hc : ContDiffOn ℝ 1 (deriv α.toFun) (Set.Ioo α.a α.b) :=
        α.contDiffOn.deriv_of_isOpen isOpen_Ioo le_top
      exact (hc.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds ht)
    -- Product rule: d/dt ⟪T, T⟫ = ⟪T, T'⟫ + ⟪T', T⟫  (order from HasDerivAt.inner)
    have hexp : deriv (fun s => ⟪curveTangent3 α h s, curveTangent3 α h s⟫_ℝ) t =
        ⟪curveTangent3 α h t, deriv (curveTangent3 α h) t⟫_ℝ +
        ⟪deriv (curveTangent3 α h) t, curveTangent3 α h t⟫_ℝ :=
      (HasDerivAt.inner (𝕜 := ℝ) hdiff.hasDerivAt hdiff.hasDerivAt).deriv
    -- ⟪T, T⟫ = 1 near t, so its derivative is 0
    have hzero : deriv (fun s => ⟪curveTangent3 α h s, curveTangent3 α h s⟫_ℝ) t = 0 := by
      have heq : (fun s => ⟪curveTangent3 α h s, curveTangent3 α h s⟫_ℝ) =ᶠ[nhds t] (fun _ => 1) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (dot_tangent α h)
      rw [heq.deriv_eq, deriv_const]
    -- So ⟪T, T'⟫ + ⟪T', T⟫ = 0
    have Dh : ⟪curveTangent3 α h t, deriv (curveTangent3 α h) t⟫_ℝ +
              ⟪deriv (curveTangent3 α h) t, curveTangent3 α h t⟫_ℝ = 0 := hexp ▸ hzero
    -- By symmetry ⟪T', T⟫ = ⟪T, T'⟫, so 2⟪T, T'⟫ = 0 → ⟪T, T'⟫ = 0
    have hsymm : ⟪deriv (curveTangent3 α h) t, curveTangent3 α h t⟫_ℝ =
                 ⟪curveTangent3 α h t, deriv (curveTangent3 α h) t⟫_ℝ := real_inner_comm _ _
    have hfun : curveTangent3 α h = deriv α.toFun := rfl
    simp only [hfun] at Dh hsymm
    linarith [Dh, hsymm]

private lemma binormal_cross (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ)
    (ht : t ∈ Set.Ioo α.a α.b) :
    curveNormal3 α h t =
      let e := EuclideanSpace.equiv (Fin 3) ℝ
      e.symm (crossProduct (e (curveBinormal3 α h t)) (e (curveTangent3 α h t))) := by
  -- Let e : EuclideanSpace ℝ (Fin 3) ≃ (Fin 3 → ℝ) be the equivalence.
  set e := EuclideanSpace.equiv (Fin 3) ℝ with he
  -- Step 1: B × T = T × (N × T)
  -- B = T × N by definition, so e(B) = e(T) × e(N).
  -- Then (e(T) × e(N)) × e(T) = e(T) × (e(N) × e(T)) - e(N) × (e(T) × e(T))
  --                             = e(T) × (e(N) × e(T)) - e(N) × 0
  --                             = e(T) × (e(N) × e(T)).   (by cross_cross and cross_self)
  have heB : e (curveBinormal3 α h t) =
      crossProduct (e (curveTangent3 α h t)) (e (curveNormal3 α h t)) := by
    have hdef : curveBinormal3 α h t =
        e.symm (crossProduct (e (curveTangent3 α h t)) (e (curveNormal3 α h t))) := rfl
    rw [hdef, e.apply_symm_apply]
  have hBT : crossProduct (e (curveBinormal3 α h t)) (e (curveTangent3 α h t)) =
      crossProduct (e (curveTangent3 α h t))
        (crossProduct (e (curveNormal3 α h t)) (e (curveTangent3 α h t))) := by
    rw [heB, cross_cross, cross_self, map_zero, sub_zero]
  -- Step 2: T × (N × T) = (T⬝T)·N − (N⬝T)·T = 1·N − 0·T = N  (BAC-CAB)
  -- Connect e v ⬝ᵥ e w with ⟪v, w⟫_ℝ via inner_eq_star_dotProduct
  -- e v = PiLp.ofLp v definitionally (PiLp.coe_continuousLinearEquiv is rfl),
  -- so EuclideanSpace.inner_eq_star_dotProduct v w : ⟪v,w⟫_ℝ = e w ⬝ᵥ star (e v)  by rfl
  have dot_e_eq : ∀ v w : ℝ^3, e v ⬝ᵥ e w = ⟪v, w⟫_ℝ := fun v w => by
    have hstar : star (e v) = e v := by ext; simp
    calc e v ⬝ᵥ e w
        = e w ⬝ᵥ e v        := dotProduct_comm _ _
      _ = e w ⬝ᵥ star (e v) := by rw [hstar]
      _ = ⟪v, w⟫_ℝ          := (EuclideanSpace.inner_eq_star_dotProduct v w).symm
  have hTT : e (curveTangent3 α h t) ⬝ᵥ e (curveTangent3 α h t) = 1 :=
    (dot_e_eq _ _).trans (dot_tangent α h t ht)
  have hNT : e (curveNormal3 α h t) ⬝ᵥ e (curveTangent3 α h t) = 0 :=
    (dot_e_eq _ _).trans ((real_inner_comm _ _).trans (orthogonality_tangent_normal α h t ht))
  have hTNT : crossProduct (e (curveTangent3 α h t))
      (crossProduct (e (curveNormal3 α h t)) (e (curveTangent3 α h t))) =
      e (curveNormal3 α h t) := by
    rw [cross_cross_eq_smul_sub_smul', hTT, hNT, one_smul, zero_smul, sub_zero]
  calc curveNormal3 α h t
      = e.symm (e (curveNormal3 α h t)) := (e.symm_apply_apply _).symm
    _ = e.symm (crossProduct (e (curveTangent3 α h t))
          (crossProduct (e (curveNormal3 α h t)) (e (curveTangent3 α h t)))) := by rw [hTNT]
    _ = e.symm (crossProduct (e (curveBinormal3 α h t)) (e (curveTangent3 α h t))) := by rw [← hBT]

/-- **Frenet formula for B**: the derivative of the binormal is `-τ(t) • N(t)`. -/
theorem derivBinormal (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ)
    (hcross : curveNormal3 α h t =
      (1 / Torsion3 α h t) •
        (let e := EuclideanSpace.equiv (Fin 3) ℝ
         e.symm (crossProduct (e (curveTangent3 α h t)) (e (deriv (curveNormal3 α h) t)))))
    (hb' : deriv (curveBinormal3 α h) t =
      (let e := EuclideanSpace.equiv (Fin 3) ℝ;
        -(e.symm (crossProduct (e (curveTangent3 α h t)) (e (deriv (curveNormal3 α h) t))))))
    (hτ : Torsion3 α h t ≠ 0) :
    deriv (curveBinormal3 α h) t = -(Torsion3 α h t) • curveNormal3 α h t := by
  let X : ℝ^3 :=
    (let e := EuclideanSpace.equiv (Fin 3) ℝ
     e.symm (crossProduct (e (curveTangent3 α h t)) (e (deriv (curveNormal3 α h) t))))
  have hcross' : curveNormal3 α h t = (1 / Torsion3 α h t) • X := by
    simpa [X] using hcross
  have hX : X = Torsion3 α h t • curveNormal3 α h t := by
    have hmul : (Torsion3 α h t) * (1 / Torsion3 α h t) = 1 := by
      field_simp [hτ]
    calc
      X = (1 : ℝ) • X := by simp
      _ = (Torsion3 α h t * (1 / Torsion3 α h t)) • X := by rw [hmul]
      _ = (Torsion3 α h t) • ((1 / Torsion3 α h t) • X) := by
        rw [smul_smul]
      _ = (Torsion3 α h t) • curveNormal3 α h t := by
        rw [← hcross']
  calc
    deriv (curveBinormal3 α h) t = -X := by simpa [X] using hb'
    _ = -(Torsion3 α h t • curveNormal3 α h t) := by rw [hX]
    _ = -(Torsion3 α h t) • curveNormal3 α h t := by rw [neg_smul]

/-- **Frenet formula for N**:
the derivative of the principal normal is `-κ(t) • T(t) + τ(t) • B(t)`. -/
theorem deriv_normal (α : ParametrizedDifferentiableCurve3)
    (h : isArcLengthParametrized3 α) (t : ℝ) (ht : t ∈ Set.Ioo α.a α.b)
    (hκ : Curvature3 α h t ≠ 0)
    (hcross : curveNormal3 α h t =
      (1 / Torsion3 α h t) •
        (let e := EuclideanSpace.equiv (Fin 3) ℝ
         e.symm (crossProduct (e (curveTangent3 α h t)) (e (deriv (curveNormal3 α h) t)))))
    (hb' : deriv (curveBinormal3 α h) t =
      (let e := EuclideanSpace.equiv (Fin 3) ℝ;
        -(e.symm (crossProduct (e (curveTangent3 α h t)) (e (deriv (curveNormal3 α h) t))))))
    (hτ : Torsion3 α h t ≠ 0) :
    deriv (curveNormal3 α h) t =
      -(Curvature3 α h t) • curveTangent3 α h t + Torsion3 α h t • curveBinormal3 α h t := by
  set e := EuclideanSpace.equiv (Fin 3) ℝ
  have hn : curveNormal3 α h t =
  e.symm (crossProduct (e (curveBinormal3 α h t)) (e (curveTangent3 α h t))) :=
      binormal_cross α h t ht
  have hn' : deriv (curveNormal3 α h) t =
      e.symm (crossProduct (e (deriv (curveBinormal3 α h) t)) (e (curveTangent3 α h t)) +
              crossProduct (e (curveBinormal3 α h t)) (e (deriv (curveTangent3 α h) t))) := by
    -- curveNormal agrees near t with the cross-product formula (binormal_cross holds on all of Ioo)
    have heq : curveNormal3 α h =ᶠ[nhds t]
        fun s => e.symm (crossProduct (e (curveBinormal3 α h s)) (e (curveTangent3 α h s))) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun s hs => binormal_cross α h s hs)
    rw [heq.deriv_eq]
    -- HasDerivAt for e ∘ curveBinormal: curveBinormal is smooth (C^∞ of α),
    --then chain rule with CLM e
    have hB : HasDerivAt (fun s => e (curveBinormal3 α h s)) (e (deriv (curveBinormal3 α h) t)) t
    := by
      have hBdiff : DifferentiableAt ℝ (curveBinormal3 α h) t := by
        have hTdiff : DifferentiableAt ℝ (curveTangent3 α h) t := by
          have hc : ContDiffOn ℝ 1 (deriv α.toFun) (Set.Ioo α.a α.b) :=
            α.contDiffOn.deriv_of_isOpen isOpen_Ioo le_top
          exact (hc.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds ht)
        have hNdiff : DifferentiableAt ℝ (curveNormal3 α h) t := by
          -- curveNormal α h s = (1 / ‖α''(s)‖) • α''(s)
          change DifferentiableAt ℝ
              (fun s => (1 / ‖deriv (deriv α.toFun) s‖) • deriv (deriv α.toFun) s) t
          have hα2 : DifferentiableAt ℝ (deriv (deriv α.toFun)) t := by
            have hc : ContDiffOn ℝ 1 (deriv (deriv α.toFun)) (Set.Ioo α.a α.b) :=
              (α.contDiffOn.deriv_of_isOpen isOpen_Ioo le_top).deriv_of_isOpen isOpen_Ioo le_top
            exact (hc.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds ht)
          have hα2ne : deriv (deriv α.toFun) t ≠ 0 :=
            fun h0 => hκ (by simp [Curvature3, h0])
          have hscalar : DifferentiableAt ℝ (fun s => (1 : ℝ) / ‖deriv (deriv α.toFun) s‖) t :=
            (differentiableAt_const 1).div (hα2.norm ℝ hα2ne) (norm_ne_zero_iff.mpr hα2ne)
          exact hscalar.smul hα2
        have h1 : DifferentiableAt ℝ (fun s => e (curveTangent3 α h s)) t :=
          (e : EuclideanSpace ℝ (Fin 3) →L[ℝ] (Fin 3 → ℝ)).differentiableAt.comp t hTdiff
        have h2 : DifferentiableAt ℝ (fun s => e (curveNormal3 α h s)) t :=
          (e : EuclideanSpace ℝ (Fin 3) →L[ℝ] (Fin 3 → ℝ)).differentiableAt.comp t hNdiff
        -- crossProduct (e T(s)) (e N(s)) is differentiable: reduce to polynomial coords
        have hcpdiff : DifferentiableAt ℝ
            (fun s => crossProduct (e (curveTangent3 α h s)) (e (curveNormal3 α h s))) t := by
          have hTi : ∀ i : Fin 3, DifferentiableAt ℝ (fun s => e (curveTangent3 α h s) i) t :=
            fun i => (differentiableAt_pi.mp h1) i
          have hNi : ∀ i : Fin 3, DifferentiableAt ℝ (fun s => e (curveNormal3 α h s) i) t :=
            fun i => (differentiableAt_pi.mp h2) i
          rw [differentiableAt_pi]; intro i; fin_cases i
          · change DifferentiableAt ℝ (fun s =>
                e (curveTangent3 α h s) 1 * e (curveNormal3 α h s) 2 -
                e (curveTangent3 α h s) 2 * e (curveNormal3 α h s) 1) t
            exact ((hTi 1).mul (hNi 2)).sub ((hTi 2).mul (hNi 1))
          · change DifferentiableAt ℝ (fun s =>
                e (curveTangent3 α h s) 2 * e (curveNormal3 α h s) 0 -
                e (curveTangent3 α h s) 0 * e (curveNormal3 α h s) 2) t
            exact ((hTi 2).mul (hNi 0)).sub ((hTi 0).mul (hNi 2))
          · change DifferentiableAt ℝ (fun s =>
                e (curveTangent3 α h s) 0 * e (curveNormal3 α h s) 1 -
                e (curveTangent3 α h s) 1 * e (curveNormal3 α h s) 0) t
            exact ((hTi 0).mul (hNi 1)).sub ((hTi 1).mul (hNi 0))
        -- e.symm is CLM: compose to get differentiability of curveBinormal
        exact DifferentiableAt.comp t (e.symm : (Fin 3 → ℝ) →L[ℝ] ℝ^3).differentiableAt hcpdiff
      exact (e : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      (Fin 3 → ℝ)).hasFDerivAt.comp_hasDerivAt t hBdiff.hasDerivAt
    -- HasDerivAt for e ∘ curveTangent: curveTangent = deriv α.toFun is C^1 (from C^∞ of α)
    have hT : HasDerivAt (fun s => e (curveTangent3 α h s))
      (e (deriv (curveTangent3 α h) t)) t := by
      have hTdiff : DifferentiableAt ℝ (curveTangent3 α h) t := by
        have hc : ContDiffOn ℝ 1 (deriv α.toFun) (Set.Ioo α.a α.b) :=
          α.contDiffOn.deriv_of_isOpen isOpen_Ioo le_top
        exact (hc.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds ht)
      exact (e : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      (Fin 3 → ℝ)).hasFDerivAt.comp_hasDerivAt t hTdiff.hasDerivAt
    -- product rule: d/dt [B(t) ×₃ T(t)] = B'(t) ×₃ T(t) + B(t) ×₃ T'(t)
    -- crossProduct is bilinear so we need its derivative as a CLM-valued function
    have hprod : HasDerivAt
        (fun s => crossProduct (e (curveBinormal3 α h s)) (e (curveTangent3 α h s)))
        (crossProduct (e (deriv (curveBinormal3 α h) t)) (e (curveTangent3 α h t)) +
         crossProduct (e (curveBinormal3 α h t)) (e (deriv (curveTangent3 α h) t))) t := by
      have hBi : ∀ i : Fin 3, HasDerivAt
          (fun s => e (curveBinormal3 α h s) i)
          (e (deriv (curveBinormal3 α h) t) i) t :=
        fun i => (hasDerivAt_pi.mp hB) i
      have hTi : ∀ i : Fin 3, HasDerivAt
          (fun s => e (curveTangent3 α h s) i)
          (e (deriv (curveTangent3 α h) t) i) t :=
        fun i => (hasDerivAt_pi.mp hT) i
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · -- component 0: B 1 * T 2 - B 2 * T 1
        convert ((hBi 1).mul (hTi 2)).sub ((hBi 2).mul (hTi 1)) using 1
        change e (deriv (curveBinormal3 α h) t) 1 * e (curveTangent3 α h t) 2 -
              e (deriv (curveBinormal3 α h) t) 2 * e (curveTangent3 α h t) 1 +
            (e (curveBinormal3 α h t) 1 * e (deriv (curveTangent3 α h) t) 2 -
             e (curveBinormal3 α h t) 2 * e (deriv (curveTangent3 α h) t) 1) =
            e (deriv (curveBinormal3 α h) t) 1 * e (curveTangent3 α h t) 2 +
            e (curveBinormal3 α h t) 1 * e (deriv (curveTangent3 α h) t) 2 -
            (e (deriv (curveBinormal3 α h) t) 2 * e (curveTangent3 α h t) 1 +
             e (curveBinormal3 α h t) 2 * e (deriv (curveTangent3 α h) t) 1)
        ring
      · -- component 1: B 2 * T 0 - B 0 * T 2
        convert ((hBi 2).mul (hTi 0)).sub ((hBi 0).mul (hTi 2)) using 1
        change e (deriv (curveBinormal3 α h) t) 2 * e (curveTangent3 α h t) 0 -
              e (deriv (curveBinormal3 α h) t) 0 * e (curveTangent3 α h t) 2 +
            (e (curveBinormal3 α h t) 2 * e (deriv (curveTangent3 α h) t) 0 -
             e (curveBinormal3 α h t) 0 * e (deriv (curveTangent3 α h) t) 2) =
            e (deriv (curveBinormal3 α h) t) 2 * e (curveTangent3 α h t) 0 +
            e (curveBinormal3 α h t) 2 * e (deriv (curveTangent3 α h) t) 0 -
            (e (deriv (curveBinormal3 α h) t) 0 * e (curveTangent3 α h t) 2 +
             e (curveBinormal3 α h t) 0 * e (deriv (curveTangent3 α h) t) 2)
        ring
      · -- component 2: B 0 * T 1 - B 1 * T 0
        convert ((hBi 0).mul (hTi 1)).sub ((hBi 1).mul (hTi 0)) using 1
        change e (deriv (curveBinormal3 α h) t) 0 * e (curveTangent3 α h t) 1 -
              e (deriv (curveBinormal3 α h) t) 1 * e (curveTangent3 α h t) 0 +
            (e (curveBinormal3 α h t) 0 * e (deriv (curveTangent3 α h) t) 1 -
             e (curveBinormal3 α h t) 1 * e (deriv (curveTangent3 α h) t) 0) =
            e (deriv (curveBinormal3 α h) t) 0 * e (curveTangent3 α h t) 1 +
            e (curveBinormal3 α h t) 0 * e (deriv (curveTangent3 α h) t) 1 -
            (e (deriv (curveBinormal3 α h) t) 1 * e (curveTangent3 α h t) 0 +
             e (curveBinormal3 α h t) 1 * e (deriv (curveTangent3 α h) t) 0)
        ring
    -- e.symm is a CLM: chain rule via HasFDerivAt.comp_hasDerivAt
    exact (((e.symm : (Fin 3 → ℝ) →L[ℝ] ℝ^3).hasFDerivAt).comp_hasDerivAt t hprod).deriv
  -- Apply Frenet 1 (deriv T = κ • N) and Frenet 3 (deriv B = -τ • N) and reduce.
  have hB : deriv (curveBinormal3 α h) t = -(Torsion3 α h t) • curveNormal3 α h t := by
    rw [derivBinormal α h t hcross hb' hτ]
  rw [hn', derivTangent α h t hκ, hB]
  -- Push smul through e (CLE) and crossProduct (bilinear LinearMap).
  rw [map_smul e (-(Torsion3 α h t)) (curveNormal3 α h t),
      map_smul e (Curvature3 α h t) (curveNormal3 α h t),
      LinearMap.map_smul₂ crossProduct (-(Torsion3 α h t))
        (e (curveNormal3 α h t)) (e (curveTangent3 α h t)),
      LinearMap.map_smul (crossProduct (e (curveBinormal3 α h t))) (Curvature3 α h t)
        (e (curveNormal3 α h t))]
  -- Compute the cross-product identities `e N × e T = -e B` and `e B × e N = -e T`.
  have heB_def : e (curveBinormal3 α h t) =
      crossProduct (e (curveTangent3 α h t)) (e (curveNormal3 α h t)) := rfl
  have hNT : crossProduct (e (curveNormal3 α h t)) (e (curveTangent3 α h t)) =
      -e (curveBinormal3 α h t) := by
    rw [heB_def, ← cross_anticomm]
  have dot_e_eq : ∀ v w : ℝ^3, e v ⬝ᵥ e w = ⟪v, w⟫_ℝ := fun v w => by
    have hstar : star (e v) = e v := by ext; simp
    calc e v ⬝ᵥ e w
        = e w ⬝ᵥ e v        := dotProduct_comm _ _
      _ = e w ⬝ᵥ star (e v) := by rw [hstar]
      _ = ⟪v, w⟫_ℝ          := (EuclideanSpace.inner_eq_star_dotProduct v w).symm
  have hTN_dot : e (curveTangent3 α h t) ⬝ᵥ e (curveNormal3 α h t) = 0 :=
    (dot_e_eq _ _).trans (orthogonality_tangent_normal α h t ht)
  have hN_norm : ‖curveNormal3 α h t‖ = 1 := by
    have hκ_pos : (0 : ℝ) < Curvature3 α h t :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hκ)
    change ‖(1 / Curvature3 α h t) • deriv (deriv α.toFun) t‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (one_div_pos.mpr hκ_pos))]
    change 1 / Curvature3 α h t * ‖deriv (deriv α.toFun) t‖ = 1
    rw [show ‖deriv (deriv α.toFun) t‖ = Curvature3 α h t from rfl]
    field_simp
  have hNN_dot : e (curveNormal3 α h t) ⬝ᵥ e (curveNormal3 α h t) = 1 := by
    rw [dot_e_eq, real_inner_self_eq_norm_sq, hN_norm]; norm_num
  have hBN : crossProduct (e (curveBinormal3 α h t)) (e (curveNormal3 α h t)) =
      -e (curveTangent3 α h t) := by
    rw [heB_def, cross_cross_eq_smul_sub_smul, hTN_dot, hNN_dot,
        zero_smul, one_smul, zero_sub]
  rw [hNT, hBN]
  -- (-τ) • -(e B) = τ • e B   and   κ • -(e T) = -(κ • e T)
  rw [show -(Torsion3 α h t) • -(e (curveBinormal3 α h t)) =
        (Torsion3 α h t) • e (curveBinormal3 α h t) from neg_smul_neg _ _,
      smul_neg (Curvature3 α h t) (e (curveTangent3 α h t))]
  -- Push e.symm through add/neg/smul, then reduce e.symm ∘ e.
  rw [map_add e.symm, map_neg e.symm, map_smul e.symm, map_smul e.symm,
      e.symm_apply_apply, e.symm_apply_apply]
  -- Goal: τ • B + -(κ • T) = -(κ) • T + τ • B
  rw [neg_smul]
  abel

end Curves
