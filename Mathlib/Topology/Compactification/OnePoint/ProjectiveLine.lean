/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One-point compactification and projectivization

We construct a set-theoretic equivalence between
`OnePoint K` and the projectivization `ℙ K (K × K)` for an arbitrary division ring `K`.

TODO: Add the extension of this equivalence to a homeomorphism in the case `K = ℝ`,
where `OnePoint ℝ` gets the topology of one-point compactification.


## Main definitions and results

* `OnePoint.equivProjectivization` : the equivalence `OnePoint K ≃ ℙ K (K × K)`.

## Tags

one-point extension, projectivization
-/

open scoped LinearAlgebra.Projectivization

open Projectivization Matrix Polynomial OnePoint

section MatrixProdAction

variable {R n : Type*} [Semiring R] [Fintype n] [DecidableEq n]

instance : Module (Matrix (Fin 2) (Fin 2) R) (R × R) :=
  (LinearEquiv.finTwoArrow R R).symm.toAddEquiv.module _

instance {S} [DistribSMul S R] [SMulCommClass R S R] :
    SMulCommClass (Matrix (Fin 2) (Fin 2) R) S (R × R) :=
  (LinearEquiv.finTwoArrow R R).symm.smulCommClass _ _

@[simp] lemma Matrix.fin_two_smul_prod (g : Matrix (Fin 2) (Fin 2) R) (v : R × R) :
    g • v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := by
  simp [Equiv.smul_def, smul_eq_mulVec, Matrix.mulVec_eq_sum]

@[simp] lemma Matrix.GeneralLinearGroup.fin_two_smul_prod {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) (v : R × R) :
    g • v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := by
  simp [Units.smul_def]

end MatrixProdAction

namespace OnePoint

section DivisionRing

variable (K : Type*) [DivisionRing K] [DecidableEq K]

/-- The one-point compactification of a division ring `K` is equivalent to
the projectivization `ℙ K (K × K)`. -/
def equivProjectivization :
    OnePoint K ≃ ℙ K (K × K) where
  toFun p := p.elim (mk K (1, 0) (by simp)) (fun t ↦ mk K (t, 1) (by simp))
  invFun p := by
    refine Projectivization.lift
      (fun u : {v : K × K // v ≠ 0} ↦ if u.1.2 = 0 then ∞ else ((u.1.2)⁻¹ * u.1.1)) ?_ p
    rintro ⟨-, hv⟩ ⟨⟨x, y⟩, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hv
    by_cases h₀ : y = 0 <;> simp [h₀, ht, mul_assoc]
  left_inv p := by cases p <;> simp
  right_inv p := by
    induction p using ind with | h p hp =>
    obtain ⟨x, y⟩ := p
    by_cases h₀ : y = 0 <;> simp only [mk_eq_mk_iff', h₀, Projectivization.lift_mk, if_true,
      if_false, OnePoint.elim_infty, OnePoint.elim_some, Prod.smul_mk, Prod.mk.injEq, smul_eq_mul,
      mul_zero, and_true]
    · use x⁻¹
      simp_all
    · exact ⟨y⁻¹, rfl, inv_mul_cancel₀ h₀⟩

@[simp]
lemma equivProjectivization_apply_infinity :
    equivProjectivization K ∞ = mk K ⟨1, 0⟩ (by simp) :=
  rfl

@[simp]
lemma equivProjectivization_apply_coe (t : K) :
    equivProjectivization K t = mk K ⟨t, 1⟩ (by simp) :=
  rfl

@[simp]
lemma equivProjectivization_symm_apply_mk (x y : K) (h : (x, y) ≠ 0) :
    (equivProjectivization K).symm (mk K ⟨x, y⟩ h) = if y = 0 then ∞ else y⁻¹ * x := by
  simp [equivProjectivization]

end DivisionRing

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- For a field `K`, the group `GL(2, K)` acts on `OnePoint K`, via the canonical identification
with the `ℙ¹(K)` (which is given explicitly by Möbius transformations). -/
instance instGLAction : MulAction (GL (Fin 2) K) (OnePoint K) :=
  (equivProjectivization K).mulAction (GL (Fin 2) K)

lemma smul_infty_def {g : GL (Fin 2) K} :
    g • ∞ = (equivProjectivization K).symm (.mk K (g 0 0, g 1 0) (fun h ↦ by
      simpa [det_fin_two, Prod.mk_eq_zero.mp h] using g.det_ne_zero)) := by
  simp [Equiv.smul_def, mulVec_eq_sum, Units.smul_def]

lemma smul_infty_eq_ite (g : GL (Fin 2) K) :
    g • (∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0 := by
  by_cases h : g 1 0 = 0 <;>
  simp [h, div_eq_inv_mul, smul_infty_def]

lemma smul_infty_eq_self_iff {g : GL (Fin 2) K} :
    g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0 := by
  simp [smul_infty_eq_ite]

lemma smul_some_eq_ite {g : GL (Fin 2) K} {k : K} :
    g • (k : OnePoint K) =
      if g 1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1) := by
  simp [Equiv.smul_def, mulVec_eq_sum, div_eq_inv_mul, mul_comm, Units.smul_def]

lemma map_smul {L : Type*} [Field L] [DecidableEq L]
    (f : K →+* L) (g : GL (Fin 2) K) (c : OnePoint K) :
    OnePoint.map f (g • c) = (g.map f) • (c.map f) := by
  cases c with
  | infty => simp [smul_infty_eq_ite, apply_ite]
  | coe c => simp [smul_some_eq_ite, ← map_mul, ← map_add, apply_ite]

end Field

end OnePoint

namespace Matrix.GeneralLinearGroup

variable {K : Type*} [Field K] [DecidableEq K]

/-- The roots of `g.fixpointPolynomial` are the fixed points of `g ∈ GL(2, K)` acting on the finite
part of `OnePoint K`. -/
lemma fixpointPolynomial_aeval_eq_zero_iff {c : K} {g : GL (Fin 2) K} :
    g.fixpointPolynomial.aeval c = 0 ↔ g • (c : OnePoint K) = c := by
  simp only [fixpointPolynomial, map_sub, map_mul, map_add, aeval_X_pow, aeval_C, aeval_X,
    Algebra.algebraMap_self_apply, OnePoint.smul_some_eq_ite]
  split_ifs with h
  · refine ⟨fun hg ↦ (g.det_ne_zero ?_).elim, fun hg ↦ (infty_ne_coe _ hg).elim⟩
    rw [det_fin_two]
    grind
  · rw [coe_eq_coe, div_eq_iff h]
    grind

/-- If `g` is parabolic, this is the unique fixed point of `g` in `OnePoint K`. -/
def parabolicFixedPoint (g : GL (Fin 2) K) : OnePoint K :=
  if g 1 0 = 0 then ∞ else ↑((g 0 0 - g 1 1) / (2 * g 1 0))

lemma IsParabolic.smul_eq_self_iff {g : GL (Fin 2) K} (hg : g.IsParabolic) [NeZero (2 : K)]
    {c : OnePoint K} : g • c = c ↔ c = parabolicFixedPoint g := by
  rcases hg with ⟨hg, hdisc⟩
  rw [discr_fin_two, trace_fin_two, det_fin_two] at hdisc
  cases c with
  | infty => by_cases h : g 1 0 = 0 <;> simp [parabolicFixedPoint, smul_infty_eq_ite, h]
  | coe c =>
    suffices g 1 0 * c ^ 2 + (g 1 1 - g 0 0) * c - g 0 1 = 0 ↔ c = g.parabolicFixedPoint by
      simpa [← fixpointPolynomial_aeval_eq_zero_iff, fixpointPolynomial]
    by_cases hc : g 1 0 = 0
    · have hd : g 1 1 = g 0 0 := by grind
      suffices g 0 1 ≠ 0 by simpa [parabolicFixedPoint, hc, hd]
      -- can't have `g 0 1 ≠ 0` since that would force `g` to be scalar
      refine fun hb ↦ fixpointPolynomial_eq_zero_iff.not.mpr hg ?_
      simp [fixpointPolynomial, hb, hc, hd]
    · have : discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1) = 0 := by rw [discrim]; grind
      simpa [parabolicFixedPoint, if_neg hc, sq, sub_eq_add_neg]
        using quadratic_eq_zero_iff_of_discrim_eq_zero hc this c

lemma IsParabolic.parabolicFixedPoint_pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
    {n : ℕ} (hn : n ≠ 0) :
    (g ^ n).parabolicFixedPoint = g.parabolicFixedPoint := by
  rw [eq_comm, ← IsParabolic.smul_eq_self_iff (hg.pow hn)]
  clear hn
  induction n with
  | zero => simp
  | succ n IH => rw [pow_succ, MulAction.mul_smul, hg.smul_eq_self_iff.mpr rfl, IH]

/-- Elliptic elements have no fixed points in `OnePoint K`. -/
lemma IsElliptic.smul_ne_self [LinearOrder K] [IsStrictOrderedRing K]
    {g : GL (Fin 2) K} (hg : g.IsElliptic) (c : OnePoint K) :
    g • c ≠ c := by
  cases c with
  | infty =>
    rw [Ne, smul_infty_eq_self_iff]
    refine fun h ↦ not_le_of_gt hg ?_
    have : g.val.discr = (g 0 0 - g 1 1) ^ 2 := by
      simp only [discr_fin_two, trace_fin_two, det_fin_two]
      grind
    rw [this]
    apply sq_nonneg
  | coe c =>
    refine fun h ↦ not_le_of_gt hg ?_
    have : g.val.discr = (2 * g 1 0 * c + (g 1 1 + -g 0 0)) ^ 2 := by
      replace h : g 1 0 * (c * c) + (g 1 1 + -g 0 0) * c + -g 0 1 = 0 := by
        simpa [← fixpointPolynomial_aeval_eq_zero_iff, fixpointPolynomial, sq, sub_eq_add_neg]
          using h
      simp only [← discrim_eq_sq_of_quadratic_eq_zero h, discr_fin_two, discrim, trace_fin_two,
        det_fin_two]
      grind
    rw [this]
    apply sq_nonneg

end Matrix.GeneralLinearGroup
