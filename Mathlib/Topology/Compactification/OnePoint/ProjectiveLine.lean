/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Projectivization.GLAction
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Algebra.QuadraticDiscriminant

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

namespace OnePoint

section DivisionRing

variable (K : Type*) [DivisionRing K] [DecidableEq K]

/-- The one-point compactification of a division ring `K` is equivalent to
the projectivivization `ℙ K (K × K)`. -/
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

/-- For a field `K`, the group `GL(2, K)` acts on `OnePoint K`. -/
instance instGLAction : MulAction (GL (Fin 2) K) (OnePoint K) :=
  (equivProjectivization K).mulAction (GL (Fin 2) K)

lemma smul_infty_def {g : GL (Fin 2) K} :
    g • ∞ = (equivProjectivization K).symm (.mk K (g 0 0, g 1 0) (fun h ↦ by
      simpa [det_fin_two, Prod.mk_eq_zero.mp h] using g.det_ne_zero)) := by
  simp [Equiv.smul_def, MulAction.compHom_smul_def, Projectivization.smul_mk, mulVec_eq_sum,
    Units.smul_def]

@[simp]
lemma smul_infty_eq_ite {g : GL (Fin 2) K} :
    (g • ∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0 := by
  by_cases h : g 1 0 = 0 <;>
  simp [h, div_eq_inv_mul, smul_infty_def]

lemma smul_infty_eq_self_iff {g : GL (Fin 2) K} :
    g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0 := by
  simp

lemma smul_some_eq_ite {g : GL (Fin 2) K} {k : K} :
    g • (k : OnePoint K) =
      if g 1 0 * k + g 1 1 = 0 then ∞ else (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1) := by
  simp [Equiv.smul_def, MulAction.compHom_smul_def, Projectivization.smul_mk, mulVec_eq_sum,
    div_eq_inv_mul, mul_comm, Units.smul_def]

lemma map_smul {L : Type*} [Field L] [DecidableEq L]
    (f : K →+* L) (g : GL (Fin 2) K) (c : OnePoint K) :
    OnePoint.map f (g • c) = (g.map f) • (c.map f) := by
  cases c with
  | infty => simp [smul_infty_eq_ite, apply_ite]
  | coe c => simp [smul_some_eq_ite, ← map_mul, ← map_add, apply_ite]

end Field

end OnePoint

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
  (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/-- The discriminant of a `2 × 2` matrix. -/
noncomputable def disc : R := m.trace ^ 2 - 4 * m.det

/-- A `2 × 2` matrix is *parabolic* if it is non-scalar and its discriminant is 0. -/
def IsParabolic : Prop := m ∉ Set.range (scalar _) ∧ m.disc = 0

/-- A `2 × 2` matrix is *hyperbolic* if its discriminant is a non-zero square. -/
def IsHyperbolic : Prop := m.disc ≠ 0 ∧ ∃ s, s ^ 2 = m.disc

/-- A `2 × 2` matrix is *elliptic* if its discriminant is not a square. -/
def IsElliptic : Prop := ¬∃ s, s ^ 2 = m.disc

section conjugation

variable {m}

-- conjugation lemmas are not flagged `simp` because `g.val⁻¹` is simp-normal form, not
-- `g⁻¹.val`, but `g⁻¹.val` is more convenient in this theory

lemma disc_conj : (g * m * g⁻¹).disc = m.disc := by
  simp only [disc, trace_units_conj, det_units_conj]

lemma disc_conj' : (g⁻¹ * m * g).disc = m.disc := by
  simpa using disc_conj g⁻¹

lemma isParabolic_conj_iff : (g * m * g⁻¹).IsParabolic ↔ IsParabolic m := by
  simp_rw [IsParabolic, disc_conj, Set.mem_range, Units.eq_mul_inv_iff_mul_eq,
    scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal, Units.mul_right_inj]

lemma isParabolic_conj'_iff : (g⁻¹ * m * g).IsParabolic ↔ m.IsParabolic := by
  simpa using isParabolic_conj_iff g⁻¹

lemma isHyperbolic_conj_iff : (g * m * g⁻¹).IsHyperbolic ↔ m.IsHyperbolic := by
  simp only [IsHyperbolic, disc_conj]

lemma isHyperbolic_conj'_iff : (g⁻¹ * m * g).IsHyperbolic ↔ m.IsHyperbolic := by
  simpa using isHyperbolic_conj_iff g⁻¹

lemma isElliptic_conj_iff : (g * m * g⁻¹).IsElliptic ↔ m.IsElliptic := by
  simp only [IsElliptic, disc_conj]

lemma isElliptic_conj'_iff : (g⁻¹ * m * g).IsElliptic ↔ m.IsElliptic := by
  simpa using isElliptic_conj_iff g⁻¹

end conjugation

section Field

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

lemma sub_scalar_sq_eq_disc [NeZero (2 : K)] :
    (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.disc / 4) := by
  simp only [Matrix.scalar_apply, Matrix.trace_fin_two, disc, Matrix.trace_fin_two,
    Matrix.det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field_simp
    ring

variable (m) in
/-- The unique eigenvalue of a parabolic matrix (junk if `m` is not parabolic). -/
def parabolicEigenvalue : K := m.trace / 2

lemma IsParabolic.sub_eigenvalue_sq_eq_zero [NeZero (2 : K)] (hm : m.IsParabolic) :
    (m - scalar _ m.parabolicEigenvalue) ^ 2 = 0 := by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_disc, hm.2]

/-- Characterization of parabolic elements: they have the form `a + m` where `a` is scalar and
`m` is nonzero and nilpotent. -/
lemma isParabolic_iff_exists [NeZero (2 : K)] :
    m.IsParabolic ↔ ∃ a n, m = scalar _ a + n ∧ n ≠ 0 ∧ n ^ 2 = 0 := by
  constructor
  · exact fun hm ↦ ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h ↦ hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ ↦ hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb, ← map_sub, ← map_pow, ← map_zero (scalar (Fin 2)), scalar_inj,
        sq_eq_zero_iff] using hnsq
    · suffices scalar (Fin 2) (m.disc / 4) = 0 by
        rw [← map_zero (scalar (Fin 2)), scalar_inj, div_eq_zero_iff] at this
        have : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using NeZero.ne _
        tauto
      rw [← sub_scalar_sq_eq_disc, hm, trace_add, scalar_apply, trace_diagonal]
      simp [mul_div_cancel_left₀ _ (NeZero.ne (2 : K)),
        (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hnsq⟩).eq_zero , hnsq]

end Field

end Matrix

namespace Matrix.GeneralLinearGroup

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Synonym of `Matrix.IsParabolic`, for dot-notation. -/
@[reducible] def IsParabolic (g : GL (Fin 2) R) : Prop := g.val.IsParabolic

/-- Synonym of `Matrix.IsElliptic`, for dot-notation. -/
@[reducible] def IsElliptic (g : GL (Fin 2) R) : Prop := g.val.IsElliptic

/-- Synonym of `Matrix.IsHyperbolic`, for dot-notation. -/
@[reducible] def IsHyperbolic (g : GL (Fin 2) R) : Prop := g.val.IsHyperbolic

/-- The center of `GL n R` consists of scalar matrices. -/
lemma mem_center_iff_val_eq_scalar {g : GL n R} :
    g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (scalar _) := by
  rcases isEmpty_or_nonempty n
  · simpa [Subsingleton.elim (Subgroup.center _) ⊤] using ⟨1, Subsingleton.elim _ _⟩
  constructor
  · intro hg
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
    simpa [Units.ext_iff] using Subgroup.mem_center_iff.mp hg (.mk _ _ t.mul_inv t.inv_mul)
  · refine fun ⟨a, ha⟩ ↦ Subgroup.mem_center_iff.mpr fun h ↦ ?_
    simpa [Units.ext_iff, ← ha] using (scalar_commute a (mul_comm a ·) h.val).symm

/-- The center of `GL n R` is the image of `Rˣ`. -/
lemma center_eq_range_units :
    Subgroup.center (GL n R) = (Units.map (algebraMap R _).toMonoidHom).range := by
  ext g
  -- eliminate tedious case `n = ∅`
  rcases isEmpty_or_nonempty n
  · simpa [Subsingleton.elim (Subgroup.center _) ⊤] using ⟨1, Subsingleton.elim _ _⟩
  constructor
  · -- previous lemma shows the underlying matrix is scalar, but now need to show
    -- the scalar is a unit; so we apply argument both to `g` and `g⁻¹`
    intro hg
    obtain ⟨a, ha⟩ := mem_center_iff_val_eq_scalar.mp hg
    obtain ⟨b, hb⟩ := mem_center_iff_val_eq_scalar.mp (Subgroup.inv_mem _ hg)
    have hab : a * b = 1 := by
      simpa [-mul_inv_cancel, ← ha, ← hb, ← diagonal_one, Units.ext_iff] using mul_inv_cancel g
    refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, ?_⟩
    simp [Units.ext_iff, ← ha, algebraMap_eq_diagonal]
  · rintro ⟨a, rfl⟩
    exact mem_center_iff_val_eq_scalar.mpr ⟨a, rfl⟩

/-- Polynomial whose roots are the fixed points of `g` considered as a Möbius transformation. -/
noncomputable def fixpointPolynomial (g : GL (Fin 2) R) : R[X] :=
  C (g 1 0) * X ^ 2 + C (g 1 1 - g 0 0) * X - C (g 0 1)

/-- The fixed-point polynomial is identically zero iff `g` is scalar. -/
lemma fixpointPolynomial_eq_zero_iff {g : GL (Fin 2) R} :
    g.fixpointPolynomial = 0 ↔ g.val ∈ Set.range (scalar _) := by
  rw [fixpointPolynomial]
  constructor
  · refine fun hP ↦ ⟨g 0 0, ?_⟩
    have hb : g 0 1 = 0 := by simpa using congr_arg (coeff · 0) hP
    have hc : g 1 0 = 0 := by simpa using congr_arg (coeff · 2) hP
    have hd : g 1 1 = g 0 0 := by simpa [sub_eq_zero] using congr_arg (coeff · 1) hP
    ext i j
    fin_cases i <;>
    fin_cases j <;>
    simp [hb, hc, hd]
  · rintro ⟨a, ha⟩
    simp [← ha]

variable {K : Type*} [Field K]

lemma parabolicEigenvalue_ne_zero {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsParabolic g) :
    g.val.parabolicEigenvalue ≠ 0 := by
  rw [parabolicEigenvalue, div_ne_zero_iff, eq_true_intro (two_ne_zero' K), and_true,
    Ne, ← sq_eq_zero_iff, sub_eq_zero.mp hg.2, show (4 : K) = 2 ^ 2 by norm_num, mul_eq_zero,
    sq_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, g.det_ne_zero⟩

lemma IsParabolic.pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
    {n : ℕ} (hn : n ≠ 0) : IsParabolic (g ^ n) := by
  rw [IsParabolic, isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn IH =>
      simp only [pow_succ, IH, add_mul, Nat.add_sub_cancel, mul_add, ← map_mul, add_assoc]
      simp only [scalar_apply, ← smul_eq_mul_diagonal, ← MulAction.mul_smul, ← smul_eq_diagonal_mul,
        smul_mul, ← sq, hmsq, smul_zero, add_zero, ← add_smul, Nat.cast_add_one, add_mul, one_mul]
      rw [(by omega : n = n - 1 + 1), pow_succ, (by omega : n - 1 + 1 = n)]
      ring_nf
  · suffices a ≠ 0 by simp [this, hm0, hn]
    refine fun ha ↦ (g ^ 2).det_ne_zero ?_
    rw [ha, map_zero, zero_add] at hg
    rw [← hg] at hmsq
    rw [Units.val_pow_eq_pow_val, hmsq, det_zero ⟨0⟩]

variable [DecidableEq K]

/-- The roots of `g.fixpointPolynomial` are the fixed points of `g ∈ GL(2, K)` acting on the finite
part of `OnePoint K`. -/
lemma fixpointPolynomial_aeval_eq_zero_iff {c : K} {g : GL (Fin 2) K} :
    g.fixpointPolynomial.aeval c = 0 ↔ g • (c : OnePoint K) = c := by
  simp only [fixpointPolynomial, map_sub, map_mul, map_add, aeval_X_pow, aeval_C, aeval_X,
    Algebra.id.map_eq_self, OnePoint.smul_some_eq_ite]
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
  rw [disc, trace_fin_two, det_fin_two] at hdisc
  cases c with
  | infty => by_cases h : g 1 0 = 0 <;> simp [parabolicFixedPoint, h]
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
lemma IsElliptic.smul_ne_self {g : GL (Fin 2) K} (hg : g.IsElliptic) (c : OnePoint K) :
    g • c ≠ c := by
  cases c with
  | infty =>
    refine fun h ↦ hg ⟨g 0 0 - g 1 1, ?_⟩
    simp only [disc, trace_fin_two, det_fin_two, smul_infty_eq_self_iff.mp h]
    ring
  | coe c =>
    refine fun h ↦ hg ⟨2 * g 1 0 * c + (g 1 1 + -g 0 0), ?_⟩
    simp [← fixpointPolynomial_aeval_eq_zero_iff, fixpointPolynomial, sq, sub_eq_add_neg] at h
    simp only [← discrim_eq_sq_of_quadratic_eq_zero h, disc, discrim, trace_fin_two, det_fin_two]
    ring

end Matrix.GeneralLinearGroup
