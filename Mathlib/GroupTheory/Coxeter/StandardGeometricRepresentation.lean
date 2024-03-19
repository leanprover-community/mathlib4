/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Int.Parity

/-!
# The standard geometric representation
Throughout this file, `B` is a type and `M : Matrix B B ℕ` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* Matrix.CoxeterGroup M`, where `Matrix.CoxeterGroup M` refers to
the quotient of the free group on `B` by the Coxeter relations given by the matrix `M`. See
`Mathlib.GroupTheory.Coxeter.Basic` for more details.

Let $V$ be the free $\mathbb{R}$ vector space over `B` and let $\{\alpha_i\}$ be the standard basis
of $V$. We define a bilinear form on $V$ by
$$\langle \alpha_i, \alpha_{i'}\rangle = -\cos (\pi / M_{i, i'}),$$
where $M$ is the Coxeter matrix of $W$ (see `Mathlib.GroupTheory.Coxeter.Basic`). This is positive
definite if and only if $W$ is a finite group, although we do not prove that in this file.

Then, we have a representation $\rho \colon W \to GL(V)$, called the
*standard geometric representation*, given by
$$\rho(s_i) v = v - \langle \alpha_i, v\rangle \alpha_i.$$ We prove that this representation is well
defined and faithful.

We prove for all $w$ and $i$ that $\ell(w s_i) + 1 = \ell(w)$ if and only if $\rho(w) \alpha_i$ is a
nonpositive linear combination of the simple roots, and that $\ell(w s_i) = \ell(w) + 1$ if and only
if $\rho(w) \alpha_i$ is a nonnegative linear combination of the simple roots.

## Main definitions
* `cs.standardBilinForm`: The invariant bilinear form associated to the standard geometric
representation.
* `cs.standardGeometricRepresentation`: The standard geometric representation of `W`. This has type
`Representation ℝ W (B →₀ ℝ)`.

## References
* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)
-/

noncomputable section

open List Real LinearMap

/-- The Chebyshev polynomial of the second kind corresponding to the index n - 1. Correctly
yields U₋₁ = 0 if n = 0.
-/
@[local simp] private def Polynomial.Chebyshev.USubOne (R : Type) [CommRing R] (n : ℕ) :=
    U R (n + 1) - 2 * (T R (n + 1))

private lemma Polynomial.Chebyshev.USubOne_add_one (R : Type) [CommRing R] (n : ℕ) :
    USubOne R (n + 1) = U R n := by
  dsimp [USubOne]
  rw [T_eq_U_sub_X_mul_U]
  rw [(by ring : n + 1 + 1 = n + 2), U_add_two]
  ring

private lemma Polynomial.Chebyshev.sin_pi_div_m_ne_zero {m : ℕ} (hm : m > 1) : sin (π / m) ≠ 0 := by
  intro eq0
  have h₀ : 0 < π / m := by positivity
  have h₁ := calc
    π / m ≤ π / 2                   := by
      apply (div_le_div_left (by positivity) (by positivity) (by positivity)).mpr
      apply Nat.cast_le.mpr
      linarith
    _     ≤ 2                       := by linarith [Real.pi_le_four]
  linarith [Real.sin_pos_of_pos_of_le_two h₀ h₁]

private lemma Polynomial.Chebyshev.USubOne_real_cos (θ : ℝ) (n : ℕ) :
    eval (cos θ) (USubOne ℝ n) * sin θ = sin (n * θ) := by
  rcases n with _ | n
  · simp [USubOne]
  · rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, USubOne_add_one]
    exact U_real_cos _ _

private lemma Polynomial.Chebyshev.USubOne_real_neg_cos_eq {m : ℕ} (n : ℕ) (hm : m > 1) :
    eval (- cos (π / m)) (USubOne ℝ n) = -((-1) ^ n * sin (π * (n / m)) / sin (π / m)) := by
  rw [← Real.cos_add_pi (π / m)]

  have sin_ne_zero : sin (π / m) ≠ 0 := sin_pi_div_m_ne_zero hm
  have sin_ne_zero' : sin (π / m + π) ≠ 0 := by rw [sin_add_pi]; simpa

  rw [(eq_div_iff sin_ne_zero').mpr (USubOne_real_cos (π / m + π) n)]
  rw [mul_add, sin_add_nat_mul_pi, sin_add_pi]
  field_simp [sin_ne_zero]
  ring_nf

private lemma Polynomial.Chebyshev.U_real_neg_cos_eq {m : ℕ} (n : ℕ) (hm : m > 1) :
    eval (- cos (π / m)) (U ℝ n) = (-1) ^ n * sin (π * ((n + 1) / m)) / sin (π / m) := by
  rw [← USubOne_add_one, USubOne_real_neg_cos_eq _ hm, pow_succ]
  simp [neg_mul, neg_div]


/-! ### The standard geometric representation
Given a Coxeter group `W` whose simple reflections are indexed by a set `B`, we define
the standard geometric representation of `W`, which is a representation of `W` with underlying
vector space `B →₀ ℝ`.
-/
namespace Matrix

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable (hM : IsCoxeter M)

local notation "V" => B →₀ ℝ
instance : AddCommMonoid V := Finsupp.instAddCommMonoid

def simpleRoot (i : B) : V := Finsupp.single i 1
local prefix:100 "α" => simpleRoot

/-- The standard bilinear form on `B →₀ ℝ`. Given by `⟪αᵢ, αⱼ⟫ = -cos (π / Mᵢⱼ)`
for `i j : B`, where {αᵢ} is the standard basis of `B →₀ ℝ` and `M` is the Coxeter matrix.
This is positive definite if and only if the associated Coxeter group is finite. -/
def standardBilinForm (M : Matrix B B ℕ) : LinearMap.BilinForm ℝ V :=
    (Finsupp.lift (V →ₗ[ℝ] ℝ) ℝ B)
        (fun i ↦ ((Finsupp.lift ℝ ℝ B)
            (fun i' ↦ -cos (π / M i i'))))

local notation:max "⟪"  a  ","  b  "⟫" => Matrix.standardBilinForm M a b

@[simp] theorem standardBilinForm_simpleRoot_self (i : B) :
    ⟪α i, α i⟫ = 1 := by simp [standardBilinForm, simpleRoot, hM.diagonal i]

variable (M)

@[simp] theorem standardBilinForm_simpleRoot_simpleRoot (i i' : B) :
    ⟪α i, α i'⟫ = - cos (π / M i i') := by simp [standardBilinForm, simpleRoot]

variable {M}

theorem isSymm_standardBilinForm : LinearMap.IsSymm (standardBilinForm M) := by
  apply LinearMap.isSymm_iff_eq_flip.mpr
  apply (Finsupp.basisSingleOne).ext
  intro i
  apply (Finsupp.basisSingleOne).ext
  intro i'
  simp [standardBilinForm, hM.symmetric.apply i i']

variable (M)

/-- The orthogonal reflection in the vector `v` under the standard bilinear form.
-/
def orthoReflection {v : V} (hv : ⟪v, v⟫ = 1) :
    V →ₗ[ℝ] V := Module.reflection (show ((2 : ℝ) • (standardBilinForm M v)) v = 2 by
      rw [LinearMap.smul_apply, hv]; norm_num)

local prefix:100 "r" => M.orthoReflection

attribute [local simp] Module.reflection
attribute [local simp] Module.preReflection

@[simp] theorem orthoReflection_apply_self {v : V} (hv : ⟪v, v⟫ = 1) : (r hv) v = -v :=
  Module.reflection_apply_self _

theorem orthoReflection_sqr_eq_id {v : V} (hv : ⟪v, v⟫ = 1) :
    (r hv) * (r hv) = LinearMap.id := by
  apply LinearMap.ext
  exact Module.involutive_reflection _

theorem orthoReflection_eq_iff {v v' : V} (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) :
    r hv = r hv' ↔ ∃ μ : ℝ, v' = μ • v := by
  constructor
  · intro h
    have h₁ : (r hv) v' = (r hv') v' := LinearMap.ext_iff.mp h v'
    rw [M.orthoReflection_apply_self hv'] at h₁
    dsimp [orthoReflection] at h₁
    apply congrArg (v' + ·) at h₁
    rw [add_right_neg, add_sub, ← two_smul ℝ v'] at h₁
    apply sub_eq_zero.mp at h₁
    apply congrArg (((1 : ℝ) / 2) • ·) at h₁
    rw [smul_smul, smul_smul, ← mul_assoc] at h₁
    norm_num at h₁
    use ⟪v, v'⟫
  · rintro ⟨μ, rfl⟩
    simp only [SMulHomClass.map_smul, LinearMap.smul_apply, smul_eq_mul] at hv'
    simp only [map_smul, smul_apply, smul_eq_mul, hv, mul_one] at hv'
    -- hv': μ * μ = 1
    apply LinearMap.ext
    intro w
    dsimp [orthoReflection]
    rw [smul_smul, SMulHomClass.map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc 2,
        mul_comm _ μ, ← mul_assoc μ, hv']
    simp

/-- Any orthogonal reflection is orthogonal with respect to the standard bilinear form. -/
theorem standardBilinForm_compl₁₂_orthoReflection {v : V} (hv : ⟪v, v⟫ = 1) :
    LinearMap.compl₁₂ M.standardBilinForm (r hv) (r hv)  = M.standardBilinForm := by
  apply LinearMap.ext
  intro w
  apply LinearMap.ext
  intro w'
  dsimp [orthoReflection]
  simp only [map_sub, SMulHomClass.map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [← (isSymm_standardBilinForm hM).eq v w, RingHom.id_apply, hv]
  ring

variable {M}

/-- The orthogonal reflection in the standard basis vector `αᵢ` under the standard bilinear form. -/
def simpleOrthoReflection (i : B) := r (standardBilinForm_simpleRoot_self hM i)

local prefix:100 "σ" => Matrix.simpleOrthoReflection hM

theorem simpleOrthoReflection_simpleRoot (i i' : B) :
    (σ i) (α i') = α i' + (2 * cos (Real.pi / M i i')) • α i := by
  dsimp [simpleOrthoReflection, orthoReflection]
  rw [standardBilinForm_simpleRoot_simpleRoot]
  rw [sub_eq_add_neg, ← neg_smul]
  congr
  ring

@[simp] theorem simpleOrthoReflection_simpleRoot_self (i : B) : (σ i) (α i) = -α i := by
  simp [simpleOrthoReflection_simpleRoot, hM.diagonal i, two_smul]

open Polynomial Polynomial.Chebyshev

theorem orthoReflection_mul_orthoReflection_pow_apply {v v' : V} (k : ℕ)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) :
        (((r hv) * (r hv')) ^ k) v
        = eval ⟪v, v'⟫ (U ℝ (2 * k)) • v - eval ⟪v, v'⟫ (USubOne ℝ (2 * k)) • v' := by
  induction' k with k ih
  · simp [USubOne]
  · /- Apply inductive hypothesis. -/
    rw [pow_succ, LinearMap.mul_apply, ih, LinearMap.mul_apply]

    /- Expand everything out. -/
    simp only [map_sub, map_add, map_smul]
    dsimp [orthoReflection]
    simp only [map_sub, map_add, map_smul, smul_sub, smul_add, smul_smul, hv, hv',
      SMulHomClass.map_smul, LinearMap.smul_apply]

    /- Move all terms to the left-hand side. -/
    apply sub_eq_zero.mp

    /- Rewrite using μ = ⟪v, v'⟫. -/
    rw [(by rw[← (isSymm_standardBilinForm hM).eq v' v]; simp : ⟪v', v⟫ = ⟪v, v'⟫)]
    set μ := ⟪v, v'⟫

    /- Sort the terms and write the entire expression as a • v + b • v'. -/
    simp only [sub_eq_add_neg, neg_add, ← neg_smul, smul_eq_mul]
    have h₁ : ∀ a b : ℝ, a • v + b • v = (a + b) • v :=
      fun _ _ ↦ (add_smul _ _ _).symm
    have h₂ : ∀ a b : ℝ, a • v' + b • v' = (a + b) • v' :=
      fun _ _ ↦ (add_smul _ _ _).symm
    have h₃ : ∀ a b : ℝ, a • v' + b • v = b • v + a • v' :=
      fun _ _ ↦ add_comm _ _
    have h₄ : ∀ a b c : ℝ, a • v + b • v' + c • v = (a + c) • v + b • v' :=
      fun a b c ↦ (add_right_comm _ _ _).trans (congrArg (· + _) (h₁ a c))
    have h₅ : ∀ a b c : ℝ, a • v + b • v' + c • v' = a • v + (b + c) • v' :=
      fun a b c ↦ (add_assoc _ _ _).trans (congrArg (_ + ·) (h₂ b c))
    simp only [← add_assoc, h₁, h₂, h₃, h₄, h₅]

    /- Put everything remaining in ring normal form. -/
    rw [Nat.succ_eq_add_one]
    dsimp only [USubOne]
    ring_nf

    /- Write the coefficients of v and v' as polynomials in μ. -/
    have h₁ : ∀ P : ℝ[X], eval μ P * μ ^ 2 = eval μ (X ^ 2 * P) := by simp [mul_comm]
    have h₂ : ∀ P : ℝ[X], μ * eval μ P = eval μ (X * P) := by simp
    have h₃ : ∀ P : ℝ[X], μ * eval μ P = eval μ (X * P) := by simp
    have h₄ : ∀ P : ℝ[X], eval μ P * 2 = eval μ (2 * P) := by simp [mul_comm]
    have h₅ : ∀ P : ℝ[X], eval μ P * 4 = eval μ (4 * P) := by simp [mul_comm]
    simp only [← eval_add, ← eval_mul_X, ← eval_sub, ← eval_neg, h₁, h₂, h₃, h₄, h₅]

    /- Use the recurrence relations for the Chebyshev polynomials to rewrite
    all the occurrences of U ℝ (3 + k * 2), U ℝ (2 + k * 2), U ℝ (1 + k * 2).
    -/
    rw [(by ring : 1 + k * 2 = k * 2 + 1),
        (by ring : 2 + k * 2 = k * 2 + 1 + 1),
        (by ring : 3 + k * 2 = k * 2 + 1 + 1 + 1)]
    simp only [U_eq_X_mul_U_add_T]
    ring_nf

    /- Then do the same for T ℝ (2 + k * 2) and T ℝ (3 + k * 2). -/
    rw [(by ring : 2 + k * 2 = k * 2 + 2),
        (by ring : 3 + k * 2 = k * 2 + 1 + 2)]
    simp only [T_eq_X_mul_T_sub_pol_U]
    simp only [U_eq_X_mul_U_add_T]

    ring_nf
    simp

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v {v v' : V} {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m > 1) :
        (((r hv) * (r hv')) ^ m) v = v := by
  rw [orthoReflection_mul_orthoReflection_pow_apply hM, hvv']
  rw [U_real_neg_cos_eq _ hm, USubOne_real_neg_cos_eq _ hm]
  rw [Nat.cast_mul, Nat.cast_two, add_div, mul_div_cancel 2 (by positivity : (m : ℝ) ≠ 0),
    mul_add π, mul_comm π, mul_one_div, add_comm (2 * π)]
  rw [sin_add_two_pi, sin_two_pi]
  rw [mul_div_cancel _ (sin_pi_div_m_ne_zero hm)]
  simp

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v' {v v' : V} {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m > 1) :
        (((r hv) * (r hv')) ^ m) v' = v' := let a := r hv; let b := r hv'; calc
  ((a * b) ^ m) v'
  _ = (b * b * (a * b) ^ m) v'         := by simp [M.orthoReflection_sqr_eq_id hv']
  _ = (b * (b * (a * b) ^ m)) v'       := by rw [mul_assoc]
  _ = (b * ((b * a) ^ m * b)) v'       := by
    congr 2
    exact (SemiconjBy.eq (SemiconjBy.pow_right (by unfold SemiconjBy; group) m))
  _ = (b * (b * a) ^ m * b) v'         := by rw [mul_assoc]
  _ = (b * (b * a) ^ m) (b v')         := LinearMap.mul_apply _ _ _
  _ = (b * (b * a) ^ m) (-v')          := congrArg _ (M.orthoReflection_apply_self hv')
  _ = -((b * (b * a) ^ m) v')          := map_neg _ _
  _ = -(b (((b * a) ^ m) v'))          := congrArg _ (LinearMap.mul_apply _ _ _)
  _ = -(b v')                          := by
    congr
    apply orthoReflection_mul_orthoReflection_pow_order_apply_v hM
    · rwa [← (isSymm_standardBilinForm hM).eq v v', RingHom.id_apply]
    · assumption
  _ = -(-v')                           := congrArg _ (M.orthoReflection_apply_self hv')
  _ = v'                               := neg_neg v'

private lemma can_decomp_into_parallel_and_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m > 1) :
    ∃ μ₁ μ₂ : ℝ, ⟪v, w - μ₁ • v - μ₂ • v'⟫ = 0 ∧ ⟪v', w - μ₁ • v - μ₂ • v'⟫ = 0 := by
  use (1 / (sin (π / m)) ^ 2) * (⟪v, w⟫ + cos (π / m) * ⟪v', w⟫)
  use (1 / (sin (π / m)) ^ 2) * (⟪v', w⟫ + cos (π / m) * ⟪v, w⟫)

  -- Expand everything out.
  simp only [mul_add, LinearMap.map_sub, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]

  -- Use known values of bilinear form.
  rw [(by rw[← (isSymm_standardBilinForm hM).eq v' v]; simp : ⟪v', v⟫ = ⟪v, v'⟫)]
  simp only [hv, hv', hvv']
  field_simp [Polynomial.Chebyshev.sin_pi_div_m_ne_zero hm]
  ring_nf

  constructor
  all_goals {
    rw [Real.sin_sq]
    ring
  }

private lemma fixed_of_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvw : ⟪v, w⟫ = 0) (hv'w : ⟪v', w⟫ = 0) :
    (((r hv) * (r hv')) ^ m) w = w := by
  induction' m with m ih
  · simp
  · rw [pow_succ, LinearMap.mul_apply, ih, LinearMap.mul_apply]
    dsimp [orthoReflection]
    simp [hvw, hv'w]

private lemma orthoReflection_mul_orthoReflection_pow_order {v v' : V} {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m ≠ 1) :
    ((r hv) * (r hv')) ^ m = 1 := by
  rcases Nat.lt_or_gt_of_ne hm with mlt | mgt
  · simp [Nat.lt_one_iff.mp mlt]
  · apply LinearMap.ext
    intro w
    rcases can_decomp_into_parallel_and_orthogonal hM w hv hv' hvv' mgt with ⟨μ₁, μ₂, hμ⟩
    set! w' := w - μ₁ • v - μ₂ • v' with hw'
    rw [← hw'] at hμ
    rcases hμ with ⟨h₁, h₂⟩

    have h₃ : w = w' + μ₁ • v + μ₂ • v' := by rw [hw']; abel
    simp only [h₃, LinearMap.map_add, LinearMap.map_smul, LinearMap.one_apply]
    congr
    · exact fixed_of_orthogonal w' hv hv' h₁ h₂
    · exact orthoReflection_mul_orthoReflection_pow_order_apply_v hM hv hv' hvv' mgt
    · exact orthoReflection_mul_orthoReflection_pow_order_apply_v' hM hv hv' hvv' mgt

end Matrix

namespace CoxeterSystem

variable {W : Type*} [Group W]
variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simpleReflection
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "α" => Matrix.simpleRoot
local notation:max "⟪"  a  ","  b  "⟫" => Matrix.standardBilinForm M a b
local notation:100 "σ" i => Matrix.simpleOrthoReflection (cs.isCoxeter) i
local notation "V" => B →₀ ℝ

/-- The standard geometric representation on `B →₀ ℝ`. For `i : B`, the simple reflection `sᵢ`
acts by `sᵢ v = v - 2 ⟪αᵢ, v⟫ * αᵢ`, where {αᵢ} is the standard basis of `B →₀ ℝ`.
-/
def standardGeometricRepresentation : Representation ℝ W V := cs.lift (
  show IsLiftable M (fun i ↦ σ i) by
    unfold IsLiftable
    intro i i'
    dsimp
    rcases em (i = i') with rfl | ne
    · simp [Matrix.simpleOrthoReflection, Matrix.orthoReflection_sqr_eq_id, ← LinearMap.one_eq_id]
    · let m := M i i'
      have hm : m ≠ 1 := cs.isCoxeter.off_diagonal i i' ne
      apply Matrix.orthoReflection_mul_orthoReflection_pow_order cs.isCoxeter
      · exact Matrix.standardBilinForm_simpleRoot_simpleRoot M i i'
      · exact hm
)

noncomputable alias SGR := standardGeometricRepresentation

local prefix:100 "ρ" => cs.SGR

theorem SGR_simple (i : B) : ρ (s i) = σ i := cs.lift_apply_simple _ i

/-- The standard geometric representation preserves the standard bilinear form. -/
theorem standardBilinForm_compl₁₂_SGR_apply (w : W) :
    M.standardBilinForm.compl₁₂ (ρ w) (ρ w) = M.standardBilinForm := by
  apply cs.simple_induction w
  · intro i
    rw [SGR_simple, Matrix.simpleOrthoReflection,
      Matrix.standardBilinForm_compl₁₂_orthoReflection _ cs.isCoxeter]
  · rw [map_one, LinearMap.one_eq_id, LinearMap.compl₁₂_id_id]
  · intro w w' hw hw'
    rw [map_mul, mul_eq_comp, LinearMap.compl₁₂_comp_comp, hw, hw']

theorem SGR_alternatingWord_apply_simpleRoot (i i' : B) (m : ℕ) (hM : M i i' > 1) :
    cs.SGR (π (alternatingWord i i' m)) (α i) = if Even m
      then (sin ((m + 1) * π / M i i') / sin (π / M i i')) • (α i)
        + (sin (m * π / M i i') / sin (π / M i i')) • (α i')
      else (sin (m * π / M i i') / sin (π / M i i')) • (α i)
        + (sin ((m + 1) * π / M i i') / sin (π / M i i')) • (α i') := by
  rw [prod_alternatingWord_eq_pow, map_mul, map_pow, map_mul, apply_ite cs.SGR, map_one, mul_apply]
  simp only [SGR_simple]
  nth_rw 3 [Matrix.simpleOrthoReflection]
  nth_rw 2 [Matrix.simpleOrthoReflection]
  rw [Matrix.orthoReflection_mul_orthoReflection_pow_apply cs.isCoxeter]
  simp only [Matrix.standardBilinForm_simpleRoot_simpleRoot]
  rw [Polynomial.Chebyshev.USubOne_real_neg_cos_eq _ hM,
    Polynomial.Chebyshev.U_real_neg_cos_eq _ hM]
  simp only [pow_mul, (by norm_num : (-1 : ℝ) ^ 2 = 1), one_pow, one_mul]
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [if_pos (by use k), if_pos (by use k), one_apply, neg_smul, sub_neg_eq_add]
    rw [← two_mul, Nat.mul_div_cancel_left _ (by norm_num : 2 > 0)]
    congr 4 <;> (field_simp; ring)
  · rw [if_neg (by apply Nat.odd_iff_not_even.mp; use k),
      if_neg (by apply Nat.odd_iff_not_even.mp; use k), neg_smul, sub_neg_eq_add]
    have h₁ : (2 * k + 1) / 2 = k := by rw [Nat.mul_add_div (by positivity)]; norm_num
    have h₂ : (2 * k : ℕ) = 2 * (k : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_two]
    have h₃ : (2 * k + 1 : ℕ) = 2 * (k : ℝ) + 1 := by
      rw [Nat.cast_add, h₂, Nat.cast_one]
    simp only [h₁, h₂, h₃]
    simp only [map_add, map_smul, map_smul]
    rw [Matrix.simpleOrthoReflection_simpleRoot_self, Matrix.simpleOrthoReflection_simpleRoot]
    rw [smul_neg, ← neg_smul, smul_add, smul_smul, add_assoc, ← add_smul]
    congr 3
    · congr 1
      field_simp
      ring
    · field_simp [Polynomial.Chebyshev.sin_pi_div_m_ne_zero]
      have : (2 * k + 1 + 1) * π / M i i' = (2 * k + 1) * π / M i i' + π / M i i' := by
        field_simp
        ring
      rw [this, sin_add]
      have : π * (2 * k) / M i i' = (2 * k + 1) * π / M i i' - π / M i i' := by
        field_simp
        ring
      rw [this, sin_sub]
      rw [cs.isCoxeter.symmetric.apply i i']
      ring_nf


theorem SGR_alternatingWord_apply_simpleRoot' (i i' : B) (m : ℕ) (hM : M i i' = 0) :
    cs.SGR (π (alternatingWord i i' m)) (α i) = if Even m
      then (m + 1) • (α i) + m • (α i')
      else m • (α i) + (m + 1) • (α i') := by
  sorry

theorem SGR_alternatingWord_apply_simpleRoot_eq_nonneg_smul_add_nonneg_smul
    (i i' : B) (m : ℕ) (hm : m < M i i' ∨ M i i' = 0) :
    ∃ (μ μ' : ℝ), μ ≥ 0 ∧ μ' ≥ 0 ∧
      cs.SGR (π (alternatingWord i i' m)) (α i) = μ • (α i) + μ' • (α i') := by
  sorry

-- TODO: The order of s_i s_i' is actually M_{i, i'}

/-- The proposition that all the coordinates of `v` in the basis of simple roots are nonnegative. -/
def IsPositive (v : V) := ∀ i : B, v i ≥ 0
/-- The proposition that all the coordinates of `v` in the basis of simple roots are nonpositive. -/
def IsNegative (v : V) := ∀ i : B, v i ≤ 0

theorem SGR_apply_simpleRoot_pos_of {w : W} {i : B} (h : ℓ (w * s i) = ℓ w + 1) :
    IsPositive (cs.SGR w (α i)) := by
  sorry

theorem SGR_apply_simpleRoot_neg_of {w : W} {i : B} (h : ℓ (w * s i) + 1 = ℓ w) :
    IsNegative (cs.SGR w (α i)) := by
  sorry

theorem SGR_apply_simpleRoot_pos_iff (w : W) (i : B) :
    ℓ (w * s i) = ℓ w + 1 ↔ IsPositive (cs.SGR w (α i)) := by
  sorry

theorem SGR_apply_simpleRoot_neg_iff (w : W) (i : B) :
    ℓ (w * s i) + 1 = ℓ w ↔ IsNegative (cs.SGR w (α i)) := by
  sorry

theorem injective_SGR : Function.Injective cs.SGR := by
  sorry

alias faithful_SGR := injective_SGR

end CoxeterSystem

end
