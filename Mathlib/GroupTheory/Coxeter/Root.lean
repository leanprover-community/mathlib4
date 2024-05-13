/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.GroupTheory.Coxeter.StandardGeometricRepresentation

/-! # Roots

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

As in `Mathlib/GroupTheory/Coxeter/StandardGeometricRepresentation.lean`, let $W$ be a Coxeter
group, let $V$ be the corresponding root space with simple roots $\alpha_i$ for $i \in B$, and let
let $\rho \colon W \to GL(V)$ be the corresponding standard geometric representation. A *root* of
$W$ is a vector of the form $w \alpha_i$, where $w \in W$ and $i \in B$. Clearly, $W$ acts
on the set of roots.

We prove that every root of $W$ is either positive (i.e. can be written as a linear
combination of the $\alpha_i$ with nonnegative coefficients) or negative (i.e. can be written as a
linear combination of the $\alpha_i$ with nonpositive coefficients). We also prove that every root
$\beta = w \alpha_i$ has an associated reflection $t_\beta = w s_i w^{-1} \in W$, and that the
function $\beta \mapsto t_\beta$ is a bijection between the set of positive roots and the set of
reflections of $W$. The inverse is the map $t \mapsto \beta_t$.

Then, we prove that $t$ is a right inversion of $w \in W$ if and only if $w \beta_t$ is negative.

 -/

namespace CoxeterSystem

open List Matrix Function Real

variable {B : Type*}
variable {M : CoxeterMatrix B}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq
local prefix:100 "ρ" => cs.sgr
local prefix:100 "α" => CoxeterMatrix.simpleRoot
local notation:max "⟪"  a  ","  b  "⟫" => M.standardBilinForm a b
local notation "V" => B →₀ ℝ

/-- The type of roots of `cs`. Note that this is not a root system (`RootSystem`) in the sense of
`Mathlib/LinearAlgebra/RootSystem/Defs.lean`, because it is not necessarily finite. -/
def roots : Set V := { v | ∃ (w : W) (i : B), v = (ρ w) (α i) }

/-- Roots are unit vectors. -/
theorem standardBilinForm_root_self {v : V} (hv : v ∈ cs.roots) : ⟪v, v⟫ = 1 := by
  obtain ⟨w, i, rfl⟩ := hv
  calc
    _ = ⟪α i, α i⟫        := LinearMap.congr_fun₂ (cs.standardBilinForm_compl₁₂_sgr_apply w) _ _
    _ = 1                 := M.standardBilinForm_simpleRoot_self i

/-- Every simple root is a root. -/
theorem simpleRoot_mem_roots (i : B) : α i ∈ cs.roots := by use 1, i; simp

theorem sgr_apply_simpleRoot_mem_roots (w : W) (i : B) : (ρ w) (α i) ∈ cs.roots :=
  ⟨w, i, rfl⟩

theorem sgr_apply_root_mem_roots (w : W) {v : V} (hv : v ∈ cs.roots) :
    (ρ w) v ∈ cs.roots := by
  obtain ⟨w', i, rfl⟩ := hv
  use w * w', i, by simp only [_root_.map_mul, LinearMap.mul_apply]

theorem neg_roots : -cs.roots = cs.roots := by
  suffices h : cs.roots ⊆ -cs.roots by {
    apply subset_antisymm
    · simpa using Set.neg_subset_neg.mpr h
    · exact h
  }
  rintro _ ⟨w, i, rfl⟩
  use w * (cs.simple i), i
  rw [_root_.map_mul, LinearMap.mul_apply, cs.sgr_simple]
  simp

theorem root_pos_or_neg {v : V} (hv : v ∈ cs.roots) : 0 < v ∨ v < 0 := by
  obtain ⟨w, i, rfl⟩ := hv
  obtain des | not_des := em (cs.IsRightDescent w i)
  · right
    exact cs.sgr_apply_simpleRoot_neg_iff.mpr des
  · left
    exact cs.sgr_apply_simpleRoot_pos_iff.mpr not_des

theorem abs_root_pos {v : V} (hv : v ∈ cs.roots) : 0 < |v| := by
  sorry

theorem abs_root_mem_roots {v : V} (hv : v ∈ cs.roots) : |v| ∈ cs.roots := by
  sorry

theorem orthogonalReflection_root_eq_iff {v v' : V} (hv : v ∈ cs.roots) (hv' : v' ∈ cs.roots) :
    M.orthoReflection (cs.standardBilinForm_root_self hv) =
      M.orthoReflection (cs.standardBilinForm_root_self hv') ↔
    |v| = |v'| := by
  sorry -- Use CoxeterMatrix.orthoReflection_eq_orthoReflection_iff

theorem standardBilinForm_sgr_apply_simpleRoot_self (w : W) (i : B) :
    ⟪(ρ w) (α i), (ρ w) (α i)⟫ = 1 :=
  cs.standardBilinForm_root_self <| cs.sgr_apply_simpleRoot_mem_roots w i

theorem eq_one_or_eq_neg_one_of_smul_mem_roots {v : V} {μ : ℝ} (hv : v ∈ cs.roots)
    (hμv : μ • v ∈ cs.roots) : μ = 1 ∨ μ = -1 := by
  have := cs.standardBilinForm_root_self hμv
  simp only [LinearMapClass.map_smul, LinearMap.smul_apply, cs.standardBilinForm_root_self hv,
    smul_eq_mul, mul_one] at this
  exact mul_self_eq_one_iff.mp this

theorem eq_simpleRoot_of_pos_of_sgr_simple_apply_neg {v : V} {i : B} (hv : v ∈ cs.roots)
    (v_pos : 0 < v) (iv_neg : (ρ (s i)) v < 0) : v = α i := by
  simp [sgr_simple, CoxeterMatrix.simpleOrthoReflection, CoxeterMatrix.orthoReflection,
    Module.reflection_apply] at iv_neg
  set μ := v i
  have : v = μ • α i := by
    classical
    ext i'
    unfold CoxeterMatrix.simpleRoot
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    split
    · rw [‹i = i'›.symm, smul_eq_mul, mul_one]
    · rw [smul_zero]
      apply _root_.le_antisymm
      · simpa [CoxeterMatrix.simpleRoot, Finsupp.single_apply,
          if_neg (by assumption)] using iv_neg.le i'
      · exact v_pos.le i'
  obtain one | neg_one :=
    cs.eq_one_or_eq_neg_one_of_smul_mem_roots (cs.simpleRoot_mem_roots i) (this ▸ hv)
  · simpa [one] using this
  · rw [neg_one] at this
    rw [this] at v_pos
    have := v_pos.le i
    simp [CoxeterMatrix.simpleRoot] at this
    absurd this
    linarith

theorem orthoReflection_sgr_reflection_apply (w : W) (i : B) :
    M.orthoReflection (cs.standardBilinForm_sgr_apply_simpleRoot_self w i) = ρ (w * s i * w⁻¹) := by
  apply LinearMap.ext
  intro v
  rw [_root_.map_mul, _root_.map_mul, sgr_simple]
  unfold CoxeterMatrix.simpleOrthoReflection CoxeterMatrix.orthoReflection
    Module.reflection Module.preReflection
  dsimp
  rw [map_sub, _root_.map_smul]
  congr 2
  · rw [← LinearMap.mul_apply, ← _root_.map_mul]
    simp
  · congr 1
    calc
      ⟪(ρ w) (α i), v⟫
      _ = ⟪(ρ w) (α i), (ρ w) ((ρ w⁻¹) v)⟫ := by
        rw [← LinearMap.mul_apply, ← _root_.map_mul]
        simp
      _ = ⟪α i, (ρ w⁻¹) v⟫                 :=
        LinearMap.congr_fun₂ (cs.standardBilinForm_compl₁₂_sgr_apply w) _ _

theorem sgr_apply_simple_eq_iff (w w' : W) (i i' : B) :
    |(ρ w) (α i)| = |(ρ w') (α i')| ↔ w * s i * w⁻¹ = w' * s i' * w'⁻¹ := by
  /- The previous theorem states that the orthogonal reflection with respect to the vector
  `(ρ w) (α i)` equals `ρ (w * s i * w⁻¹)`. Use `orthogonalReflection_root_eq_iff`. Result follows
  from injectivity of `ρ` -/
  sorry

/-- The root corresponding to the reflection `t = w * s i * w⁻¹` is `|(ρ w) (α i)|`.
This is well-defined by `CoxeterSystem.reflectionToRoot_conj`. If `t` is not a
reflection, this returns `0` as a junk value. -/
def reflectionToRoot (cs : CoxeterSystem M W) (t : W) : V := sorry

/-- The reflection corresponding to the root `(ρ w) (α i)` is `w * s i * w⁻¹`.
This is well-defined by `CoxeterSystem.rootToReflection_sgr_apply`. If `v` is not a root,
this returns `1` as a junk value.-/
def rootToReflection (cs : CoxeterSystem M W) (v : V) : W := sorry

theorem reflectionToRoot_conj (w : W) (i : B) :
    cs.reflectionToRoot (w * s i * w⁻¹) = |(ρ w) (α i)| := sorry

theorem rootToReflection_sgr_apply (w : W) (i : B) :
    cs.rootToReflection ((ρ w) (α i)) = w * s i * w⁻¹ := sorry

theorem rootToReflection_neg_sgr_apply (w : W) (i : B) :
    cs.rootToReflection (-(ρ w) (α i)) = w * s i * w⁻¹ := sorry

theorem reflectionToRoot_mem_roots {t : W} (ht : cs.IsReflection t) :
    cs.reflectionToRoot t ∈ cs.roots := sorry

theorem reflectionToRoot_pos {t : W} (ht : cs.IsReflection t) : cs.reflectionToRoot t > 0 :=
  sorry

theorem reflectionToRoot_eq_zero_of_not_isReflection {t : W} (ht : ¬cs.IsReflection t) :
    cs.reflectionToRoot t = 0 := sorry

theorem rootToReflection_even (v : V) : cs.rootToReflection v = cs.rootToReflection (-v) := sorry

theorem isReflection_rootToReflection {v : V} (hv : v ∈ cs.roots) :
    cs.IsReflection (cs.rootToReflection v) := sorry

theorem rootToReflection_eq_one_of_not_mem_roots {v : V} (hv : v ∈ cs.roots) :
    cs.rootToReflection v = 1 := sorry

theorem rootToReflection_reflectionToRoot {t : W} (ht : cs.IsReflection t) :
    cs.rootToReflection (cs.reflectionToRoot t) = t := sorry

theorem reflectionToRoot_rootToReflection {v : V} (hv : v ∈ cs.roots) :
    cs.reflectionToRoot (cs.rootToReflection v) = |v| := sorry

theorem bijOn_reflectionToRoot :
    Set.BijOn cs.reflectionToRoot {t | cs.IsReflection t} {v ∈ cs.roots | v > 0} := by sorry

theorem bijOn_rootToReflection_pos :
    Set.BijOn cs.rootToReflection {v ∈ cs.roots | v > 0} {t | cs.IsReflection t} := by sorry

theorem bijOn_rootToReflection_neg :
    Set.BijOn cs.rootToReflection {v ∈ cs.roots | v < 0} {t | cs.IsReflection t} := by sorry

/-- If `(ρ w) (cs.reflectionToRoot t).val < 0`, then `t` is a right inversion of `w`. -/
theorem isRightInversion_of_sgr_apply_reflectionToRoot_neg {w t : W} (ht : cs.IsReflection t)
    (ht : (ρ w) (cs.reflectionToRoot t) < 0) : cs.IsRightInversion w t := by
  sorry -- Use `cs.simple_induction_left` on the variable `w`, and then use
  -- `cs.eq_simpleRoot_of_pos_of_sgr_simple_apply_neg`

/-- `t` is a right inversion of `w` if and only if `(ρ w) (cs.reflectionToRoot t).val < 0`. -/
theorem isRightInversion_iff_sgr_apply_reflectionToRoot_neg {w t : W} (ht : cs.IsReflection t) :
    cs.IsRightInversion w t ↔ (ρ w) (cs.reflectionToRoot t) < 0 := by
  sorry -- Idea: apply `isRightInversion_of_sgr_apply_reflectionToRoot_neg` to both `(w, t)` and `(w * t, t)`

/-- `t` is not a right inversion of `w` if and only if `(ρ w) (cs.reflectionToRoot t).val > 0`. -/
theorem not_isRightInversion_iff_sgr_apply_reflectionToRoot_pos {w t : W} (ht : cs.IsReflection t) :
    ¬cs.IsRightInversion w t ↔ (ρ w) (cs.reflectionToRoot t) > 0 := by
  sorry
-- Next step is to prove that if `(ρ (π ω)) (cs.reflectionToRoot t).val < 0`,
-- then `t` is in the right inversion sequence of `ω`. Use cons-induction on `ω`.
