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
$$\rho(s_i) v = v - \langle \alpha_i, v\rangle \alpha_i.$$
Every reflection of $W$ acts by a reflection in the standard geometric representation.
We also define the associated set of *roots* $\Phi = \{\rho(w) \alpha_i : w \in W, i \in B\}$.
(If `W` is infinite, then this is not a root system in the sense of
`Mathlib.LinearAlgebra.RootSystem` because it is infinite and because `B →₀ ℝ` is not an inner
product space.)

We prove that every root is either *positive* or *negative*; that is, it either has all nonnegative
coordinates or all nonpositive coordinates when written in the standard basis $\{\alpha_i\}$.
Every reflection $t \in W$ (see `Mathlib.GroupTheory.Coxeter.Length`) has a corresponding positive
root $\beta_t$. For all $w \in W$, we prove that $\rho(w) \beta_t$ is negative if and only if $t$ is
a right inversion of $w$.

## Main definitions
* `cs.standardBilinForm`: The invariant bilinear form associated to the standard geometric
representation.
* `cs.standardGeometricRepresentation`: The standard geometric representation of `W`. This has type
`Representation ℝ W (B →₀ ℝ)`.
* `cs.roots`
* `cs.posRoots`
* `cs.negRoots`

## References
* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*][bjorner2005]
-/

noncomputable section

namespace CoxeterSystem

open List Matrix Function Real

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simpleReflection
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

/-! ### The standard geometric representation
Given a Coxeter group `W` whose simple reflections are indexed by a set `B`, we define
the standard geometric representation of `W`, which is a representation of `W` with underlying
vector space `B →₀ ℝ`. We then use this to define the set of roots, which is a subset of
`B →₀ ℝ`. The roots correspond two-to-one to the reflections of `W`.
-/

def simpleRoot (i : B) : B →₀ ℝ := Finsupp.single i 1
local prefix:100 "α" => simpleRoot

/-- The standard bilinear form on `B →₀ ℝ`. Given by `⟪αᵢ, αⱼ⟫ = -cos (π / Mᵢⱼ)`
for `i j : B`, where {αᵢ} is the standard basis of `B →₀ ℝ` and `M` is the Coxeter matrix.
This is positive definite if and only if the associated Coxeter group is finite. -/
def standardBilinForm (M : Matrix B B ℕ) : LinearMap.BilinForm ℝ (B →₀ ℝ) :=
    (Finsupp.lift ((B →₀ ℝ) →ₗ[ℝ] ℝ) ℝ B)
        (fun i ↦ ((Finsupp.lift ℝ ℝ B)
            (fun i' ↦ -cos (Real.pi / M i i'))))

local notation:max "⟪"  a  ","  b  "⟫" => standardBilinForm M a b

@[simp] theorem standardBilinForm_simpleRoot_self (i : B) :
    ⟪α i, α i⟫ = 1 := by simp [standardBilinForm, simpleRoot, cs.isCoxeter.diagonal i]

@[simp] theorem standardBilinForm_simpleRoot_simpleRoot (i i' : B) :
    ⟪α i, α i'⟫ = - cos (Real.pi / M i i') := by simp [standardBilinForm, simpleRoot]

theorem isSymm_standardBilinForm :
    LinearMap.IsSymm (standardBilinForm M) := by
  apply LinearMap.isSymm_iff_eq_flip.mpr
  apply (Finsupp.basisSingleOne).ext
  intro i
  apply (Finsupp.basisSingleOne).ext
  intro i'
  simp [standardBilinForm]
  rw [cs.isCoxeter.symmetric.apply i i']

/-- The orthogonal reflection in the vector `v` under the standard bilinear form.
-/
def orthoReflection (cs : CoxeterSystem M W) (v : B →₀ ℝ) :
    (B →₀ ℝ) →ₗ[ℝ] (B →₀ ℝ) := sorry

theorem orthoReflection_sqr_eq_id {v : B →₀ ℝ} (hv : ⟪v, v⟫ = 1) :
    (cs.orthoReflection v) * (cs.orthoReflection v) = LinearMap.id := by
  sorry

theorem orthoReflection_eq_iff {v v' : B →₀ ℝ} (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) :
    cs.orthoReflection v = cs.orthoReflection v' ↔ ∃ μ : ℝ, v' = μ • v := by
  sorry

/-- The standard geometric representation on `B →₀ ℝ`. For `i : B`, the simple reflection `sᵢ`
acts by `sᵢ v = v - 2 ⟪αᵢ, v⟫ * αᵢ`, where {αᵢ} is the standard basis of `B →₀ ℝ`.
-/
def standardGeometricRepresentation (cs : CoxeterSystem M W) : Representation ℝ W (B →₀ ℝ) := sorry

alias SGR := standardGeometricRepresentation

theorem SGR_simple (i : B) : cs.SGR (s i) = cs.orthoReflection (α i) := by
  sorry

theorem SGR_simple_simpleRoot (i i' : B) :
    cs.SGR (s i) (α i') = α i' + ((2 : ℝ) * cos (Real.pi / M i i')) • α i := by
  sorry

theorem SGR_simple_simpleRoot_self (i : B) : cs.SGR (s i) (α i) = -α i := by
  sorry

theorem SGR_bilin_eq_bilin (w : W) (v v' : B →₀ ℝ) : ⟪cs.SGR w v, cs.SGR w v'⟫ = ⟪v, v'⟫ := by
  sorry

theorem SGR_alternatingWord_simpleRoot (i i' : B) (m : ℕ) (hM : M i i' ≠ 0) :
    cs.SGR (π (alternatingWord i i' m)) (α i) = if Even m
      then (sin ((m + 1) * Real.pi / M i i') / sin (Real.pi / M i i')) • (α i)
        + (sin (m * Real.pi / M i i') / sin (Real.pi / M i i')) • (α i')
      else (sin (m * Real.pi / M i i') / sin (Real.pi / M i i')) • (α i)
        + (sin ((m + 1) * Real.pi / M i i') / sin (Real.pi / M i i')) • (α i') := by
  sorry

theorem SGR_alternatingWord_simpleRoot' (i i' : B) (m : ℕ) (hM : M i i' = 0) :
    cs.SGR (π (alternatingWord i i' m)) (α i) = if Even m
      then (m + 1) • (α i) + m • (α i')
      else m • (α i) + (m + 1) • (α i') := by
  sorry

theorem SGR_alternatingWord_simpleRoot_pos (i i' : B) (m : ℕ) (hm : m < M i i' ∨ M i i' = 0) :
    ∃ (μ μ' : ℝ), μ ≥ 0 ∧ μ' ≥ 0 ∧
      cs.SGR (π (alternatingWord i i' m)) (α i) = μ • (α i) + μ' • (α i') := by
  sorry

/-- The roots of the standard geometric representation; i.e. the vectors that can be written
in the form w αᵢ, where `w : W` and {αᵢ} is the standard basis of `B →₀ ℝ`. If `W` is infinite,
then this is not a root system in the sense of `Mathlib.LinearAlgebra.RootSystem` because it is
infinite and because `B →₀ ℝ` is not an inner product space.
-/
def roots : Set (B →₀ ℝ) := {v : B →₀ ℝ | ∃ w : W, ∃ i : B, v = cs.SGR w (α i)}

/-- The roots that can be written as a nonnegative linear combination of the standard basis vectors
`αᵢ`.-/
def posRoots : Set (B →₀ ℝ) := cs.roots ∩ {v : B →₀ ℝ | ∀ i : B, v i ≥ 0}
/-- The roots that can be written as a nonpositive linear combination of the standard basis vectors
`αᵢ`.-/
def negRoots : Set (B →₀ ℝ) := cs.roots ∩ {v : B →₀ ℝ | ∀ i : B, v i ≤ 0}

@[simp] theorem roots_invariant (w : W) (v : B →₀ ℝ) : cs.SGR w v ∈ cs.roots ↔ v ∈ cs.roots := by
  sorry

@[simp] theorem roots_eq_neg_roots : -cs.roots = cs.roots := by
  sorry

theorem negRoots_eq_neg_posRoots : cs.negRoots = -cs.posRoots := by
  sorry

theorem SGR_simpleRoot_mem_posRoot_of (w : W) (i : B) :
    ℓ (w * s i) = ℓ w + 1 → cs.SGR w (α i) ∈ cs.posRoots := by
  sorry

theorem SGR_simpleRoot_mem_negRoot_of (w : W) (i : B) :
    ℓ (w * s i) + 1 = ℓ w → cs.SGR w (α i) ∈ cs.negRoots := by
  sorry

theorem SGR_simpleRoot_mem_posRoot_iff (w : W) (i : B) :
    ℓ (w * s i) = ℓ w + 1 ↔ cs.SGR w (α i) ∈ cs.posRoots := by
  sorry

theorem SGR_simpleRoot_mem_negRoot_iff (w : W) (i : B) :
    ℓ (w * s i) + 1 = ℓ w ↔ cs.SGR w (α i) ∈ cs.negRoots := by
  sorry

theorem root_pos_or_neg : cs.roots = cs.posRoots ∪ cs.negRoots := by
  sorry

theorem root_not_pos_and_neg : cs.posRoots ∩ cs.negRoots = ∅ := by
  sorry

theorem SGR_injective : Injective cs.SGR := by
  sorry

def reflectionToRoot : cs.reflections ≃ cs.posRoots := sorry

theorem reflection_by_smul (w : W) (v : B →₀ ℝ) :
    cs.orthoReflection (cs.SGR w v) = (cs.SGR w) ∘ (cs.orthoReflection v) ∘ (cs.SGR w⁻¹) := by
  sorry

theorem reflection_by_root (γ : cs.posRoots) :
    cs.orthoReflection γ = cs.SGR (cs.reflectionToRoot.invFun γ) := by
  sorry

theorem isRightInversion_iff (w : W) (t : cs.reflections) : cs.IsRightInversion w t ↔
    cs.SGR w (cs.reflectionToRoot.toFun t) ∈ cs.negRoots := by
  sorry

end CoxeterSystem

end
