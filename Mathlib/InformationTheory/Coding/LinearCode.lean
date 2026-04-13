/-
Copyright (c) 2026 Cristina Dueñas Navarro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cristina Dueñas Navarro
-/
module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linear codes over finite fields

This file defines linear codes over a finite field $\mathbb{F}_q$ and establishes basic
properties of their minimum Hamming distance.

## Main definitions

* `LinearCode`: An $[n, k]_q$-linear code, i.e., a $k$-dimensional subspace of $\mathbb{F}_q^n$.
* `minDist`: The minimum Hamming distance $d(C)$ of a linear code `C`.
* `LinearCodeWithDist`: An $[n, k, d]$-linear code, i.e., a linear code whose minimum distance
  is at least $d$.
* `hammingSphere`: The Hamming sphere of a given radius centred at a vector in $\mathbb{F}_q^n$.

## Main statements

* `minDist_eq_sInf_pairwiseDist`: The minimum distance of `C` equals the infimum of pairwise
  Hamming distances between distinct codewords.
* `disjoint_spheres`: If $2t < d$, the Hamming spheres of radius $t$ centred at distinct
  codewords are disjoint; equivalently, the code can correct up to $t$ errors.

## Implementation notes

This file assumes that `F` is a finite field $\mathbb{F}_q$ and that `q` is its order.

## Tags

linear code, minimum distance, Hamming sphere, error-correcting code
-/

@[expose] public section

namespace InformationTheory

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
variable {q : ℕ} (hq : Fintype.card F = q)

/-- An **$[n, k]_q$-linear code** is a $k$-dimensional subspace of $\mathbb{F}_q^n$. -/
structure LinearCode (n k : ℕ) where
  /-- The underlying $k$-dimensional subspace of $\mathbb{F}_q^n$, encoded as `Fin n → F`. -/
  space : Subspace F (Fin n → F)
  /-- The `F`-rank of `space` equals `k`. -/
  dim : Module.finrank F space = k

/-- The **minimum distance** $d(C)$ of a code $C$ is the infimum of the Hamming weights of its
non-zero elements. -/
noncomputable def minDist {n k : ℕ} (C : LinearCode F n k) : ℕ :=
  sInf {w | ∃ x : Fin n → F, x ∈ C.space ∧ x ≠ 0 ∧ w = hammingNorm x}

/-- An **$[n, k, d]$-linear code** is an $[n, k]$-linear code with minimum distance at least
`d`. -/
structure LinearCodeWithDist (n k d : ℕ) where
  /-- The underlying $[n, k]$-linear code. -/
  code : LinearCode F n k
  /-- The minimum distance of `code` is at least `d`. -/
  dist_lower_bound : d ≤ minDist F code

omit [Fintype F] in
/-- The minimum distance of a code coincides with the infimum of pairwise Hamming distances
between distinct codewords. -/
lemma minDist_eq_sInf_pairwiseDist {n k : ℕ} (C : LinearCode F n k) :
    minDist F C = sInf {d | ∃ x ∈ C.space, ∃ y ∈ C.space, x ≠ y ∧ d = hammingDist x y} := by
  unfold minDist
  simp_rw [← hammingDist_zero_right]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx_space, hx_ne, rfl⟩
    exact ⟨x, hx_space, 0, Submodule.zero_mem C.space, hx_ne, rfl⟩
  · rintro ⟨x, hx_space, y, hy_space, hxy_ne, rfl⟩
    have hc_space : -x + y ∈ C.space :=
      Submodule.add_mem C.space (Submodule.neg_mem C.space hx_space) hy_space
    have hc_ne : -x + y ≠ 0 := fun h => hxy_ne (neg_add_eq_zero.mp h)
    refine ⟨-x + y, hc_space, hc_ne, ?_⟩
    rw [hammingDist_eq_hammingNorm x y]
    exact hammingDist_zero_right (-x + y)

/-- The **Hamming sphere** $S_t(c)$ is the set of all vectors in $\mathbb{F}_q^n$ at Hamming
distance at most `radius` from `center`. -/
def hammingSphere {n : ℕ} (center : Fin n → F) (radius : ℕ) : Set (Fin n → F) :=
  {v | hammingDist center v ≤ radius}

omit [Fintype F] in
/-- If `d` is a lower bound for the minimum distance of a code `C` and $2t < d$
(equivalently, $t \leq \lfloor(d-1)/2\rfloor$), then the Hamming spheres of radius `t` centred
at distinct codewords are disjoint; equivalently, the code can correct up to `t` errors. -/
theorem disjoint_spheres {n k d t : ℕ} (C : LinearCodeWithDist F n k d)
    (ht : 2 * t < d)
    (c₁ c₂ : Fin n → F) (hc₁ : c₁ ∈ C.code.space) (hc₂ : c₂ ∈ C.code.space)
    (z : Fin n → F) (hz₁ : z ∈ hammingSphere F c₁ t) (hz₂ : z ∈ hammingSphere F c₂ t) :
    c₁ = c₂ := by
  by_contra h_ne
  have h_dist_le_2t : hammingDist c₁ c₂ ≤ 2 * t :=
    calc hammingDist c₁ c₂
        ≤ hammingDist c₁ z + hammingDist z c₂ := hammingDist_triangle c₁ z c₂
      _ = hammingDist c₁ z + hammingDist c₂ z := by rw [hammingDist_comm z c₂]
      _ ≤ t + t                               := add_le_add hz₁ hz₂
      _ = 2 * t                               := by omega
  have h_minDist_le_dist : minDist F C.code ≤ hammingDist c₁ c₂ := by
    rw [minDist_eq_sInf_pairwiseDist F C.code]
    apply csInf_le (OrderBot.bddBelow _)
    simp only [Set.mem_setOf_eq]
    exact ⟨c₁, hc₁, c₂, hc₂, h_ne, rfl⟩
  have h_d_le_2t : d ≤ 2 * t :=
    calc d ≤ minDist F C.code  := C.dist_lower_bound
      _ ≤ hammingDist c₁ c₂   := h_minDist_le_dist
      _ ≤ 2 * t               := h_dist_le_2t
  omega

end InformationTheory
