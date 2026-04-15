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

/-- A **word** of length `n` over the field `F`: an arbitrary vector in $\mathbb{F}_q^n$,
equipped with the Hamming distance. -/
abbrev Word (n : ℕ) : Type _ := Hamming (fun _ : Fin n ↦ F)

/-- An **$[n, k]_q$-linear code** is a $k$-dimensional subspace of $\mathbb{F}_q^n$. -/
structure LinearCode (n k : ℕ) where
  /-- The underlying $k$-dimensional subspace of $\mathbb{F}_q^n$, encoded as `Fin n → F`. -/
  carrier : Subspace F (Fin n → F)
  /-- The `F`-rank of `carrier` equals `k`. -/
  dim : Module.finrank F carrier = k

/-- The **minimum distance** $d(C)$ of a code $C$ is the infimum of the Hamming weights of its
non-zero elements. -/
noncomputable def minDist {n k : ℕ} (C : LinearCode F n k) : ℕ :=
  sInf {w | ∃ x : Fin n → F, x ∈ C.carrier ∧ x ≠ 0 ∧ w = hammingNorm x}

/-- An **$[n, k, d]$-linear code** is an $[n, k]$-linear code with minimum distance at least
`d`. -/
structure LinearCodeWithDist (n k d : ℕ) extends LinearCode F n k where
  /-- The minimum distance of `code` is at least `d`. -/
  dist_lower_bound : d ≤ minDist F toLinearCode

omit [Fintype F] in
/-- The minimum distance is a lower bound for the Hamming distance between any two distinct
codewords. -/
lemma minDist_le_hammingDist {n k : ℕ} (C : LinearCode F n k) {x y : Fin n → F}
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) (hxy : x ≠ y) :
    minDist F C ≤ hammingDist x y := by
  apply Nat.sInf_le
  refine ⟨-x + y, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.neg_mem _ hx) hy
  · exact fun h ↦ hxy (neg_add_eq_zero.mp h)
  · rw [hammingDist_eq_hammingNorm]

omit [Fintype F] in
/-- A nontrivial code attains its minimum distance at some pair of distinct codewords. -/
lemma exists_pair_hammingDist_eq_minDist {n k : ℕ} (C : LinearCode F n k)
    [Nontrivial C.carrier] :
    ∃ x ∈ C.carrier, ∃ y ∈ C.carrier, x ≠ y ∧ hammingDist x y = minDist F C := by
  have hne : {w | ∃ x : Fin n → F, x ∈ C.carrier ∧ x ≠ 0 ∧ w = hammingNorm x}.Nonempty := by
    obtain ⟨⟨z, hz_mem⟩, hz_ne⟩ := exists_ne (0 : C.carrier)
    exact ⟨hammingNorm z, z, hz_mem, fun h ↦ hz_ne (Subtype.ext h), rfl⟩
  obtain ⟨z, hz_mem, hz_ne, hz_eq⟩ := Nat.sInf_mem hne
  refine ⟨z, hz_mem, 0, Submodule.zero_mem _, hz_ne, ?_⟩
  rw [hammingDist_zero_right]
  exact hz_eq.symm

omit [Fintype F] in
/-- The minimum distance of a code coincides with the infimum of pairwise Hamming distances
between distinct codewords. -/
lemma minDist_eq_sInf_pairwiseDist {n k : ℕ} (C : LinearCode F n k) :
    minDist F C = sInf {d | ∃ x ∈ C.carrier, ∃ y ∈ C.carrier, x ≠ y ∧ d = hammingDist x y} := by
  unfold minDist
  congr 1
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx_space, hx_ne, rfl⟩
    exact ⟨x, hx_space, 0, Submodule.zero_mem C.carrier, hx_ne, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨y - x, Submodule.sub_mem _ hy hx, sub_ne_zero.mpr (Ne.symm hxy), ?_⟩
    rw [hammingDist_eq_hammingNorm x y]
    congr 1
    abel

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
    (c₁ c₂ : Fin n → F) (hc₁ : c₁ ∈ C.carrier) (hc₂ : c₂ ∈ C.carrier)
    (h_ne : c₁ ≠ c₂) :
    Disjoint (hammingSphere F c₁ t) (hammingSphere F c₂ t) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have h_dist_le_2t : hammingDist c₁ c₂ ≤ 2 * t :=
    calc hammingDist c₁ c₂
      _ ≤ hammingDist c₁ z + hammingDist z c₂ := hammingDist_triangle c₁ z c₂
      _ = hammingDist c₁ z + hammingDist c₂ z := by rw [hammingDist_comm z c₂]
      _ ≤ t + t                               := add_le_add hz₁ hz₂
      _ = 2 * t                               := by omega
  have h_minDist_le_dist : minDist F C.toLinearCode ≤ hammingDist c₁ c₂ := by
    rw [minDist_eq_sInf_pairwiseDist F C.toLinearCode]
    apply csInf_le (OrderBot.bddBelow _)
    simp only [Set.mem_setOf_eq]
    exact ⟨c₁, hc₁, c₂, hc₂, h_ne, rfl⟩
  have h_d_le_2t : d ≤ 2 * t :=
    calc d ≤ minDist F C.toLinearCode  := C.dist_lower_bound
      _ ≤ hammingDist c₁ c₂            := h_minDist_le_dist
      _ ≤ 2 * t                        := h_dist_le_2t
  omega

end InformationTheory
