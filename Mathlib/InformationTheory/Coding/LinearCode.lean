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

* `minDist_eq_sInf_weights`: The minimum distance of `C` equals the infimum of Hamming weights
  of nonzero codewords.
* `disjoint_spheres`: If $2t < d$, the Hamming spheres of radius $t$ centred at distinct
  codewords are disjoint; equivalently, the code can correct up to $t$ errors.

## Implementation notes

This file assumes that `F` is a finite field.

## Tags

linear code, minimum distance, Hamming sphere, error-correcting code
-/

@[expose] public section

namespace InformationTheory

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- A **word** of length `n` over the field `F`: an arbitrary vector in $F^n$,
equipped with the Hamming distance. -/
abbrev Word (n : ℕ) : Type _ := Hamming (fun _ : Fin n ↦ F)

/-- An **$[n, k]$-linear code** is a $k$-dimensional subspace of $F^n$. -/
structure LinearCode (n k : ℕ) where
  /-- The underlying $k$-dimensional subspace of $F^n$, encoded as `Word F n`. -/
  carrier : Subspace F (Word F n)
  /-- The `F`-rank of `carrier` equals `k`. -/
  dim : Module.finrank F carrier = k

/-- The **minimum distance** $d(C)$ of a code $C$ is the infimum of Hamming distances between
distinct codewords. -/
noncomputable def minDist {n k : ℕ} (C : LinearCode F n k) : ℕ :=
  sInf {d | ∃ x ∈ C.carrier, ∃ y ∈ C.carrier, x ≠ y ∧ d = hammingDist x y}

/-- An **$[n, k, d]$-linear code** is an $[n, k]$-linear code with minimum distance at least
`d`. -/
structure LinearCodeWithDist (n k d : ℕ) extends LinearCode F n k where
  /-- The minimum distance of `code` is at least `d`. -/
  dist_lower_bound : d ≤ minDist F toLinearCode

omit [Fintype F] in
/-- The minimum distance is a lower bound for the Hamming weight of any nonzero codeword. -/
lemma minDist_le_hammingNorm {n k : ℕ} (C : LinearCode F n k) {x : Fin n → F}
    (hx : x ∈ C.carrier) (hx_ne : x ≠ 0) :
    minDist F C ≤ hammingNorm x := by
  apply Nat.sInf_le
  exact ⟨x, hx, 0, Submodule.zero_mem _, hx_ne, (hammingDist_zero_right x).symm⟩

omit [Fintype F] in
/-- A nontrivial code attains its minimum distance as the Hamming weight of some nonzero
codeword. -/
lemma exists_hammingNorm_eq_minDist {n k : ℕ} (C : LinearCode F n k)
    [Nontrivial C.carrier] :
    ∃ x ∈ C.carrier, x ≠ 0 ∧ hammingNorm x = minDist F C := by
  have hne : {d | ∃ x ∈ C.carrier, ∃ y ∈ C.carrier, x ≠ y ∧ d = hammingDist x y}.Nonempty := by
    obtain ⟨⟨z, hz_mem⟩, hz_ne⟩ := exists_ne (0 : C.carrier)
    refine ⟨hammingDist z 0, z, hz_mem, 0, Submodule.zero_mem _, ?_, rfl⟩
    exact fun h ↦ hz_ne (Subtype.ext h)
  obtain ⟨x, hx_mem, y, hy_mem, hxy, hxy_eq⟩ := Nat.sInf_mem hne
  exact ⟨-x + y, Submodule.add_mem _ (Submodule.neg_mem _ hx_mem) hy_mem,
    fun h ↦ hxy (neg_add_eq_zero.mp h),
    (hammingDist_eq_hammingNorm x y).symm.trans hxy_eq.symm⟩

omit [Fintype F] in
/-- The minimum distance of a code coincides with the infimum of Hamming weights of nonzero
codewords. -/
lemma minDist_eq_sInf_weights {n k : ℕ} (C : LinearCode F n k) :
    minDist F C = sInf {w | ∃ x : Fin n → F, x ∈ C.carrier ∧ x ≠ 0 ∧ w = hammingNorm x} := by
  unfold minDist
  congr 1
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨-x + y, Submodule.add_mem _ (Submodule.neg_mem _ hx) hy,
      fun h ↦ hxy (neg_add_eq_zero.mp h), hammingDist_eq_hammingNorm x y⟩
  · rintro ⟨x, hx_space, hx_ne, rfl⟩
    exact ⟨x, hx_space, 0, Submodule.zero_mem _, hx_ne, rfl⟩

/-- The **Hamming sphere** $S_t(c)$ is the set of all vectors in $F^n$ at Hamming
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
        ≤ hammingDist c₁ z + hammingDist z c₂ := hammingDist_triangle c₁ z c₂
      _ = hammingDist c₁ z + hammingDist c₂ z := by rw [hammingDist_comm z c₂]
      _ ≤ t + t                               := add_le_add hz₁ hz₂
      _ = 2 * t                               := by omega
  have h_minDist_le_dist : minDist F C.toLinearCode ≤ hammingDist c₁ c₂ := by
    apply csInf_le (OrderBot.bddBelow _)
    simp only [Set.mem_setOf_eq]
    exact ⟨c₁, hc₁, c₂, hc₂, h_ne, rfl⟩
  have h_d_le_2t : d ≤ 2 * t :=
    calc d ≤ minDist F C.toLinearCode  := C.dist_lower_bound
      _ ≤ hammingDist c₁ c₂            := h_minDist_le_dist
      _ ≤ 2 * t                        := h_dist_le_2t
  omega

end InformationTheory
