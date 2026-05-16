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
public import Mathlib.Topology.MetricSpace.Infsep

/-!
# Linear codes over finite fields

This file defines linear codes over a finite field $F$ and establishes basic
properties of their minimum Hamming distance.

## Main definitions

* `LinearCode`: A linear code of length $n$, i.e., a subspace of $F^n$.
* `minDist`: The minimum Hamming distance $d(C)$ of a linear code `C`.
* `LinearCodeWithDist`: An $[n, d]$-linear code, i.e., a linear code whose minimum distance
  is at least $d$.
* `hammingSphere`: The Hamming sphere of a given radius centred at a vector in $F^n$.

## Main statements

* `minDist_eq_sInf`: The minimum distance of `C`, defined via `Set.infsep`, equals the infimum
  of the Hamming distances between distinct codewords.
* `minDist_eq_sInf_weights`: The minimum distance of `C` equals the infimum of Hamming weights
  of nonzero codewords.
* `disjoint_hammingSphere`: If $2t < d$, the Hamming spheres of radius $t$ centred at distinct
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

/-- A **linear code** of length `n` is a subspace of $F^n$. -/
abbrev LinearCode (n : ℕ) := Subspace F (Word F n)

/-- The **minimum distance** $d(C)$ of a code $C$ is the infimum separation (`Set.infsep`) of
the set of codewords, i.e. the infimum of the Hamming distances between distinct codewords. -/
noncomputable def minDist {n : ℕ} (C : LinearCode F n) : ℕ :=
  ⌊(C : Set (Word F n)).infsep⌋₊

/-- An **$[n, d]$-linear code** is a linear code of length `n` with minimum distance at
least `d`. -/
structure LinearCodeWithDist (n d : ℕ) where
  /-- The underlying linear code of length `n`. -/
  carrier : LinearCode F n
  /-- The minimum distance of `carrier` is at least `d`. -/
  dist_lower_bound : d ≤ minDist F carrier

omit [Fintype F] in
/-- The minimum distance is a lower bound for the Hamming weight of any nonzero codeword. -/
lemma minDist_le_hammingNorm {n : ℕ} (C : LinearCode F n) {x : Fin n → F}
    (hx : x ∈ C) (hx_ne : x ≠ 0) :
    minDist F C ≤ hammingNorm x := by
  have h0 : (0 : Word F n) ∈ (C : Set (Word F n)) := C.zero_mem
  have h := Set.infsep_le_dist_of_mem (s := (C : Set (Word F n))) hx h0 hx_ne
  calc minDist F C = ⌊(C : Set (Word F n)).infsep⌋₊ := rfl
    _ ≤ ⌊(hammingNorm x : ℝ)⌋₊ := Nat.floor_mono h
    _ = hammingNorm x := Nat.floor_natCast _

omit [Fintype F] in
/-- The minimum distance of a code coincides with the infimum of the Hamming distances
between distinct codewords. -/
lemma minDist_eq_sInf {n : ℕ} [Finite F] (C : LinearCode F n) :
    minDist F C = sInf {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ d = hammingDist x y} := by
  letI := Fintype.ofFinite F
  rcases Set.subsingleton_or_nontrivial (C : Set (Word F n)) with hC | hC
  · have hempty :
        {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ d = hammingDist x y} = (∅ : Set ℕ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro d ⟨x, hx, y, hy, hxy, -⟩
      exact hxy (hC hx hy)
    rw [hempty, Nat.sInf_empty]
    change ⌊(C : Set (Word F n)).infsep⌋₊ = 0
    rw [hC.infsep_zero, Nat.floor_zero]
  · obtain ⟨a, ha, b, hb, hab, hsep⟩ :=
      (Set.toFinite (C : Set (Word F n))).infsep_exists_of_nontrivial hC
    have haS : hammingDist a b ∈
        {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ d = hammingDist x y} := ⟨a, ha, b, hb, hab, rfl⟩
    have hfloor : minDist F C = hammingDist a b := by
      change ⌊(C : Set (Word F n)).infsep⌋₊ = hammingDist a b
      rw [hsep]
      exact Nat.floor_natCast _
    rw [hfloor]
    refine le_antisymm (le_csInf ⟨_, haS⟩ ?_) (Nat.sInf_le haS)
    rintro d ⟨x, hx, y, hy, hxy, rfl⟩
    have h := Set.infsep_le_dist_of_mem (s := (C : Set (Word F n))) hx hy hxy
    calc hammingDist a b = ⌊(C : Set (Word F n)).infsep⌋₊ := hfloor.symm
      _ ≤ ⌊(hammingDist x y : ℝ)⌋₊ := Nat.floor_mono h
      _ = hammingDist x y := Nat.floor_natCast _

omit [Fintype F] in
/-- A nontrivial code attains its minimum distance as the Hamming weight of some nonzero
codeword. -/
lemma exists_hammingNorm_eq_minDist {n : ℕ} [Finite F] (C : LinearCode F n)
    [Nontrivial C] :
    ∃ x ∈ C, x ≠ 0 ∧ hammingNorm x = minDist F C := by
  have hne : {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ d = hammingDist x y}.Nonempty := by
    obtain ⟨⟨z, hz_mem⟩, hz_ne⟩ := exists_ne (0 : C)
    refine ⟨hammingDist z 0, z, hz_mem, 0, Submodule.zero_mem _, ?_, rfl⟩
    exact fun h ↦ hz_ne (Subtype.ext h)
  obtain ⟨x, hx_mem, y, hy_mem, hxy, hxy_eq⟩ := Nat.sInf_mem hne
  refine ⟨-x + y, Submodule.add_mem _ (Submodule.neg_mem _ hx_mem) hy_mem,
    fun h ↦ hxy (neg_add_eq_zero.mp h), ?_⟩
  rw [minDist_eq_sInf]
  exact (hxy_eq.trans (hammingDist_eq_hammingNorm x y)).symm

omit [Fintype F] in
/-- The minimum distance of a code coincides with the infimum of Hamming weights of nonzero
codewords. -/
lemma minDist_eq_sInf_weights {n : ℕ} [Finite F] (C : LinearCode F n) :
    minDist F C = sInf {w | ∃ x : Fin n → F, x ∈ C ∧ x ≠ 0 ∧ w = hammingNorm x} := by
  rw [minDist_eq_sInf]
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
theorem disjoint_hammingSphere {n d t : ℕ} (C : LinearCodeWithDist F n d)
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
      _ ≤ t + t := add_le_add hz₁ hz₂
      _ = 2 * t := by omega
  have h_minDist_le_dist : minDist F C.carrier ≤ hammingDist c₁ c₂ := by
    have h := Set.infsep_le_dist_of_mem
      (s := (C.carrier : Set (Word F n))) hc₁ hc₂ h_ne
    calc minDist F C.carrier = ⌊(C.carrier : Set (Word F n)).infsep⌋₊ := rfl
      _ ≤ ⌊(hammingDist c₁ c₂ : ℝ)⌋₊ := Nat.floor_mono h
      _ = hammingDist c₁ c₂ := Nat.floor_natCast _
  have h_d_le_2t : d ≤ 2 * t :=
    calc d ≤ minDist F C.carrier := C.dist_lower_bound
      _ ≤ hammingDist c₁ c₂ := h_minDist_le_dist
      _ ≤ 2 * t := h_dist_le_2t
  omega

end InformationTheory
