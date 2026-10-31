/-
Copyright (c) 2026 Richie Caputo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richie Caputo
-/
module

public import Mathlib.Analysis.Matrix.Inertia
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# The line graph signature identity

For a finite simple graph `G` with `n` vertices and `m` edges, let `L(G)` denote its line graph,
`A(L(G))` the adjacency matrix of the line graph (over `ℝ`), and `Q(G) = D(G) + A(G)` the
signless Laplacian of `G`.  This file proves the classical identity

  `s(A(L(G))) = n - m + p - q`

where `s` is the signature (number of positive minus number of negative eigenvalues, with
multiplicity) and `(p, q)` are the numbers of positive/negative eigenvalues of `Q(G) - 2•1`,
i.e. `(p, q, z) = In(Q(G) - 2I)` in inertia notation.

## Proof outline

The `V × E(G)` incidence matrix `B` satisfies the two Gram identities

* `Bᵀ * B = A(L(G)) + 2•1` (`SimpleGraph.transpose_mul_edgeIncMatrix`),
* `B * Bᵀ = Q(G)` (`SimpleGraph.edgeIncMatrix_mul_transpose`).

By `Matrix.charpoly_mul_comm'` (the rectangular AB-vs-BA characteristic polynomial identity),
`X ^ n * charpoly (Bᵀ * B) = X ^ m * charpoly (B * Bᵀ)`.  Since both matrices are real
symmetric, their characteristic polynomials split over their eigenvalues
(`Matrix.IsHermitian.roots_charpoly_add_smul_one`), so the two root multisets agree:

  `n •{0} + {μᵢ + 2} = m •{0} + {νⱼ + 2}`

where `μ` runs over the eigenvalues of `A(L(G))` and `ν` over those of `Q(G) - 2•1`.
Counting elements `> 2` gives `pos(A(L(G))) = p`; counting elements `< 2` gives
`n + neg(A(L(G))) = m + q`.  Subtracting yields the identity.

## Main definitions

* `SimpleGraph.signlessLapMatrix`: the signless Laplacian `Q(G) = D(G) + A(G)`.
* `SimpleGraph.edgeIncMatrix`: the `V × E(G)` incidence matrix, i.e. the restriction of
  `SimpleGraph.incMatrix` to the columns indexed by actual edges.

## Main result

* `SimpleGraph.signature_adjMatrix_lineGraph`: the line graph signature identity.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The signless Laplacian `Q(G) = D(G) + A(G)` of a simple graph. -/
def signlessLapMatrix (R : Type*) [AddMonoidWithOne R] : Matrix V V R :=
  G.degMatrix R + G.adjMatrix R

instance : DecidableRel (G.lineGraph.Adj) := fun e f =>
  decidable_of_iff (e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V))
    lineGraph_adj_iff_exists.symm

/-- The `V × E(G)` incidence matrix of a simple graph: the restriction of
`SimpleGraph.incMatrix` to the columns indexed by actual edges. -/
def edgeIncMatrix (R : Type*) [Zero R] [One R] : Matrix V G.edgeSet R :=
  (G.incMatrix R).submatrix id Subtype.val

variable (R : Type*)

/-- Gram identity I: `B * Bᵀ` is the signless Laplacian `Q(G)`, where `B` is the `V × E(G)`
incidence matrix. -/
theorem edgeIncMatrix_mul_transpose [Semiring R] :
    G.edgeIncMatrix R * (G.edgeIncMatrix R)ᵀ = G.signlessLapMatrix R := by
  have hfull : G.incMatrix R * (G.incMatrix R)ᵀ = G.signlessLapMatrix R := by
    rw [incMatrix_mul_transpose]
    ext a b
    simp only [of_apply, signlessLapMatrix, degMatrix, Matrix.add_apply, Matrix.diagonal_apply,
      adjMatrix_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  rw [← hfull]
  ext a b
  simp only [Matrix.mul_apply, edgeIncMatrix, Matrix.submatrix_apply, Matrix.transpose_apply,
    id_eq]
  rw [← Finset.sum_subtype G.edgeFinset (fun x => G.mem_edgeFinset)
      (fun e => G.incMatrix R a e * G.incMatrix R b e)]
  exact Finset.sum_subset (Finset.subset_univ _) fun e _ he =>
    mul_eq_zero_of_left (G.incMatrix_of_notMem_incidenceSet fun hmem =>
      he (G.mem_edgeFinset.mpr (G.incidenceSet_subset a hmem))) _

/-- Gram identity II: `Bᵀ * B = A(L(G)) + 2•1`, where `B` is the `V × E(G)` incidence matrix
and `A(L(G))` is the adjacency matrix of the line graph. -/
theorem transpose_mul_edgeIncMatrix [NonAssocSemiring R] :
    (G.edgeIncMatrix R)ᵀ * G.edgeIncMatrix R = G.lineGraph.adjMatrix R + (2 : R) • 1 := by
  ext e f
  have hentry : ((G.edgeIncMatrix R)ᵀ * G.edgeIncMatrix R) e f
      = ∑ a : V, G.incMatrix R a ↑e * G.incMatrix R a ↑f := by
    simp [Matrix.mul_apply, edgeIncMatrix]
  rw [hentry, Matrix.add_apply, Matrix.smul_apply, adjMatrix_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hef : e = f
  · subst hef
    rw [if_neg (G.lineGraph.irrefl), if_pos rfl, mul_one, zero_add]
    have h2 := G.incMatrix_transpose_mul_diag (R := R) (e := (e : Sym2 V))
    rw [if_pos e.2, Matrix.mul_apply] at h2
    simp only [Matrix.transpose_apply] at h2
    exact h2
  · rw [if_neg hef, mul_zero, add_zero]
    have hterm : ∀ a : V, G.incMatrix R a ↑e * G.incMatrix R a ↑f
        = if a ∈ (e : Sym2 V) ∧ a ∈ (f : Sym2 V) then (1 : R) else 0 := fun a => by
      rw [incMatrix_apply', incMatrix_apply', ite_zero_mul_ite_zero, one_mul]
      simp only [edge_mem_incidenceSet_iff]
    simp only [hterm]
    by_cases hadj : G.lineGraph.Adj e f
    · rw [if_pos hadj]
      obtain ⟨-, v₀, hv₀e, hv₀f⟩ := lineGraph_adj_iff_exists.mp hadj
      refine (Finset.sum_eq_single_of_mem v₀ (Finset.mem_univ v₀) fun b _ hb => ?_).trans
        (if_pos ⟨hv₀e, hv₀f⟩)
      rw [if_neg]
      rintro ⟨hbe, hbf⟩
      exact hef (Subtype.ext (((Sym2.mem_and_mem_iff hb).mp ⟨hbe, hv₀e⟩).trans
        ((Sym2.mem_and_mem_iff hb).mp ⟨hbf, hv₀f⟩).symm))
    · rw [if_neg hadj]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg]
      rintro ⟨hae, haf⟩
      exact hadj (lineGraph_adj_iff_exists.mpr ⟨hef, a, hae, haf⟩)

variable {R}

omit [DecidableRel G.Adj] in
/-- The adjacency matrix of the line graph is real symmetric. -/
theorem isHermitian_adjMatrix_lineGraph : (G.lineGraph.adjMatrix ℝ).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans (isSymm_adjMatrix _)

/-- `Q(G) - 2•1` is real symmetric. -/
theorem isHermitian_signlessLapMatrix_sub_two_smul_one :
    (G.signlessLapMatrix ℝ - (2 : ℝ) • 1).IsHermitian :=
  (((G.isHermitian_degMatrix (R := ℝ)).add
      ((Matrix.conjTranspose_eq_transpose_of_trivial _).trans (isSymm_adjMatrix _))).sub
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)))

section CountingHelpers

private theorem countP_replicate_zero_of_not {p : ℝ → Prop} [DecidablePred p] (hp : ¬p 0)
    (k : ℕ) : Multiset.countP p (Multiset.replicate k (0 : ℝ)) = 0 :=
  Multiset.countP_eq_zero.mpr fun _ ha => by
    rw [Multiset.eq_of_mem_replicate ha]; exact hp

private theorem countP_replicate_of_pos {p : ℝ → Prop} [DecidablePred p] (hp : p 0) (k : ℕ) :
    Multiset.countP p (Multiset.replicate k (0 : ℝ)) = k := by
  rw [Multiset.countP_eq_card.mpr fun _ ha => by
    rw [Multiset.eq_of_mem_replicate ha]; exact hp, Multiset.card_replicate]

private theorem countP_two_lt_aux {ι : Type*} [Fintype ι] (g : ι → ℝ) (k : ℕ) :
    Multiset.countP (fun x : ℝ => 2 < x)
        (Multiset.replicate k (0 : ℝ) + Finset.univ.val.map fun i => g i + 2)
      = (Finset.univ.filter fun i => 0 < g i).card := by
  have hfilter : (Finset.univ.val.filter fun i => (2 : ℝ) < g i + 2)
      = Finset.univ.val.filter fun i => 0 < g i :=
    Multiset.filter_congr fun i _ => by constructor <;> intro h <;> linarith
  rw [Multiset.countP_add, countP_replicate_zero_of_not (by norm_num), zero_add,
    Multiset.countP_map, hfilter, Finset.card_def, Finset.filter_val]

private theorem countP_lt_two_aux {ι : Type*} [Fintype ι] (g : ι → ℝ) (k : ℕ) :
    Multiset.countP (fun x : ℝ => x < 2)
        (Multiset.replicate k (0 : ℝ) + Finset.univ.val.map fun i => g i + 2)
      = k + (Finset.univ.filter fun i => g i < 0).card := by
  have hfilter : (Finset.univ.val.filter fun i => g i + 2 < 2)
      = Finset.univ.val.filter fun i => g i < 0 :=
    Multiset.filter_congr fun i _ => by constructor <;> intro h <;> linarith
  rw [Multiset.countP_add, countP_replicate_of_pos (by norm_num),
    Multiset.countP_map, hfilter, Finset.card_def, Finset.filter_val]

end CountingHelpers

/-- **The line graph signature identity.**

For a finite simple graph `G` with `n` vertices and `m` edges,

  `s(A(L(G))) = n - m + p - q`

where `s` is the signature of the adjacency matrix of the line graph `L(G)` and `(p, q)` are
the numbers of positive/negative eigenvalues of `Q(G) - 2•1` (with `Q(G)` the signless
Laplacian), all counted with multiplicity.

This is the Gram-pairing argument: the incidence matrix `B` pairs
`Bᵀ * B = A(L(G)) + 2•1` with `B * Bᵀ = Q(G)`, which have equal nonzero spectra. -/
theorem signature_adjMatrix_lineGraph :
    (G.isHermitian_adjMatrix_lineGraph).signature
      = (Fintype.card V : ℤ) - (Fintype.card G.edgeSet : ℤ)
        + (G.isHermitian_signlessLapMatrix_sub_two_smul_one).posInertia
        - (G.isHermitian_signlessLapMatrix_sub_two_smul_one).negInertia := by
  set hL := G.isHermitian_adjMatrix_lineGraph with hLdef
  set hQ := G.isHermitian_signlessLapMatrix_sub_two_smul_one with hQdef
  -- the rectangular AB-vs-BA characteristic polynomial identity for the Gram pair
  have hkey := Matrix.charpoly_mul_comm' (G.edgeIncMatrix ℝ)ᵀ (G.edgeIncMatrix ℝ)
  rw [G.transpose_mul_edgeIncMatrix ℝ, G.edgeIncMatrix_mul_transpose ℝ] at hkey
  have hsplit : G.signlessLapMatrix ℝ
      = G.signlessLapMatrix ℝ - (2 : ℝ) • 1 + (2 : ℝ) • 1 := by abel
  rw [hsplit] at hkey
  -- pass to root multisets
  have hroots := congrArg Polynomial.roots hkey
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (Matrix.charpoly_monic _).ne_zero),
      Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (Matrix.charpoly_monic _).ne_zero),
      Polynomial.roots_X_pow, Polynomial.roots_X_pow,
      hL.roots_charpoly_add_smul_one 2, hQ.roots_charpoly_add_smul_one 2,
      Multiset.nsmul_singleton, Multiset.nsmul_singleton] at hroots
  -- count roots `> 2` on both sides: positive inertia transfers
  have h1 := congrArg (Multiset.countP fun x : ℝ => 2 < x) hroots
  rw [countP_two_lt_aux, countP_two_lt_aux] at h1
  -- count roots `< 2` on both sides: negative inertia transfers, shifted by the paddings
  have h2 := congrArg (Multiset.countP fun x : ℝ => x < 2) hroots
  rw [countP_lt_two_aux, countP_lt_two_aux] at h2
  simp only [Matrix.IsHermitian.signature, Matrix.IsHermitian.posInertia,
    Matrix.IsHermitian.negInertia]
  omega

end SimpleGraph
