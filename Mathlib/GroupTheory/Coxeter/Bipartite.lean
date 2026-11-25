/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Coxeter.ReflectionSystem
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Bipartite reflection systems

Let `B : Matrix ι ι K` be a symmetric matrix and let `p : ι → Prop` split the index set into
two parts such that `B i j = 0` whenever `i ≠ j` lie in the same part (`IsBipartition B p`).
Conjugating by the diagonal sign matrix `signFlip p = diag(±1)` (with `-1` on the nodes
satisfying `p`) negates every off-diagonal entry of `B` connecting the two parts, so
`signFlip p * B * signFlip p = -negDiag B`, where `negDiag B` negates the diagonal of `B`.

Since the generating reflections of `B` and `-B` coincide, conjugation by `signFlip p` sends each
generating reflection of `B` to the corresponding generating reflection of `negDiag B`.
Consequently every word in the reflections of `B` is conjugate to the same word in the
reflections of `negDiag B`, and in particular these have the same characteristic polynomial.

We also record that reflections in the same part commute, so products of reflections over one part
do not depend on the order, and that the two "bipartite Coxeter elements" `s₊ s₋` and `s₋ s₊`
are conjugate.

## Main definitions
* `ReflectionSystem.negDiag`: negate the diagonal entries of a matrix.
* `ReflectionSystem.negDiagSystem`: the reflection system with form `negDiag S.B`.
* `ReflectionSystem.IsBipartition`: `p` splits the nodes into two parts with no edges inside
  either part.
* `ReflectionSystem.signFlip`: the diagonal sign matrix `diag(±1)` attached to `p`.

## Main results
* `ReflectionSystem.signFlip_mul_mul_signFlip`: `P * B * P = -negDiag B`.
* `ReflectionSystem.signFlip_mul_reflectionMatrix_mul_signFlip`:
  `P * s_i(B) * P = s_i(negDiag B)`.
* `ReflectionSystem.isConj_prod_reflectionMatrix_negDiag` and
  `ReflectionSystem.charpoly_prod_reflectionMatrix_negDiag`: words in the reflections of `B` and
  of `negDiag B` are conjugate and have the same characteristic polynomial.
* `ReflectionSystem.prod_map_reflectionMatrix_eq_of_perm`: a product of reflections from a single
  part is independent of the order of the factors.
* `ReflectionSystem.isConj_prod_append_comm`: `s_u s_v` is conjugate to `s_v s_u`.

## References
* J. K. Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems*, PhD thesis,
  Florida State University (2012), Theorem 1.4 and Proposition 3.32.
-/

open Matrix

@[expose] public section

namespace ReflectionSystem

variable {ι K : Type*} [Field K]

/-- `p` splits the nodes into two parts with no edges inside either part: `B i j = 0` whenever
`i ≠ j` and `p i ↔ p j`. -/
def IsBipartition (B : Matrix ι ι K) (p : ι → Prop) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → (p i ↔ p j) → B i j = 0

variable [DecidableEq ι]

/-- Negate the diagonal entries of a matrix. -/
def negDiag (B : Matrix ι ι K) : Matrix ι ι K :=
  of fun i j ↦ if i = j then -B i j else B i j

@[simp]
lemma negDiag_apply (B : Matrix ι ι K) (i j : ι) :
    negDiag B i j = if i = j then -B i j else B i j := rfl

lemma negDiag_isSymm {B : Matrix ι ι K} (hB : B.IsSymm) : (negDiag B).IsSymm := by
  ext i j
  simp only [transpose_apply, negDiag_apply]
  by_cases h : i = j
  · subst h
    rfl
  · simp [h, Ne.symm h, hB.apply i j]

/-- The reflection system obtained from `S` by negating all diagonal entries of its form. -/
def negDiagSystem (S : ReflectionSystem ι K) : ReflectionSystem ι K where
  B := negDiag S.B
  B_symm := negDiag_isSymm S.B_symm
  B_diag_ne_zero i := by simp [S.B_diag_ne_zero i]

section signFlip

variable (p : ι → Prop) [DecidablePred p]

/-- The diagonal sign matrix with `-1` on the nodes satisfying `p` and `1` elsewhere. -/
def signFlip : Matrix ι ι K :=
  diagonal fun i ↦ if p i then -1 else 1

lemma signFlip_apply (i j : ι) :
    signFlip (K := K) p i j = if i = j then (if p i then -1 else 1) else 0 :=
  diagonal_apply _ i j

lemma signFlip_transpose : (signFlip (K := K) p)ᵀ = signFlip p :=
  diagonal_transpose _

variable [Fintype ι]

lemma signFlip_mul_self : signFlip (K := K) p * signFlip p = 1 := by
  rw [signFlip, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

variable {p}

/-- Conjugating a bipartite form by `signFlip p` negates it and then negates its diagonal back. -/
theorem signFlip_mul_mul_signFlip {B : Matrix ι ι K} (hB : IsBipartition B p) :
    signFlip p * B * signFlip p = -negDiag B := by
  ext i j
  simp only [signFlip, mul_diagonal, diagonal_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hi : p i <;> simp [hi]
  · by_cases hp : (p i ↔ p j)
    · simp [hij, hB hij hp]
    · by_cases hi : p i <;> by_cases hj : p j <;> simp_all

/-- Conjugation by `signFlip p` sends the reflections of `B` to those of `negDiag B`. -/
theorem signFlip_mul_reflectionMatrix_mul_signFlip {B : Matrix ι ι K} (hB : IsBipartition B p)
    (i : ι) :
    signFlip p * reflectionMatrix B i * signFlip p = reflectionMatrix (negDiag B) i := by
  ext r c
  simp only [signFlip, mul_diagonal, diagonal_mul, reflectionMatrix_apply, negDiag_apply]
  by_cases hri : r = i
  · subst hri
    by_cases hrc : r = c
    · subst hrc
      by_cases hr : p r <;> simp [hr]
    · by_cases hp : (p r ↔ p c)
      · simp [hrc, hB hrc hp]
      · by_cases hr : p r <;> by_cases hc : p c <;> simp_all [div_neg]
  · by_cases hrc : r = c
    · subst hrc
      by_cases hr : p r <;> simp [hr, hri]
    · simp [hri, hrc]

/-- Conjugation by `signFlip p` sends a word in the reflections of `B` to the same word in the
reflections of `negDiag B`. -/
theorem signFlip_mul_prod_mul_signFlip {B : Matrix ι ι K} (hB : IsBipartition B p)
    (w : List ι) :
    signFlip p * (w.map (reflectionMatrix B)).prod * signFlip p =
      (w.map (reflectionMatrix (negDiag B))).prod := by
  induction w with
  | nil => simp [signFlip_mul_self]
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih,
      ← signFlip_mul_reflectionMatrix_mul_signFlip hB a]
    calc signFlip p * (reflectionMatrix B a * (t.map (reflectionMatrix B)).prod) * signFlip p
        = signFlip p * reflectionMatrix B a * (signFlip p * signFlip p) *
            (t.map (reflectionMatrix B)).prod * signFlip p := by
          rw [signFlip_mul_self, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

end signFlip

variable [Fintype ι] {p : ι → Prop}

/-- A word in the reflections of a bipartite form `B` is conjugate to the same word in the
reflections of `negDiag B`. -/
theorem isConj_prod_reflectionMatrix_negDiag {B : Matrix ι ι K} (hB : IsBipartition B p)
    (w : List ι) :
    IsConj (w.map (reflectionMatrix B)).prod (w.map (reflectionMatrix (negDiag B))).prod := by
  classical
  refine ⟨⟨signFlip p, signFlip p, signFlip_mul_self p, signFlip_mul_self p⟩, ?_⟩
  change signFlip p * _ = _ * signFlip p
  rw [← signFlip_mul_prod_mul_signFlip hB, Matrix.mul_assoc, signFlip_mul_self, Matrix.mul_one]

/-- A word in the reflections of a bipartite form `B` has the same characteristic polynomial as
the same word in the reflections of `negDiag B`. -/
theorem charpoly_prod_reflectionMatrix_negDiag {B : Matrix ι ι K} (hB : IsBipartition B p)
    (w : List ι) :
    (w.map (reflectionMatrix (negDiag B))).prod.charpoly =
      (w.map (reflectionMatrix B)).prod.charpoly := by
  classical
  rw [← signFlip_mul_prod_mul_signFlip hB, Matrix.mul_assoc, Matrix.charpoly_mul_comm,
    Matrix.mul_assoc, signFlip_mul_self, Matrix.mul_one]

/-- In a bipartite reflection system, reflections in the same part commute. -/
theorem reflectionMatrix_comm_of_isBipartition (S : ReflectionSystem ι K)
    (hB : IsBipartition S.B p) {i j : ι} (hij : p i ↔ p j) :
    reflectionMatrix S.B i * reflectionMatrix S.B j =
      reflectionMatrix S.B j * reflectionMatrix S.B i := by
  by_cases h : i = j
  · rw [h]
  · exact S.reflectionMatrix_comm_of_orthogonal (hB h hij)

/-- A product of reflections all lying in the same part does not depend on the order. -/
theorem prod_map_reflectionMatrix_eq_of_perm (S : ReflectionSystem ι K)
    (hB : IsBipartition S.B p) {l₁ l₂ : List ι} (h : l₁.Perm l₂)
    (hl : ∀ i ∈ l₁, ∀ j ∈ l₁, p i ↔ p j) :
    (l₁.map (reflectionMatrix S.B)).prod = (l₂.map (reflectionMatrix S.B)).prod :=
  (h.map _).prod_eq' <| List.pairwise_map.2 <| List.pairwise_of_forall_mem_list
    fun i hi j hj ↦ S.reflectionMatrix_comm_of_isBipartition hB (hl i hi j hj)

variable (S : ReflectionSystem ι K)

/-- A word product of reflections is inverted by the reversed word. -/
theorem prod_map_mul_prod_map_reverse (u : List ι) :
    (u.map (reflectionMatrix S.B)).prod * (u.reverse.map (reflectionMatrix S.B)).prod = 1 := by
  induction u with
  | nil => simp
  | cons a t ih =>
    simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
    calc reflectionMatrix S.B a * (t.map (reflectionMatrix S.B)).prod *
          ((t.reverse.map (reflectionMatrix S.B)).prod * reflectionMatrix S.B a)
        = reflectionMatrix S.B a * ((t.map (reflectionMatrix S.B)).prod *
            (t.reverse.map (reflectionMatrix S.B)).prod) * reflectionMatrix S.B a := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ih, Matrix.mul_one, S.reflectionMatrix_mul_self]

/-- For any words `u` and `v`, the products `s_u s_v` and `s_v s_u` are conjugate. In particular,
the two bipartite Coxeter elements `s₊ s₋` and `s₋ s₊` are conjugate. -/
theorem isConj_prod_append_comm (u v : List ι) :
    IsConj ((u ++ v).map (reflectionMatrix S.B)).prod
      ((v ++ u).map (reflectionMatrix S.B)).prod := by
  have h1 := S.prod_map_mul_prod_map_reverse u
  have h2 : (u.reverse.map (reflectionMatrix S.B)).prod * (u.map (reflectionMatrix S.B)).prod =
      1 := by
    have := S.prod_map_mul_prod_map_reverse u.reverse
    rwa [List.reverse_reverse] at this
  refine ⟨⟨_, _, h2, h1⟩, ?_⟩
  change _ * _ = _ * _
  simp only [List.map_append, List.prod_append]
  rw [← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

end ReflectionSystem
