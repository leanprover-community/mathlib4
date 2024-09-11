/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.HasFTaylorSeries

/-!
# Faa Di Bruno formula

-/

open Set Fin Filter Function

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s : Set E} {t : Set F}
  {q : F → FormalMultilinearSeries 𝕜 F G} {p : E → FormalMultilinearSeries 𝕜 E F}

/-- A partition of `Fin n` into finitely many nonempty subsets, given by the increasing
parameterization of these subsets. We order the subsets by increasing greatest element. -/
structure OrderedFinpartition (n : ℕ) where
  /-- The number of parts in the partition -/
  k : ℕ
  /-- The size of each part -/
  partSize : Fin k → ℕ
  partSize_pos : ∀ m, 0 < partSize m
  /-- The increasing parameterization of each part -/
  emb : ∀ m, (Fin (partSize m)) → Fin n
  emb_strictMono : ∀ m, StrictMono (emb m)
  /-- The parts are ordered by increasing greatest element. -/
  parts_mono :
    StrictMono (fun (m : Fin k) ↦ emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩)
  /-- The parts are disjoint -/
  disjoint : PairwiseDisjoint univ (fun m ↦ range (emb m))
  /-- The parts cover everything -/
  cover : ⋃ m, range (emb m) = univ

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

instance : Fintype (OrderedFinpartition n) := sorry

lemma exists_inverse {n : ℕ} (c : OrderedFinpartition n) (j : Fin n) :
    ∃ p : Σ m, Fin (c.partSize m), c.emb p.1 p.2 = j := by
  have : j ∈ ⋃ m, range (c.emb m) := by rw [OrderedFinpartition.cover]; exact mem_univ _
  simp only [mem_iUnion, mem_range] at this
  rcases this with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩

/-- Given `j : Fin n`, the index of the part to which it belongs. -/
noncomputable def index (j : Fin n) : Fin c.k :=
  (c.exists_inverse j).choose.1

/-- The inverse of `c.emb` for `c : OrderedFinpartition`. It maps `j : Fin n` to the point in
`Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)`. -/
noncomputable def invEmbedding (j : Fin n) :
    Fin (c.partSize (c.index j)) := (c.exists_inverse j).choose.2

@[simp] lemma comp_invEmbedding (j : Fin n) :
    c.emb (c.index j) (c.invEmbedding j) = j :=
  (c.exists_inverse j).choose_spec

end OrderedFinpartition


namespace FormalMultilinearSeries

/-- Given a formal multilinear series `p`, a composition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.applyComposition c v i` for `v : Fin n → E` and `i : Fin c.length`. -/
def applyOrderedFinpartition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (c : OrderedFinpartition n) : (Fin n → E) → Fin c.k → F :=
  fun v m ↦ p (c.partSize m) (v ∘ c.emb m)

/-- Technical lemma stating how `p.applyOrderedFinpartition` commutes with updating variables. This
will be the key point to show that functions constructed from `applyOrderedFinpartition` retain
multilinearity. -/
theorem applyOrderedFinpartition_update
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : OrderedFinpartition n)
    (j : Fin n) (v : Fin n → E) (z : E) :
    p.applyOrderedFinpartition c (Function.update v j z) =
      Function.update (p.applyOrderedFinpartition c v) (c.index j)
        (p (c.partSize (c.index j))
          (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z)) := by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [FormalMultilinearSeries.applyOrderedFinpartition, update_same]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [FormalMultilinearSeries.applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_noteq]
    congr
    apply Function.update_comp_eq_of_not_mem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j ∈ range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

@[simp]
theorem compContinuousLinearMap_applyOrderedFinpartition {n : ℕ} (p : FormalMultilinearSeries 𝕜 F G)
    (f : E →L[𝕜] F) (c : OrderedFinpartition n) (v : Fin n → E) :
    (p.compContinuousLinearMap f).applyOrderedFinpartition c v
      = p.applyOrderedFinpartition c (f ∘ v) := by
  simp (config := {unfoldPartialApp := true}) [applyOrderedFinpartition]; rfl

end FormalMultilinearSeries


namespace ContinuousMultilinearMap

open FormalMultilinearSeries

/-- Given a formal multilinear series `p`, an ordered finite partition `c` of `n` and a continuous
multilinear map `f` in `c.length` variables, one may form a continuous multilinear map in `n`
variables by applying the right coefficient of `p` to each part of the partition, and then
applying `f` to the resulting vector. It is called `f.compAlongOrderedFinpartition p c`. -/
def compAlongOrderedFinpartition
    {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n)
    (f : ContinuousMultilinearMap 𝕜 (fun _i : Fin c.k => F) G) :
    ContinuousMultilinearMap 𝕜 (fun _i : Fin n => E) G where
  toFun v := f (p.applyOrderedFinpartition c v)
  map_add' v i x y := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyOrderedFinpartition_update, ContinuousMultilinearMap.map_add]
  map_smul' v i c x := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyOrderedFinpartition_update, ContinuousMultilinearMap.map_smul]
  cont :=
    f.cont.comp <|
      continuous_pi fun i => (coe_continuous _).comp <| continuous_pi fun j => continuous_apply _

@[simp]
theorem compAlongOrderedFinpartition_apply
    {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n)
    (f : ContinuousMultilinearMap 𝕜 (fun _i : Fin c.k => F) G) (v : Fin n → E) :
    (f.compAlongOrderedFinpartition p c) v = f (p.applyOrderedFinpartition c v) :=
  rfl

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.compAlongComposition p c`. -/
def compAlongOrderedFinpartition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) :
    ContinuousMultilinearMap 𝕜 (fun _i : Fin n => E) G :=
  (q c.k).compAlongOrderedFinpartition p c

@[simp]
theorem compAlongOrderedFinpartition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin n → E) :
    (q.compAlongOrderedFinpartition p c) v = q c.k (p.applyOrderedFinpartition c v) :=
  rfl

/-- Taylor formal composition of two formal multilinear series. The `n`-th coefficient in the
composition is defined to be the sum of `q.compAlongOrderedFinpartition p c` over all
ordered partitions of `n`. In other words, this term (as a multilinear function applied to
`v_0, ..., v_{n-1}`) is
`∑'_{k} ∑'_{I_1 ⊔ ... ⊔ I_k = {0, ..., n-1}} qₖ (p_{i_1} (...), ..., p_{i_k} (...))`, where
`i_m` is the size of `I_m` and one puts all variables of `I_m` as arguments to `p_{i_m}`, in
increasing order. The sets `I_1, ..., I_k` are ordered so that `max I_1 < max I_2 < ... < max I_k`.

This definition is chosen so that the `n`-th derivative of `g ∘ f` is the Taylor composition of
the iterated derivatives of `g` and of `f`.

Not to be confused with another notion of composition for formal multilinear series, called just
`FormalMultilinearSeries.comp`, appearing in the composition of analytic functions.
-/
protected def taylorComp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  fun n ↦ ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

end FormalMultilinearSeries

theorem faaDiBruno {n : ℕ∞} {g : F → G} {f : E → F}
    (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : MapsTo f s t) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x ↦ (q (f x)).taylorComp (p x)) s := sorry

theorem analyticWithinOn_taylorComp
    (hq : ∀ (n : ℕ), AnalyticWithinOn 𝕜 (fun x ↦ q x n) t)
    (hp : ∀ n, AnalyticWithinOn 𝕜 (fun x ↦ p x n) s) {f : E → F}
    (hf : AnalyticWithinOn 𝕜 f s) (h : MapsTo f s t) (n : ℕ) :
    AnalyticWithinOn 𝕜 (fun x ↦ (q (f x)).taylorComp (p x) n) s := sorry
