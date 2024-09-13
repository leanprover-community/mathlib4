/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

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
@[ext]
structure OrderedFinpartition (n : ℕ) where
  /-- The number of parts in the partition -/
  length : ℕ
  /-- The size of each part -/
  partSize : Fin length → ℕ
  partSize_pos : ∀ m, 0 < partSize m
  /-- The increasing parameterization of each part -/
  emb : ∀ m, (Fin (partSize m)) → Fin n
  emb_strictMono : ∀ m, StrictMono (emb m)
  /-- The parts are ordered by increasing greatest element. -/
  parts_strictMono :
    StrictMono (fun m ↦ emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩)
  /-- The parts are disjoint -/
  disjoint : PairwiseDisjoint univ (fun m ↦ range (emb m))
  /-- The parts cover everything -/
  cover : ⋃ m, range (emb m) = univ

namespace OrderedFinpartition

/-- The ordered finpartition of `Fin n` into singletons. -/
@[simps] def atomic (n : ℕ) : OrderedFinpartition n where
  length := n
  partSize _ :=  1
  partSize_pos _ := _root_.zero_lt_one
  emb m _ := m
  emb_strictMono _ := Subsingleton.strictMono _
  parts_strictMono := strictMono_id
  disjoint _ _ _ _ h := by simpa using h
  cover := eq_univ_of_forall (fun m ↦ by simp)

variable {n : ℕ} (c : OrderedFinpartition n)

instance : Inhabited (OrderedFinpartition n) := ⟨atomic n⟩

lemma length_le : c.length ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ c.parts_strictMono.injective

lemma partSize_le (m : Fin c.length) : c.partSize m ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (c.emb_strictMono m).injective

/-- Embedding of ordered finpartitions in a sigma type. The sigma type on the right is quite big,
but this is enough to get finiteness of ordered finpartitions. -/
def embSigma (n : ℕ) : OrderedFinpartition n →
    (Σ (l : Fin (n + 1)), Σ (p : Fin l → Fin (n + 1)), Π (i : Fin l), (Fin (p i) → Fin n)) :=
  fun c ↦ ⟨⟨c.length, Order.lt_add_one_iff.mpr c.length_le⟩,
    fun m ↦ ⟨c.partSize m, Order.lt_add_one_iff.mpr (c.partSize_le m)⟩, fun j ↦ c.emb j⟩

lemma injective_embSigma (n : ℕ) : Injective (embSigma n) := by
  rintro ⟨plength, psize, -, pemb, -, -, -, -⟩ ⟨qlength, qsize, -, qemb, -, -, -, -⟩
  intro hpq
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, mk.injEq, and_true, Fin.mk.injEq, embSigma]
  have : plength = qlength := hpq.1
  subst this
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, mk.injEq, and_true, Fin.mk.injEq, embSigma]
  ext i
  exact mk.inj_iff.mp (congr_fun hpq.1 i)

/- The best proof would probably to establish the bijection with Finpartitions, but we opt
for a direct argument, embedding `OrderedPartition n` in a type which is obviously finite. -/
noncomputable instance : Fintype (OrderedFinpartition n) :=
  Fintype.ofInjective _ (injective_embSigma n)

instance : Unique (OrderedFinpartition 0) := by
  have : Subsingleton (OrderedFinpartition 0) :=
    Fintype.card_le_one_iff_subsingleton.mp (Fintype.card_le_of_injective _ (injective_embSigma 0))
  exact Unique.mk' (OrderedFinpartition 0)

lemma exists_inverse {n : ℕ} (c : OrderedFinpartition n) (j : Fin n) :
    ∃ p : Σ m, Fin (c.partSize m), c.emb p.1 p.2 = j := by
  have : j ∈ ⋃ m, range (c.emb m) := by rw [OrderedFinpartition.cover]; exact mem_univ _
  simp only [mem_iUnion, mem_range] at this
  rcases this with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩

lemma emb_injective : Injective (fun (p : Σ m, Fin (c.partSize m)) ↦ c.emb p.1 p.2) := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ (h : c.emb m r = c.emb m' r')
  have : m = m' := by
    contrapose! h
    have A : Disjoint (range (c.emb m)) (range (c.emb m')) :=
      c.disjoint (mem_univ m) (mem_univ m') h
    apply disjoint_iff_forall_ne.1 A (mem_range_self r) (mem_range_self r')
  subst this
  simpa using (c.emb_strictMono m).injective h

/-- Given `j : Fin n`, the index of the part to which it belongs. -/
noncomputable def index (j : Fin n) : Fin c.length :=
  (c.exists_inverse j).choose.1

/-- The inverse of `c.emb` for `c : OrderedFinpartition`. It maps `j : Fin n` to the point in
`Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)`. -/
noncomputable def invEmbedding (j : Fin n) :
    Fin (c.partSize (c.index j)) := (c.exists_inverse j).choose.2

@[simp] lemma comp_invEmbedding (j : Fin n) :
    c.emb (c.index j) (c.invEmbedding j) = j :=
  (c.exists_inverse j).choose_spec

/-

structure OrderedFinpartition (n : ℕ) where
  /-- The number of parts in the partition -/
  length : ℕ
  /-- The size of each part -/
  partSize : Fin length → ℕ
  partSize_pos : ∀ m, 0 < partSize m
  /-- The increasing parameterization of each part -/
  emb : ∀ m, (Fin (partSize m)) → Fin n
  emb_strictMono : ∀ m, StrictMono (emb m)
  /-- The parts are ordered by increasing greatest element. -/
  parts_strictMono :
    StrictMono (fun m ↦ emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩)
  /-- The parts are disjoint -/
  disjoint : PairwiseDisjoint univ (fun m ↦ range (emb m))
  /-- The parts cover everything -/
  cover : ⋃ m, range (emb m) = univ
-/

/-- Extend an ordered partition of `n` entries, by adding a new singleton part to the left. -/
def extendLeft (c : OrderedFinpartition n) : OrderedFinpartition (n + 1) :=
  { length := c.length + 1
    partSize := Fin.cons 1 c.partSize
    partSize_pos := by
      apply Fin.cases
      simp
      simp [c.partSize_pos]
    emb := Fin.cases (fun _ ↦ 0) (fun m ↦ Fin.succ ∘ (c.emb m))
    emb_strictMono := sorry
    parts_strictMono := sorry
    disjoint := sorry
    cover := sorry }

/-- Extend an ordered partition of `n` entries, by adding to the `i`-th part a new point to the
left. -/
def extendMiddle (c : OrderedFinpartition n) (i : Fin c.length) : OrderedFinpartition (n + 1) :=
  { length := c.length
    partSize := update c.partSize i (c.partSize i + 1)
    partSize_pos := sorry
    emb := by
      intro m
      by_cases h : m = i
      · have : update c.partSize i (c.partSize i + 1) m = c.partSize i + 1 := by
          rw [h]; simp
        exact (Fin.cases 0 (Fin.succ ∘ (c.emb i))) ∘ (Fin.cast this)
      · have : update c.partSize i (c.partSize i + 1) m = c.partSize m := by simp [h]
        exact Fin.succ ∘ (c.emb m) ∘ (Fin.cast this)
    emb_strictMono := sorry
    parts_strictMono := sorry
    disjoint := sorry
    cover := sorry }

/-- Extend an ordered partition of `n` entries, by adding singleton to the left or appending it
to one of the existing part. -/
def extend (c : OrderedFinpartition n) (i : Option (Fin c.length)) : OrderedFinpartition (n + 1) :=
  match i with
  | none => c.extendLeft
  | some i => c.extendMiddle i

/-- Extending the ordered partitions of `Fin n` bijects with the ordered partitions
of `Fin (n+1)`. -/
def extendEquiv (n : ℕ) :
     ((i : OrderedFinpartition n) × Option (Fin i.length)) ≃ OrderedFinpartition (n + 1) :=
  { toFun := fun p ↦ p.1.extend p.2
    invFun := sorry
    left_inv := sorry
    right_inv := sorry }

/-- Given a formal multilinear series `p`, an ordered partition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.applyOrderedFinpartition c v i` for `v : Fin n → E` and `i : Fin c.k`. -/
def applyOrderedFinpartition (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F) :
    (Fin n → E) → Fin c.length → F :=
  fun v m ↦ p m (v ∘ c.emb m)

/-- An ordered finpartition gives an equivalence between `Fin n` and the disjoint union of the
parts, each of them parameterized by `Fin (c.partSize i)`. -/
noncomputable def equivSigma : ((i : Fin c.length) × Fin (c.partSize i)) ≃ Fin n where
  toFun p := c.emb p.1 p.2
  invFun i := ⟨c.index i, c.invEmbedding i⟩
  right_inv _ := by simp
  left_inv _ := by apply c.emb_injective; simp

@[to_additive] lemma prod_sigma_eq_prod {α : Type*} [CommMonoid α] (v : Fin n → α) :
    ∏ (m : Fin c.length), ∏ (r : Fin (c.partSize m)), v (c.emb m r) = ∏ i, v i := by
  rw [Finset.prod_sigma']
  exact Fintype.prod_equiv c.equivSigma _ _ (fun p ↦ rfl)

/-- Technical lemma stating how `p.applyOrderedFinpartition` commutes with updating variables. This
will be the key point to show that functions constructed from `applyOrderedFinpartition` retain
multilinearity. -/
theorem applyOrderedFinpartition_update_right
    (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F)
    (j : Fin n) (v : Fin n → E) (z : E) :
    c.applyOrderedFinpartition p (update v j z) =
      update (c.applyOrderedFinpartition p v) (c.index j)
        (p (c.index j)
          (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z)) := by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [applyOrderedFinpartition, update_same]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_noteq]
    congr
    apply Function.update_comp_eq_of_not_mem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j ∈ range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

theorem applyOrderedFinpartition_update_left (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F)
    (m : Fin c.length) (v : Fin n → E) (q : E[×c.partSize m]→L[𝕜] F) :
    c.applyOrderedFinpartition (update p m q) v
      = update (c.applyOrderedFinpartition p v) m (q (v ∘ c.emb m)) := by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

/-- Given a an ordered finite partition `c` of `n`, a continuous multilinear map `f` in `c.length`
variable, and for each `m` a continuous multilinear map `p m` in `c.partSize m` variables,
one can form a continuous multilinear map in `n`
variables by applying `p m` to each part of the partition, and then
applying `f` to the resulting vector. It is called `c.compAlongOrderedFinpartition f p`. -/
def compAlongOrderedFinpartition
    (f : ContinuousMultilinearMap 𝕜 (fun _i : Fin c.length ↦ F) G)
    (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F) :
    E[×n]→L[𝕜] G where
  toFun v := f (c.applyOrderedFinpartition p v)
  map_add' v i x y := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyOrderedFinpartition_update_right, ContinuousMultilinearMap.map_add]
  map_smul' v i c x := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyOrderedFinpartition_update_right, ContinuousMultilinearMap.map_smul]
  cont := by
    apply f.cont.comp
    change Continuous (fun v m ↦ p m (v ∘ c.emb m))
    fun_prop

@[simp] lemma compAlongOrderFinpartition_apply
    (f : ContinuousMultilinearMap 𝕜 (fun _i : Fin c.length ↦ F) G)
    (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F) (v : Fin n → E) :
    c.compAlongOrderedFinpartition f p v = f (c.applyOrderedFinpartition p v) := rfl

/-- Bundled version of `compAlongOrderedFinpartition`, depending linearly on `f`
and multilinearly on `p`.-/
def compAlongOrderedFinpartitionₗ :
    (ContinuousMultilinearMap 𝕜 (fun _i : Fin c.length ↦ F) G) →ₗ[𝕜]
      MultilinearMap 𝕜 (fun i : Fin c.length ↦ (E[×c.partSize i]→L[𝕜] F)) (E[×n]→L[𝕜] G) where
  toFun f :=
    { toFun := fun p ↦ c.compAlongOrderedFinpartition f p
      map_add' := by
        intro inst p m q q'
        cases Subsingleton.elim ‹_› (instDecidableEqFin _)
        ext v
        simp [applyOrderedFinpartition_update_left]
      map_smul' := by
        intro inst p m a q
        cases Subsingleton.elim ‹_› (instDecidableEqFin _)
        ext v
        simp [applyOrderedFinpartition_update_left] }
  map_add' _ _ := rfl
  map_smul' _ _ :=  rfl

variable (𝕜 E F G) in
/-- Bundled version of `compAlongOrderedFinpartition`, depending continuously linearly on `f`
and continuously multilinearly on `p`.-/
noncomputable def compAlongOrderedFinpartitionL :
    (ContinuousMultilinearMap 𝕜 (fun _i : Fin c.length ↦ F) G) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i : Fin c.length ↦ (E[×c.partSize i]→L[𝕜] F))
        (E[×n]→L[𝕜] G) := by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 (fun f p ↦ ?_)
  simp only [one_mul]
  change ‖c.compAlongOrderedFinpartition f p‖ ≤ _
  apply ContinuousMultilinearMap.opNorm_le_bound _ (by positivity) (fun v ↦ ?_)
  simp only [compAlongOrderFinpartition_apply]
  apply (f.le_opNorm _).trans
  rw [mul_assoc, ← c.prod_sigma_eq_prod, ← Finset.prod_mul_distrib]
  gcongr with m _
  · exact fun i _ ↦ by positivity
  exact (p m).le_opNorm _

@[simp] lemma compAlongOrderedFinpartitionL_apply
    (f : ContinuousMultilinearMap 𝕜 (fun _i : Fin c.length ↦ F) G)
    (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F) :
    c.compAlongOrderedFinpartitionL 𝕜 E F G f p = c.compAlongOrderedFinpartition f p := rfl

end OrderedFinpartition



namespace FormalMultilinearSeries

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.compAlongComposition p c`. -/
def compAlongOrderedFinpartition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) :
    ContinuousMultilinearMap 𝕜 (fun _i : Fin n ↦ E) G :=
  c.compAlongOrderedFinpartition (q c.length) (fun m ↦ p (c.partSize m))

@[simp]
theorem compAlongOrderedFinpartition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin n → E) :
    (q.compAlongOrderedFinpartition p c) v =
      q c.length (c.applyOrderedFinpartition (fun m ↦ (p (c.partSize m))) v) :=
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
protected noncomputable def taylorComp
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  fun n ↦ ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

end FormalMultilinearSeries

theorem faaDiBruno {n : ℕ∞} {g : F → G} {f : E → F}
    (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : MapsTo f s t) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x ↦ (q (f x)).taylorComp (p x)) s := by
  constructor
  · intro x hx
    simp [FormalMultilinearSeries.taylorComp, default, HasFTaylorSeriesUpToOn.zero_eq' hg (h hx)]
  · intro m hm x hx
    have A (c : OrderedFinpartition m) :
      HasFDerivWithinAt (fun x ↦ (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt ((fun p ↦ B p.1 p.2)
          ∘ (fun y ↦ (q (f y) c.length, fun i ↦ p y (c.partSize i))))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x


#exit

    have B : HasFDerivWithinAt (fun x ↦ (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.sum (fun c hc ↦ A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.add_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, ContinuousLinearMap.add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p ↦ rfl)

  · intro m hm
    apply continuousOn_finset_sum _ (fun c hc ↦ ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun i ↦ p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prod ?_ ?_)
    · have : (c.length : ℕ∞) ≤ m := by exact_mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i ↦ ?_)
      have : (c.partSize i : ℕ∞) ≤ m := by exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)











#exit

theorem analyticWithinOn_taylorComp
    (hq : ∀ (n : ℕ), AnalyticWithinOn 𝕜 (fun x ↦ q x n) t)
    (hp : ∀ n, AnalyticWithinOn 𝕜 (fun x ↦ p x n) s) {f : E → F}
    (hf : AnalyticWithinOn 𝕜 f s) (h : MapsTo f s t) (n : ℕ) :
    AnalyticWithinOn 𝕜 (fun x ↦ (q (f x)).taylorComp (p x) n) s := by
  apply Finset.analyticWithinOn_sum _ (fun c _ ↦ ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticWithinOn 𝕜
    ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun m ↦ p x (c.partSize m)))) s
  apply B.analyticOn_uncurry_of_multilinear.comp_analyticWithinOn ?_ (mapsTo_univ _ _)
  apply AnalyticWithinOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticWithinOn.pi (fun i ↦ hp _)
