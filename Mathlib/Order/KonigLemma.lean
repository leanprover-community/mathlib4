/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Order.Atoms.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Linarith

/-!
# Kőnig's infinity lemma

Kőnig's infinity lemma is most often stated as a graph theory result :
every infinite, locally finite connected graph contains an infinite path.
It has links to computability and proof theory, and
is often applied when the graph is a tree whose vertices encode some other types of object.

For applications of this form, it is convenient to state the lemma
in terms of covers in a strongly atomic order rather than a graph;
in this setting, the proof is almost trivial.
In this file, we prove the lemma in this order-theoretic way,
and also give a formulation that is convenient for applications in Ramsey theory.
We defer the graph-theoretic version of the statement for future work.

## Main Results

* `exists_seq_covby_of_forall_covby_finite` : Kőnig's lemma for strongly atomic orders.

* `exists_orderEmbedding_covby_of_forall_covby_finite` : Kőnig's lemma, where the sequence
    is given as an `OrderEmbedding` instead of a function.

* `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot` : Kőnig's lemma where the sequence
    starts at the minimum of an infinite type.

* `exist_seq_forall_proj_of_forall_finite` : Kőnig's lemma applied to an order on a sigma-type
  `(i : ℕ) × α i`. Useful for applications in Ramsey theory.

## TODO

Actually formulate the lemma as a statement about graphs.

-/

open Set
section Sequence

variable {α : Type*} [PartialOrder α] [IsStronglyAtomic α] {a b : α}

/-- **Kőnig's infinity lemma** : if each element in an infinite strongly atomic order
is covered by only finitely many others, and `b` is an element with infinitely many things above it,
then there is a sequence starting with `b` in which each element is covered by the next. -/
theorem exists_seq_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ → α, f 0 = b ∧ ∀ i, f i ⋖ f (i+1) := by
  let ks : ℕ → {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩
    fun _ ⟨a, ha⟩ ↦ ⟨_, (exists_covby_infinite_Ici_of_infinite_Ici ha (hfin a)).choose_spec.2⟩
  exact ⟨fun i ↦ (ks i).1, rfl,
  fun i ↦ (exists_covby_infinite_Ici_of_infinite_Ici (ks i).2 (hfin _)).choose_spec.1 ⟩

/-- The sequence given by Kőnig's lemma as an order embedding -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ ↪o α, f 0 = b ∧ ∀ i, f i ⋖ f (i+1) := by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i ↦ (hf.2 i).lt)), hf⟩

/-- A version of Kőnig's lemma where the sequence starts at the minimum of an infinite order.  -/
theorem exists_orderEmbedding_covby_of_forall_covby_finite_of_bot [OrderBot α] [Infinite α]
    (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) : ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ ∀ i, f i ⋖ f (i+1) :=
  exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

end Sequence

section Graded

/-- A formulation of Kőnig's infinity lemma, useful in applications.
Given a sequence `α 0, α 1, ...` of nonempty types with `α 0` a subsingleton,
and a well-behaved family of projections `π : α j → α i` for all `i ≤ j`,
if each term in each `α i` is the projection of only finitely many terms in `α (i+1)`,
then we can find a sequence `(f 0 : α 0), (f 1 : α 1), ...`
where `f i` is the projection of `f j` for all `i ≤ j`.

In a typical application, the `α i` are function types with increasingly large domains,
and `π hij (f : α j)` is the restriction of the domain of `f` to that of `α i`.
In this case, the sequence given by the lemma is essentially a function whose domain
is the limit of the `α i`. -/
theorem exists_seq_forall_proj_of_forall_finite {α : ℕ → Type*} [Subsingleton (α 0)]
    [∀ i, Nonempty (α i)] (π : {i j : ℕ} → (hij : i ≤ j) → α j → α i)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a, (π hij) (π hjk a) = π (hij.trans hjk) a)
    (π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a)
    (hfin : ∀ i a, {b : α (i+1) | π (Nat.le_add_right i 1) b = a}.Finite ) :
    ∃ f : (i : ℕ) → α i, ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by

  set αs := (i : ℕ) × α i

  let _ : PartialOrder (αs) := {
    le := fun a b ↦ ∃ h, π h b.2 = a.2
    le_refl := fun a ↦ ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' ↦ ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by
      rintro ⟨i,a⟩ ⟨j,b⟩ ⟨hij : i ≤ j, hab : π hij b = a⟩ ⟨hji : j ≤ i, hba : π hji a = b⟩
      obtain rfl := hij.antisymm hji
      rw [show a = b by rwa [π_refl] at hba] }

  have hcovby : ∀ {a b : αs}, a ⋖ b ↔ a ≤ b ∧ a.1 + 1 = b.1 := by
    simp only [covBy_iff_lt_and_eq_or_eq, lt_iff_le_and_ne, ne_eq, Sigma.forall, and_assoc,
      and_congr_right_iff, or_iff_not_imp_left]
    rintro i a j b ⟨h : i ≤ j, rfl : π h b = a⟩
    refine ⟨fun ⟨hne, h'⟩ ↦ ?_, ?_⟩
    · have hle' : i + 1 ≤ j := h.lt_of_ne <| by rintro rfl; simp [π_refl] at hne
      exact congr_arg Sigma.fst <| h' (i+1) (π hle' b) ⟨by simp, by rw [π_trans]⟩ ⟨hle', by simp⟩
        (fun h ↦ by apply_fun Sigma.fst at h; simp at h)
    rintro rfl
    refine ⟨fun h ↦ by apply_fun Sigma.fst at h; simp at h, ?_⟩
    rintro j c ⟨hij : i ≤ j, hcb : π _ c = π _ b⟩ ⟨hji : j ≤ i + 1, rfl : π hji b = c⟩ hne
    replace hne := show i ≠ j by rintro rfl; exact hne rfl
    obtain rfl := hji.antisymm (hij.lt_of_ne hne)
    rw [π_refl]

  have _ : IsStronglyAtomic αs := by
    simp_rw [isStronglyAtomic_iff, lt_iff_le_and_ne, hcovby]
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨⟨hij : i ≤ j, h2 : π hij b = a⟩, hne⟩
    have hle : i + 1 ≤ j := hij.lt_of_ne (by rintro rfl; simp [← h2, π_refl] at hne)
    refine ⟨⟨_, π hle b⟩, ⟨⟨by simp, by rw [π_trans, ← h2]⟩,by simp⟩, ⟨hle, by simp⟩⟩

  let _ : OrderBot αs := OrderBot.mk (toBot := ⟨0, Classical.arbitrary _⟩)
    fun _ ↦ ⟨Nat.zero_le _, Subsingleton.elim _ _⟩

  have hfin : ∀ (a : αs), {x | a ⋖ x}.Finite := by
    refine fun ⟨i,a⟩ ↦ ((hfin i a).image (fun b ↦ ⟨_,b⟩)).subset ?_
    simp only [hcovby, subset_def, mem_setOf_eq, mem_image, and_imp, Sigma.forall]
    exact fun j b ⟨_, _⟩ hj ↦ ⟨π hj.le b, by rwa [π_trans], by cases hj; rw [π_refl]⟩

  obtain ⟨f, hf0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  have hr : ∀ i, (f i).1 = i :=
    Nat.rec (by rw [hf0]; rfl) (fun i ih ↦ by rw [← (hcovby.1 (hf i)).2, ih])

  refine ⟨fun i ↦ by rw [← hr i]; exact (f i).2, fun i j hij ↦ ?_⟩
  convert (f.monotone hij).2 <;>
  simp [hr]

end Graded

section Graph

namespace SimpleGraph

variable {V : Type*} {x y z a b : V} {G : SimpleGraph V} {W : G.Walk x y}

-- def IsShortestPath (P : G.Path x y) := ∀ (Q : G.Path x y), P.1.length ≤ Q.1.length

-- lemma Reachable.exists_shortestPath (h : G.Reachable x y) :
--     ∃ (P : G.Path x y), IsShortestPath P := by
--   classical
--   have hs : {n : ℕ | ∃ (P : G.Path x y), P.1.length = n}.Nonempty := ⟨_, h.some.toPath , rfl⟩
--   obtain ⟨P, hP⟩ := Nat.sInf_mem hs
--   exact ⟨P, fun Q ↦ hP ▸ Nat.sInf_le ⟨Q, rfl⟩⟩
def Walk.IsShortest (W : G.Walk x y) := W.length = G.dist x y

lemma Walk.IsShortest.length_eq (hW : W.IsShortest) : W.length = G.dist x y := hW

lemma Walk.isShortest_of_le (hW : W.length ≤ G.dist x y) : W.IsShortest :=
    hW.antisymm <| dist_le _

lemma Walk.IsShortest.reverse (hW : W.IsShortest) : W.reverse.IsShortest := by
  rw [IsShortest, length_reverse, hW.length_eq, dist_comm]

lemma Reachable.dist_triangle (hxy : G.Reachable x y) (hyz : G.Reachable y z) :
    G.dist x z ≤ G.dist x y + G.dist y z := by
  obtain ⟨P, hP⟩ := hxy.exists_walk_of_dist
  obtain ⟨Q, hQ⟩ := hyz.exists_walk_of_dist
  convert G.dist_le (P.append Q)
  rw [Walk.length_append, hP, hQ]

lemma Walk.IsShortest.takeUntil [DecidableEq V] (hW : W.IsShortest)
    {a : V} (ha : a ∈ W.support) : (W.takeUntil a ha).IsShortest := by
  refine isShortest_of_le ?_
  have h := congr_arg Walk.length <| W.take_spec ha
  rw [length_append, hW.length_eq] at h
  linarith [dist_le (W.dropUntil a ha),
    Reachable.dist_triangle ⟨W.takeUntil _ ha⟩ ⟨W.dropUntil _ ha⟩ ]

lemma Walk.IsShortest.dropUntil [DecidableEq V] (hW : W.IsShortest)
    {a : V} (ha : a ∈ W.support) : (W.dropUntil a ha).IsShortest := by
  sorry

lemma Walk.IsShortest.dist_add_of_mem (hW : W.IsShortest)
    (ha : a ∈ W.support) : G.dist x a + G.dist a y = G.dist x y := by
  classical
  rw [← (hW.takeUntil ha), ← (hW.dropUntil ha), ← hW, ← length_append, take_spec]

lemma Walk.reachable_of_mem_of_mem (haW : a ∈ W.support) (hbW : b ∈ W.support) :
    G.Reachable a b := by
  classical
  exact Reachable.trans ⟨(W.takeUntil _ haW).reverse⟩ ⟨W.takeUntil _ hbW⟩

lemma Walk.length_takeUntil_lt [DecidableEq V] (W : G.Walk x y) (ha : a ∈ W.support)
    (hay : a ≠ y) : (W.takeUntil a ha).length < W.length := by
  nth_rw 2 [← W.take_spec ha]
  rw [length_append, lt_add_iff_pos_right, zero_lt_iff, Ne, ← Walk.nil_iff_length_eq]
  exact not_nil_of_ne hay

lemma Walk.length_dropUntil_lt [DecidableEq V] (W : G.Walk x y) (ha : a ∈ W.support)
    (hax : a ≠ x) : (W.dropUntil a ha).length < W.length := by
  nth_rw 2 [← W.take_spec ha]
  rw [length_append, lt_add_iff_pos_left, zero_lt_iff, Ne, ← Walk.nil_iff_length_eq]
  exact not_nil_of_ne hax.symm

example (G : SimpleGraph V) (hG : G.LocallyFinite) (hconn : G.Connected) (a : V) :
    ∃ (f : ℕ ↪ V), f 0 = a ∧ ∀ i, G.Adj (f i) (f (i+1)) := by
  classical
  let _ : PartialOrder V := {
    le := fun x y ↦ ∃ W : G.Walk y a, W.IsShortest ∧ x ∈ W.support
    le_refl := fun x ↦ ⟨_, (hconn.exists_walk_of_dist x a).choose_spec, by simp⟩
    le_trans := by
      rintro x y z ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
      refine ⟨(Q.takeUntil _ hyQ).append P, ?_, by simp [hxP]⟩
      rw [Walk.IsShortest, Walk.length_append, hP, ← hQ.dropUntil hyQ,
        ← Walk.length_append, Q.take_spec, hQ]
    le_antisymm := by
      rintro x y ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
      have hxy : G.dist x y = 0 := by
        linarith [hQ.dist_add_of_mem hyQ, G.dist_comm ▸ hP.dist_add_of_mem hxP]
      rwa [(show G.Reachable x y from ⟨Q.append P.reverse⟩).dist_eq_zero_iff] at hxy }

  have hsm : StrictMono (G.dist · a) := by
    simp only [StrictMono, lt_iff_le_and_ne (α := V), ne_eq, and_imp]
    refine fun x y ⟨P, hP, hxP⟩ hne ↦ ?_
    rw [← hP, (hP.dropUntil hxP).symm]
    exact P.length_dropUntil_lt hxP hne

  have _ := WellFoundedLT.of_strictMono hsm

  have hcb : ∀ x y, x ⋖ y → G.Adj x y := by
    intro x y hxy


  -- have := exists_orderEmbedding_covby_of_forall_covby_finite


  -- have : IsStronglyAtomic V := by
  --   simp_rw [isStronglyAtomic_iff, covBy_iff_lt_and_eq_or_eq, lt_iff_le_and_ne]
  --   rintro x y ⟨⟨P, hP, hxP⟩, hne⟩
  --   let z := (P.takeUntil _ hxP).reverse.sndOfNotNil (Walk.not_nil_of_ne hne)


    -- have hnil : ¬ P.Nil := P.not_nil_of_ne hne


  -- rw [IsShortest, ← congr_arg Walk.length <| W.take_spec ha]

-- def distToLE (G : SimpleGraph V) (hG : G.Connected) (a : V) : PartialOrder V where
--   le x y := ∃ W : G.Walk a y, W.IsShortest ∧ x ∈ W.support
--   le_refl x := ⟨_, (hG.exists_walk_of_dist a x).choose_spec, by simp⟩
--   le_trans := by
--     classical
--     rintro x y z ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
--     refine ⟨P.append (Q.dropUntil _ hyQ), Walk.isShortest_of_le ?_, by simp [hxP]⟩
--     rw [Walk.length_append, ← hQ, ← congr_arg Walk.length <| Q.take_spec hyQ,
--       Walk.length_append, Nat.add_le_add_iff_right]
--     exact hP.le.trans <| dist_le _
--   le_antisymm := by
--     classical
--     rintro x y ⟨P, hP, hxP⟩ ⟨Q, hQ, hxQ⟩
--     suffices h' : (Q.dropUntil y hxQ).length = 0 from (Walk.eq_of_length_eq_zero h').symm
--     have hcon := congr_arg Walk.length <| Q.take_spec hxQ
--     rw [Walk.length_append] at hcon
--     linarith [dist_le <| Q.takeUntil _ hxQ, P.length_takeUntil_le hxP, dist_le <| P.takeUntil _ hxP,
--       hP.le, hQ.le]

-- lemma Walk.IsShortest.distToLE {a : V} {W : G.Walk a y} (hW : IsShortest W) (hG : G.Connected)
--     (hx : x ∈ W.support) :
--     let _ := distToLE G hG a
--     x ≤ y :=
--   ⟨W, hW, hx⟩



-- theorem distToLE_covby_iff (G : SimpleGraph V) (hG : G.Connected) (a : V) :
--     let _ := distToLE G hG a
--     x ⋖ y ↔ ∃ (W : G.Walk a x), W.IsShortest ∧ ∃ (hxy : G.Adj x y), (W.concat hxy).IsShortest := by
--   classical
--   simp only [@covBy_iff_lt_and_eq_or_eq _ (distToLE G hG a), lt_iff_le_and_ne]
--   constructor
--   · rintro ⟨⟨⟨P, hP, hxP⟩, hne⟩, h'⟩
--     refine ⟨P.takeUntil _ hxP, hP.takeUntil hG hxP, ?_⟩
--     set z := (P.dropUntil _ hxP).sndOfNotNil sorry with hz_def
--     have hz : z ∈ P.support := by
--       simp [hz_def]
--       have : z ∈ (P.dropUntil x hxP).support := by exact?

--     have := h' z




end Graph
