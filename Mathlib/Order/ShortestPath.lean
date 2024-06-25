import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Grade
import Mathlib.Tactic.Linarith

section Graph

namespace SimpleGraph

open Walk

variable {V : Type*} {x y z a b : V} {G : SimpleGraph V} {W : G.Walk x y}

-- def IsShortestPath (P : G.Path x y) := ∀ (Q : G.Path x y), P.1.length ≤ Q.1.length

-- lemma Reachable.exists_shortestPath (h : G.Reachable x y) :
--     ∃ (P : G.Path x y), IsShortestPath P := by
--   classical
--   have hs : {n : ℕ | ∃ (P : G.Path x y), P.1.length = n}.Nonempty := ⟨_, h.some.toPath , rfl⟩
--   obtain ⟨P, hP⟩ := Nat.sInf_mem hs
--   exact ⟨P, fun Q ↦ hP ▸ Nat.sInf_le ⟨Q, rfl⟩⟩


lemma foo (W W' : G.Walk x y) (h : W.support = W'.support) : W = W' := by
  by_cases hW : W.support = [x]
  · rw [hW] at h

  -- by_cases hW : W.Nil
  -- · sorry
  -- by_cases hW' : W'.Nil
  -- · sorry
  -- rw [← W.cons_tail_eq hW, ← W'.cons_tail_eq hW']
  -- convert rfl using 2

  -- obtain (rfl | ⟨hadj : (G.Adj x _),W⟩) := W
  -- · rw [eq_comm, ← Walk.nil_iff_eq_nil, Walk.nil_iff_support_eq, ← h, support_nil]

  -- induction' W with _ x y z hxy W₁ IH W₂
  -- · rw [eq_comm, ← Walk.nil_iff_eq_nil, Walk.nil_iff_support_eq, ← h, support_nil]

  -- induction' W' with _ x' y' z' hxy' W₁' IH W₂'
  -- · simp at h
  -- simp at h
  -- have := IH W₁'



lemma Walk.sndOfNotNil_mem_support (hW : ¬ W.Nil) : W.sndOfNotNil hW ∈ W.support := by
  induction' W with W hW
  · simp at hW
  simp

lemma Walk.tail_eq_dropUntil [DecidableEq V] (hW : ¬ W.Nil) :
    W.tail hW = W.dropUntil _ (W.sndOfNotNil_mem_support hW) := by
  induction' W with W h a b hab W' IH
  · simp at hW


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

lemma Reachable.exists_isShortest (hxy : G.Reachable x y) : ∃ W : G.Walk x y, W.IsShortest :=
  hxy.exists_walk_of_dist

lemma Connected.exists_isShortest (hG : G.Connected) (x y : V) : ∃ W : G.Walk x y, W.IsShortest :=
  hG.exists_walk_of_dist x y

lemma Walk.IsShortest.takeUntil [DecidableEq V] (hW : W.IsShortest)
    {a : V} (ha : a ∈ W.support) : (W.takeUntil a ha).IsShortest := by
  refine isShortest_of_le ?_
  have h := congr_arg Walk.length <| W.take_spec ha
  rw [length_append, hW.length_eq] at h
  linarith [dist_le (W.dropUntil a ha),
    Reachable.dist_triangle ⟨W.takeUntil _ ha⟩ ⟨W.dropUntil _ ha⟩ ]

lemma Walk.IsShortest.dropUntil [DecidableEq V] (hW : W.IsShortest)
    {a : V} (ha : a ∈ W.support) : (W.dropUntil a ha).IsShortest := by
  refine isShortest_of_le ?_
  have h := congr_arg Walk.length <| W.take_spec ha
  rw [length_append, hW] at h
  linarith [dist_le (W.takeUntil a ha),
    Reachable.dist_triangle ⟨W.takeUntil _ ha⟩ ⟨W.dropUntil _ ha⟩]



lemma Walk.IsShortest.tail (hW : W.IsShortest) (hWnil : ¬ W.Nil) : (W.tail hWnil).IsShortest := by
  rw [IsShortest, ← Nat.add_left_inj (n := 1), length_tail_add_one]

  have := congr_arg Walk.length <| W.cons_tail_eq hWnil




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

def BfsFrom (_ : SimpleGraph V) (_ : V) := V

def BfsFrom.ofVert (v : V) : G.BfsFrom a := v

instance {G : SimpleGraph V} {v : V} : CoeOut (G.BfsFrom v) V where coe x := x

instance : PartialOrder (G.BfsFrom a) where
  le x y := x = y ∨ ∃ W : G.Walk y a, W.IsShortest ∧ (x : V) ∈ W.support
  le_refl _ :=  .inl rfl
  le_trans := by
    classical
    rintro x y z (rfl | ⟨P, hP, hxP⟩) (rfl | ⟨Q, hQ, hyQ⟩)
    · exact .inl rfl
    · exact .inr ⟨Q, hQ, hyQ⟩
    · exact .inr ⟨P, hP, hxP⟩
    refine .inr ⟨(Q.takeUntil y hyQ).append P, ?_, by simp [hxP]⟩
    rw [IsShortest, length_append, hP, ← hQ.dropUntil hyQ, ← length_append, Q.take_spec, hQ]
  le_antisymm := by
    classical
    rintro x y (rfl | ⟨P, hP, hxP⟩) (h' | ⟨Q, hQ, hyQ⟩)
    · rfl
    · rfl
    · simpa using h'.symm
    have hxy : G.dist x y = 0 := by
      linarith [hQ.dist_add_of_mem hyQ, G.dist_comm ▸ hP.dist_add_of_mem hxP]
    rwa [(show G.Reachable x y from ⟨Q.append P.reverse⟩).dist_eq_zero_iff] at hxy

variable [Fact G.Connected] {x y z : G.BfsFrom a}

lemma exists_isShortest_walk (G : SimpleGraph V) [Fact G.Connected] (x y : V) :
    ∃ W : G.Walk x y, W.IsShortest :=
  Connected.exists_isShortest Fact.out x y

lemma BfsFrom.exists_isShortest_walk_of_le {x y : G.BfsFrom a} (hxy : x ≤ y) :
    ∃ W : G.Walk y a, W.IsShortest ∧ x ∈ W.support := by
  obtain (rfl | ⟨W, hW⟩) := hxy
  · exact ⟨_, ((show G.Connected from Fact.out).exists_isShortest x a).choose_spec, by simp⟩
  exact ⟨_, hW⟩

lemma BfsFrom.exists_isShortest_walk_iff_le {x y : G.BfsFrom a} :
    x ≤ y ↔ ∃ W : G.Walk y a, W.IsShortest ∧ x ∈ W.support :=
  ⟨exists_isShortest_walk_of_le, Or.inr⟩

lemma BfsFrom.le_iff_dist_add {x y : G.BfsFrom a} :
    x ≤ y ↔ G.dist y a = G.dist y x + G.dist x a := by
  classical
  rw [exists_isShortest_walk_iff_le]
  refine ⟨fun ⟨W, hW, hxW⟩ ↦ (hW.dist_add_of_mem hxW).symm, fun h ↦ ?_⟩
  obtain ⟨P, hP⟩ := G.exists_isShortest_walk y x
  obtain ⟨Q, hQ⟩ := G.exists_isShortest_walk x a
  exact ⟨P.append Q, by rwa [IsShortest, eq_comm, length_append, hP, hQ], by simp⟩

lemma Walk.IsShortest.le_of_mem_support {W : G.Walk y a} (hW : W.IsShortest) (hx : x ∈ W.support) :
    x ≤ y :=
  .inr ⟨W, hW, hx⟩





-- lemma Connected.exists_shortest_walk_of_le

instance [Fact G.Connected] : GradeOrder ℕ (G.BfsFrom a) where
  grade x := G.dist x a
  grade_strictMono := by
    simp only [StrictMono, and_imp, lt_iff_le_and_ne, BfsFrom.le_iff_dist_add]
    intro x y h_eq hne
    simp [h_eq, hne.symm, (show G.Connected from Fact.out) y x]
  covBy_grade := by
    classical
    simp_rw [Nat.covBy_iff_succ_eq]
    rintro x y hcb
    obtain ⟨P, hP, hxP⟩ := BfsFrom.exists_isShortest_walk_of_le hcb.le
    let Q := P.takeUntil x hxP

    have hQ := hP.takeUntil hxP
    let w := Q.sndOfNotNil <| Q.not_nil_of_ne hcb.ne.symm
    have hwQ : w ∈ Q.support := Q.sndOfNotNil_mem _
    have hwP : w ∈ P.support := P.support_takeUntil_subset hxP hwQ

    have hwy := hP.le_of_mem_support hwP
    have := (hP.dropUntil hwP).le_of_mem_support (x := x)
    simp at this

    -- have hnil := Q.not_nil_of_ne hcb.ne.symm
    -- have := hcb.eq_or_eq (c := BfsFrom.ofVert <| Q.sndOfNotNil <| Q.not_nil_of_ne hcb.ne.symm)
    --   ()




-- example (G : SimpleGraph V) (hG : G.LocallyFinite) (hconn : G.Connected) (a : V) :
--     ∃ (f : ℕ ↪ V), f 0 = a ∧ ∀ i, G.Adj (f i) (f (i+1)) := by
--   classical
--   let _ : PartialOrder V := {
--     le := fun x y ↦ ∃ W : G.Walk y a, W.IsShortest ∧ x ∈ W.support
--     le_refl := fun x ↦ ⟨_, (hconn.exists_walk_of_dist x a).choose_spec, by simp⟩
--     le_trans := by
--       rintro x y z ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
--       refine ⟨(Q.takeUntil _ hyQ).append P, ?_, by simp [hxP]⟩
--       rw [Walk.IsShortest, Walk.length_append, hP, ← hQ.dropUntil hyQ,
--         ← Walk.length_append, Q.take_spec, hQ]
--     le_antisymm := by
--       rintro x y ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
--       have hxy : G.dist x y = 0 := by
--         linarith [hQ.dist_add_of_mem hyQ, G.dist_comm ▸ hP.dist_add_of_mem hxP]
--       rwa [(show G.Reachable x y from ⟨Q.append P.reverse⟩).dist_eq_zero_iff] at hxy }

--   have hsm : StrictMono (G.dist · a) := by
--     simp only [StrictMono, lt_iff_le_and_ne (α := V), ne_eq, and_imp]
--     refine fun x y ⟨P, hP, hxP⟩ hne ↦ ?_
--     rw [← hP, (hP.dropUntil hxP).symm]
--     exact P.length_dropUntil_lt hxP hne

--   have _ := WellFoundedLT.of_strictMono hsm

--   have hcb : ∀ x y, x ⋖ y → G.Adj x y := by
--     intro x y hxy


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
