import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith

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

@[ext] structure bfsFrom (G : SimpleGraph V) (v : V) where ofVertex :: x : V

instance {G : SimpleGraph V} {v : V} : CoeOut (G.bfsFrom v) V where coe := fun ⟨x⟩ ↦ x

instance {G : SimpleGraph V} {v : V} : PartialOrder (G.bfsFrom a) where
  le x y := x.1 = y.1 ∨ ∃ W : G.Walk x a, W.IsShortest ∧ (y : V) ∈ W.support
  le_refl _ :=  .inl rfl
  le_trans := by
    classical
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ (rfl | ⟨P, hP, hxP⟩) (rfl | ⟨Q, hQ, hzQ : z ∈ Q.support⟩)
    · exact .inl rfl
    · exact .inr ⟨Q, hQ, hzQ⟩
    · exact .inr ⟨P, hP, hxP⟩
    simp only at P Q
    refine .inr ⟨(Q.takeUntil _ hyQ).append P, ?_, by simp [hxP]⟩
    -- obtain (rfl | ⟨Q, hQ, hyQ⟩) := h
    -- · exact .inr ⟨P, hP, hxP⟩
    -- ·

    -- simp only at P hxP Q hyQ


  le_antisymm := _


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
