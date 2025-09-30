import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.FreeGroup.Basic
import Batteries.Data.List.Lemmas



variable {α X : Type*} [Fintype α] [DecidableEq α]

variable [MulAction (FreeGroup α) X]

--- All Elements of the free Group that start with a certain letter
def FreeGroup.startWith (w : α × Bool) := {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

def Orbit (x : X) (w : α × Bool) := {g • x | g ∈ FreeGroup.startWith w}

theorem Orbit.not_one {w : α × Bool} (g : FreeGroup α)  (h : g ∈ FreeGroup.startWith w) : g ≠ 1 := by
  sorry


theorem Orbit_rot (x : X) (w : α × Bool) : {(FreeGroup.mk [w])⁻¹ • y | y ∈ Orbit x w} =
      ⋃ v ∈ {z : α × Bool | z ≠ (w.1, !w.2)}, Orbit x v := by
  ext i
  simp only [FreeGroup.inv_mk, Set.mem_setOf_eq, ne_eq, Set.mem_iUnion, exists_prop, Prod.exists,
    Prod.mk.injEq, not_and, Bool.not_eq_not, Bool.exists_bool, Bool.false_eq, Bool.true_eq]
  constructor
  . intro h
    rcases h with ⟨y, ⟨hy1, hy2⟩⟩
    simp [Orbit, FreeGroup.startWith] at hy1
    rcases hy1 with ⟨g, ⟨hg1, hg2⟩⟩
    rw [← hg2] at hy2
    simp only [Orbit, FreeGroup.startWith, Set.mem_setOf_eq, ← hy2]
    by_cases hC: g.toWord.length > 1
    .
      use (g.toWord[1]'hC).1
      cases hg3 : (g.toWord[1]'hC).2
      . left
        constructor
        . intro h
          have h4  : FreeGroup.IsReduced g.toWord := FreeGroup.isReduced_toWord
          have h5 := List.IsChain.getElem h4 0 (by grind) (by grind) -- des isches
          grind
        .
          use FreeGroup.mk g.toWord.tail
          have h4 : FreeGroup.reduce g.toWord.tail = g.toWord.tail := by
              have h6 : FreeGroup.IsReduced g.toWord.tail :=
                FreeGroup.IsReduced.infix g.isReduced_toWord (by sorry)
              rw [FreeGroup.IsReduced.reduce_eq h6]
          constructor
          . simp

            grind
          .
            rw [← mul_smul, show g = FreeGroup.mk (g.toWord) by exact Eq.symm FreeGroup.mk_toWord]
            congr 1
            simp
            refine FreeGroup.reduce.exact ?_
            have h5 : FreeGroup.invRev [w] ++ g.toWord = (w.1, !w.2) :: g.toWord := by
              simp [FreeGroup.invRev]
            rw [h5]
            simp only [FreeGroup.reduce.cons, Bool.not_eq_eq_eq_not, Bool.not_not,
              FreeGroup.reduce_toWord]
            rw [show g.toWord = g.toWord.head (by grind) :: g.toWord.tail by grind]
            simp
            have h6 : g.toWord.head (by grind) = (w.1, w.2) := by
              rw [List.getElem?_eq_getElem] at hg1
              .
                sorry -- gschenkt
              . grind

            simp [h6, h4]
      . sorry
    .
      sorry --gschenkter gaul
  . simp only [forall_exists_index]

    intro a h
    rcases h with ⟨h1, h2⟩
    . simp only [Orbit, FreeGroup.startWith, Set.mem_setOf_eq, exists_exists_and_eq_and] at *
      rcases h2 with ⟨g, ⟨h2, h3⟩⟩
      subst h3
      use FreeGroup.mk [w] * g
      constructor
      . rw [List.getElem?_eq_getElem]
        . congr
          induction hg : g.toWord with
          | nil => simp [FreeGroup.toWord_mul, hg]
          | cons head tail ih =>
            simp [FreeGroup.toWord_mul]
            simp_rw [hg]
            have h_head : head = (a, false) := by
              rw [hg] at h2
              simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero,
                Option.some.injEq] at h2
              exact h2
            by_cases hC : a = w.1
            . simp_rw [h1 hC, show (head.2 = false) by simp [h_head]]
              simp
            . have h : (w.1 = head.1) = false := by
                simp [show (head.1 = a) by simp [h_head]]
                exact fun a_1 ↦ hC (id (Eq.symm a_1))
              simp [h]

        .
          have h : FreeGroup.IsReduced (w :: g.toWord.head (by grind) :: g.toWord.tail) := by
            rw [FreeGroup.isReduced_cons_cons]
            constructor
            . intro h


      . rw [← mul_smul]
        rw [← mul_assoc]
        simp only [FreeGroup.mul_mk]
        have h5 : FreeGroup.mk (FreeGroup.invRev [w] ++ [w]) = 1 := by
          rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, Group.inv_mul_cancel]
        simp [h5]
    . sorry -- das gleiche





#exit









/-


inductive Rot where
  | a : Rot
  | b : Rot

abbrev F_2 := FreeGroup Rot

variable {X : Type*} [MulAction F_2 X]


variable (x : X)

open scoped Classical
def S_A := {w : F_2 | (FreeGroup.toWord w)[0]? = (Rot.a, true)}
def S_A_points := {w • x | w ∈ S_A}

theorem S_A_eq (w : F_2) (h : w ∈ S_A) : ∃ v, w = FreeGroup.mk ((Rot.a, true) :: FreeGroup.toWord v) := by
  simp [S_A] at h
  sorry


def S_B := {w : F_2 | (FreeGroup.toWord w)[0]? = (Rot.b, true)}
def S_B_points := {w • x | w ∈ S_B}

def S_A' := {w : F_2 | (FreeGroup.toWord w)[0]? = (Rot.a, false)}
def S_A'_points := {w • x | w ∈ S_A'}

def S_B' := {w : F_2 | (FreeGroup.toWord w)[0]? = (Rot.b, false)}
def S_B'_points := {w • x | w ∈ S_B'}

theorem FreeGroup.mk_inv : FreeGroup.mk [(Rot.a, false), (Rot.a, true)] = 1 := by
  refine FreeGroup.reduce.exact ?_
  simp [@FreeGroup.reduce_nil]




theorem test : {FreeGroup.mk [(Rot.a, false)] • y | y ∈ S_A_points x} =
    S_A_points x ∪ S_B_points x ∪ S_B'_points x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp [S_A_points, S_B_points, S_B'_points] at *
    rcases hy with ⟨w, hw, h1⟩
    subst h1
    cases h : FreeGroup.toWord w with
    | nil =>
      simp [S_A] at hw
      grind only [→ List.getElem_of_getElem?, = List.getElem?_nil, usr getElem_of_getElem?]
    | cons hd1 tl =>
      have hhd1 : hd1 = (Rot.a, true) := by
        simp [S_A] at hw
        rw [h] at hw
        grind only [→ List.getElem_of_getElem?, usr getElem_of_getElem?, = List.getElem?_cons,
          cases eager Prod]
      have hw1 : w = FreeGroup.mk (hd1 :: tl) := by
        refine FreeGroup.toWord_inj.mp ?_
        rw [← h]
        simp

      cases h1 : tl with
      | nil => sorry
      | cons hd2 tl2 =>
        have h_red : FreeGroup.reduce tl = tl := by
          sorry
        cases hd' : hd2 with
        | mk rot bool =>
          cases rot
          . cases bool
            . sorry --contradiction
            . left
              left
              use FreeGroup.mk tl
              simp [S_A]
              rw [h_red, h1]
              simp [hd']
              rw [← mul_smul]
              congr
              rw [hw1,FreeGroup.mul_mk]
              sorry



          . cases bool
            . right
              sorry
            . right
              right
              sorry


  . simp
    intro h
    rcases h with ((h | h) | h)
    .
      use FreeGroup.mk [(Rot.a, true)] • z
      constructor
      . simp [S_A_points] at *
        rcases h with ⟨w, ⟨h1, h2⟩⟩
        use FreeGroup.mk [(Rot.a, true)] * w
        constructor
        . simp [S_A]
          rw [FreeGroup.toWord_mul]
          have h4 : (FreeGroup.reduce ((FreeGroup.mk [(Rot.a, true)]).toWord ++ FreeGroup.toWord w)) =
                [(Rot.a, true)] ++ (FreeGroup.toWord w) := by
              let L := FreeGroup.toWord w
              repeat rw [show FreeGroup.toWord w = L by rfl]
              have hL : FreeGroup.reduce L = L := by
                subst L
                exact FreeGroup.reduce_toWord w
              cases hL' : L  with
              | nil => simp [FreeGroup.reduce_nil]
              | cons hd tl =>

                simp only [FreeGroup.toWord_mk, Bool.true_eq,
                  Bool.not_eq_eq_eq_not, Bool.not_true, FreeGroup.reduce_nil, List.cons_append,
                  List.nil_append,FreeGroup.reduce_singleton]
                rw [FreeGroup.reduce.cons]
                simp only [Bool.true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
                --- hd::tl ist reduziert, da L := FreeGroup.toWord w
                rw [← hL', hL, hL']
                simp
                intro h3 h4

                have h5 : hd = (Rot.a, true) := by

                  simp [S_A] at h1
                  rw [show FreeGroup.toWord w = L by rfl] at h1
                  grind only [→ List.getElem_of_getElem?, usr getElem_of_getElem?, =
                    List.getElem?_cons, cases eager Prod]
                grind only [cases eager Prod]
          simp_rw [h4]
          simp
        . rw [← h2]
          rw [@mul_smul]
      . rw [← mul_smul]
        simp [FreeGroup.mk_inv]
    . sorry
    . sorry -/
