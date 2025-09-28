import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib


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
    . sorry
