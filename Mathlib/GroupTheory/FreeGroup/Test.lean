import Mathlib.GroupTheory.FreeGroup.Reduce


inductive Rot where
  | a : Rot
  | b : Rot

abbrev F_2 := FreeGroup Rot

variable {X : Type*} [MulAction F_2 X]


variable (x : X)

open scoped Classical
 def S_A := {w : F_2 | (FreeGroup.toWord w).getLast? = (Rot.a, true)}
def S_A_points := {w • x | w ∈ S_A}

def S_B := {w : F_2 | (FreeGroup.toWord w).getLast? = (Rot.b, true)}
def S_B_points := {w • x | w ∈ S_B}

def S_A' := {w : F_2 | (FreeGroup.toWord w).getLast? = (Rot.a, false)}
def S_A'_points := {w • x | w ∈ S_A'}

def S_B' := {w : F_2 | (FreeGroup.toWord w).getLast? = (Rot.b, false)}
def S_B'_points := {w • x | w ∈ S_B'}


theorem test : {FreeGroup.mk [(Rot.a, false)] • y | y ∈ S_A_points x} =
    S_A_points x ∪ S_B_points x ∪ S_B'_points x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp
    sorry
  . simp
    intro h
    rcases h with ((h | h) | h)
    .
