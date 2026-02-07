/-
Copyright (c) 2026 Zackary Skelly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zackary Skelly
-/
module

public import Mathlib.Data.List.Basic

/-!
# Constructive list split classifiers

This file provides constructive classifiers for equations of the form
`Δa ++ X :: Δb = Δ1 ++ S :: Δ2` and
`Δx ++ B :: A :: Δy = Δ1 ++ S :: Δ2`.

These are useful when a development needs explicit case data (not only propositional
disjunctions) for `before / at / after` split analysis.
-/

public section

namespace List

variable {α : Type*}

theorem append_cons_eq_singleton (xs : List α) (x : α) (ys : List α) (z : α) :
    xs ++ x :: ys = [z] → xs = [] ∧ ys = [] ∧ x = z := by
  intro h
  cases xs with
  | nil =>
      cases ys with
      | nil =>
          refine ⟨rfl, rfl, ?_⟩
          have h' : x :: ([] : List α) = z :: ([] : List α) := by
            simpa using h
          cases h'
          rfl
      | cons y ys =>
          have : False := by
            have t := congrArg List.length h
            simp at t
          cases this
  | cons a xs =>
      have : False := by
        have t : xs.length + (ys.length + 2) = 1 := by
          simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg List.length h
        have hge2' : 2 ≤ ys.length + 2 := Nat.le_add_left 2 ys.length
        have hle : ys.length + 2 ≤ xs.length + (ys.length + 2) := by
          exact Nat.le_add_left (ys.length + 2) xs.length
        have hge2 : 2 ≤ xs.length + (ys.length + 2) := Nat.le_trans hge2' hle
        have h21 : 2 ≤ 1 := by
          rw [← t]
          exact hge2
        exact (show False from (by decide : ¬ (2 ≤ 1)) h21)
      cases this

/-- Constructive classifier for equations `Δa ++ X :: Δb = Δ1 ++ S :: Δ2`. -/
inductive ConsSplit (Δa Δb Δ1 Δ2 : List α) (X S : α) : Type _
  | left (Δ1b : List α)
      (hΔ1 : Δ1 = Δa ++ X :: Δ1b)
      (hΔb : Δb = Δ1b ++ S :: Δ2)
  | right (Δ2a Δ2b : List α)
      (hΔa : Δa = Δ1 ++ S :: Δ2a)
      (hΔ2 : Δ2 = Δ2a ++ X :: Δ2b)
      (hΔb : Δb = Δ2b)
  | atSlot (hΔa : Δa = Δ1) (hXS : X = S) (hΔb : Δb = Δ2)

/-- Constructive classifier for equations `Δx ++ B :: A :: Δy = Δ1 ++ S :: Δ2`. -/
inductive SwapSplit (Δx Δy Δ1 Δ2 : List α) (A B S : α) : Type _
  | left (Δ1b : List α)
      (hΔ1 : Δ1 = Δx ++ B :: A :: Δ1b)
      (hΔy : Δy = Δ1b ++ S :: Δ2)
  | right (Δ2a Δ2b : List α)
      (hΔx : Δx = Δ1 ++ S :: Δ2a)
      (hΔ2 : Δ2 = Δ2a ++ B :: A :: Δ2b)
      (hΔy : Δy = Δ2b)
  | atA (Δ1a : List α)
      (hΔx : Δx = Δ1a)
      (hAS : A = S)
      (hΔ1 : Δ1 = Δ1a ++ [B])
      (hΔ2 : Δ2 = Δy)
  | atB (hΔx : Δx = Δ1) (hBS : B = S) (hΔ2 : Δ2 = A :: Δy)

/-- Constructively classify equalities `Δa ++ X :: Δb = Δ1 ++ S :: Δ2`. -/
def classify_cons_vs_split
    (Δa Δb Δ1 Δ2 : List α) (X S : α)
    (h : Δa ++ X :: Δb = Δ1 ++ S :: Δ2) :
    ConsSplit Δa Δb Δ1 Δ2 X S :=
  match Δa with
  | [] =>
      match Δ1 with
      | [] => by
          cases h
          exact ConsSplit.atSlot rfl rfl rfl
      | a :: Δ1' => by
          cases h
          exact ConsSplit.left Δ1' rfl rfl
  | a :: Δa' =>
      match Δ1 with
      | [] => by
          have hcons : a :: (Δa' ++ X :: Δb) = S :: Δ2 := by
            simpa [List.append_assoc] using h
          cases hcons
          refine ConsSplit.right Δa' Δb ?_ rfl rfl
          simp
      | b :: Δ1' => by
          have hcons : a :: (Δa' ++ X :: Δb) = b :: (Δ1' ++ S :: Δ2) := by
            simpa [List.append_assoc] using h
          have hab : a = b := by
            have hob : some a = some b := by
              simpa using congrArg List.head? hcons
            exact Option.some.inj hob
          have htail : Δa' ++ X :: Δb = Δ1' ++ S :: Δ2 := by
            simpa using congrArg List.tail hcons
          cases hab
          have r := classify_cons_vs_split (Δa := Δa') (Δb := Δb) (Δ1 := Δ1') (Δ2 := Δ2)
              (X := X) (S := S) htail
          cases r with
          | left Δ1b hΔ1 hΔb =>
              refine ConsSplit.left Δ1b ?_ hΔb
              have : a :: Δ1' = a :: (Δa' ++ X :: Δ1b) := by
                simpa using congrArg (fun t => a :: t) hΔ1
              simpa [List.append_assoc] using this
          | right Δ2a Δ2b hΔa hΔ2 hΔb =>
              refine ConsSplit.right Δ2a Δ2b ?_ hΔ2 hΔb
              have : a :: Δa' = a :: (Δ1' ++ S :: Δ2a) := by
                simpa using congrArg (fun t => a :: t) hΔa
              simpa [List.append_assoc] using this
          | atSlot hΔa hXS hΔb =>
              refine ConsSplit.atSlot ?_ hXS hΔb
              simpa using congrArg (fun t => a :: t) hΔa

/-- Constructively classify equalities `Δx ++ B :: A :: Δy = Δ1 ++ S :: Δ2`. -/
def classify_swap_vs_split
    (Δx Δy Δ1 Δ2 : List α) (A B S : α)
    (h : Δx ++ B :: A :: Δy = Δ1 ++ S :: Δ2) :
    SwapSplit Δx Δy Δ1 Δ2 A B S :=
  match Δx with
  | [] =>
      match Δ1 with
      | [] => by
          cases h
          exact SwapSplit.atB rfl rfl rfl
      | d :: Δ1' => by
          have hd : B = d := by
            have hob : some B = some d := by
              simpa using congrArg List.head? h
            exact Option.some.inj hob
          have htail : A :: Δy = Δ1' ++ S :: Δ2 := by
            simpa using congrArg List.tail h
          cases hd
          match Δ1' with
          | [] =>
              have hAS : A = S := by
                have hob : some A = some S := by
                  simpa using congrArg List.head? htail
                exact Option.some.inj hob
              have hDy : Δy = Δ2 := by
                simpa using congrArg List.tail htail
              exact SwapSplit.atA [] rfl hAS rfl hDy.symm
          | a1 :: Δ1b =>
              have hAa1 : A = a1 := by
                have hob : some A = some a1 := by
                  simpa using congrArg List.head? htail
                exact Option.some.inj hob
              have hDy : Δy = Δ1b ++ S :: Δ2 := by
                simpa using congrArg List.tail htail
              cases hAa1
              exact SwapSplit.left Δ1b rfl hDy
  | a :: Δx' =>
      match Δ1 with
      | [] => by
          have hcons : a :: (Δx' ++ B :: A :: Δy) = S :: Δ2 := by
            simpa [List.append_assoc] using h
          cases hcons
          exact SwapSplit.right Δx' Δy rfl rfl rfl
      | b :: Δ1' => by
          have hcons : a :: (Δx' ++ B :: A :: Δy) = b :: (Δ1' ++ S :: Δ2) := by
            simpa [List.append_assoc] using h
          have hab : a = b := by
            have hob : some a = some b := by
              simpa using congrArg List.head? hcons
            exact Option.some.inj hob
          have htail : Δx' ++ B :: A :: Δy = Δ1' ++ S :: Δ2 := by
            simpa using congrArg List.tail hcons
          cases hab
          have r := classify_swap_vs_split (Δx := Δx') (Δy := Δy) (Δ1 := Δ1') (Δ2 := Δ2)
              (A := A) (B := B) (S := S) htail
          cases r with
          | left Δ1b hΔ1 hΔy =>
              refine SwapSplit.left Δ1b ?_ hΔy
              have : a :: Δ1' = a :: (Δx' ++ B :: A :: Δ1b) := by
                simpa using congrArg (fun t => a :: t) hΔ1
              simpa [List.append_assoc] using this
          | right Δ2a Δ2b hΔx hΔ2 hΔy =>
              refine SwapSplit.right Δ2a Δ2b ?_ hΔ2 hΔy
              have : a :: Δx' = a :: (Δ1' ++ S :: Δ2a) := by
                simpa using congrArg (fun t => a :: t) hΔx
              simpa [List.append_assoc] using this
          | atA Δ1a hΔx hAS hΔ1 hΔ2 =>
              refine SwapSplit.atA (a :: Δ1a) ?_ hAS ?_ hΔ2
              · simpa using congrArg (fun t => a :: t) hΔx
              · have : a :: Δ1' = a :: (Δ1a ++ [B]) := by
                  simpa using congrArg (fun t => a :: t) hΔ1
                simpa [List.append_assoc] using this
          | atB hΔx hBS hΔ2 =>
              refine SwapSplit.atB ?_ hBS hΔ2
              simpa using congrArg (fun t => a :: t) hΔx

end List
