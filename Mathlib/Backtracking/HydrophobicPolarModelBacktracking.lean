/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Backtracking.BacktrackingVerification
import Mathlib.Data.Vector.Defs
import Batteries.Data.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Backtracking.HydrophobicPolarModel
import Mathlib.Tactic.FinCases
/-!
# Hydrophobic-polar protein folding model: automatic use of backtracking

A treatment of the hydrophobic-polar protein folding model in a generality
that covers rectangular, triangular and hexagonal lattices: `P_rect`, `P_tri`, `P_hex`.

We formalize the non-monotonicity of the objective function,
refuting an unpublished conjecture of Stecher.

We prove objective function bounds:
`P_tri ≤ P_rect ≤ P_hex` (using a theory of embeddings)
and for any model, `P ≤ b * l` and `P ≤ l * (l-1)/2` [see `pts_earned_bound_loc'`]

(The latter is worth keeping when `l ≤ 2b+1`.)

where `b` is the number of moves and `l` is the word length.
We also prove `P ≤ b * l / 2` using "handshake lemma" type reasoning
that was pointed out in Agarwala, Batzoglou et al. (`RECOMB 97`, Lemma 2.1)
and a symmetry assumption on the folding model that holds for `rect` and `hex` but not for `tri`.
The latter result required improving our definitions.

We prove the correctness of our backtracking algorithm for protein folding.

To prove some results about rotations
(we can always assume our fold starts by going to the right)
we use the type
`Fin n → α` instead of `Mathlib.Vector α n`

-/


section Backtracking_usage

open Mathlib Finset
/-- . -/
theorem path_cons_suffix {b : ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: Fin b) :
    (path go tail).1 <:+ (path go (head :: tail)).1 := by
  rw [path_cons]
  exact List.suffix_cons (go head <|Vector.head <|path go tail) (path go tail).1


/-- . -/
theorem path_append_suffix {b : ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b))
    (head: List (Fin b)) : (path go tail).1 <:+ (path go (head ++ tail)).1 := by
  induction head with
  |nil                      => exact List.nil_append _ ▸ List.suffix_rfl
  |cons head tail_1 tail_ih => calc _ <:+ (path go (tail_1 ++ tail)).1 := tail_ih
                                    _ <:+ _                            := path_cons_suffix _ _ _

/-- . -/
theorem nodup_path_preserved_under_suffixes {b : ℕ} (go: Fin b → ℤ × ℤ → ℤ × ℤ) (u v : List (Fin b))
    (huv : u <:+ v) (h : List.Nodup (path go v).1) : List.Nodup (path go u).1 := by
  obtain ⟨t,ht⟩ := huv
  obtain ⟨s,hs⟩ := path_append_suffix go u t
  exact List.Nodup.of_append_right <| hs ▸ ht ▸ h

/-- . -/
def NodupPath {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) : MonoPred b := {
  P := (fun moves ↦ List.Nodup (path go moves).1)
  preserved_under_suffixes := nodup_path_preserved_under_suffixes _}

/-- . -/
def first_nonzero_entry (moves : List (Fin 4)) : Option (Fin 4) := by
  induction moves with
  | nil                 => exact none
  | cons head _ tail_ih => exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)




/-- By symmetry we may assume that all walks (folds) are orderly,
  although that in itself could deserve a proof.-/
def orderly_and_nontrivial (moves: List (Fin 4)) := moves.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry moves.reverse = some 2

/-- February 24, 2024 -/
def orderly (moves: List (Fin 4)) :=
  (moves.reverse.getLast? = some (0:Fin 4) ∨
   moves.reverse.getLast? = none) ∧ (
   first_nonzero_entry moves.reverse = some 2 ∨
   first_nonzero_entry moves.reverse = none)

/-- . -/
instance (moves : List (Fin 4)) : Decidable (orderly moves) := by
  unfold orderly; exact instDecidableAnd

/-- . -/
instance (moves : List (Fin 4)) : Decidable (orderly_and_nontrivial moves) := by
  unfold orderly_and_nontrivial; exact instDecidableAnd

/-- . -/
def rotate : ℤ × ℤ → ℤ × ℤ := fun (x,y) ↦ (-y,x)
/-- . -/
def reflect: ℤ × ℤ → ℤ × ℤ := fun (x,y) ↦ (x,-y)
/-- . -/
def rotateIndex (a : Fin 4) : Fin 4 := match a with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0

/-- . -/
def reflectIndex (a : Fin 4) : Fin 4 := match a with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

/-- . -/
theorem reflect_basic (u : ℤ × ℤ) (c: Fin 4) :
    reflect (rect c u) = rect (reflectIndex c) (reflect u) := by
  unfold reflect rect
  simp only [neg_add_rev]
  apply Prod.ext
  fin_cases c <;> (simp only [Prod.fst_add, add_right_inj];decide;)
  fin_cases c <;> (simp only [Prod.snd_add]; rw [Int.add_comm];simp only [add_right_inj];decide)

/-- . -/
theorem rotate_basic (u : ℤ × ℤ) (c: Fin 4) :
    rotate (rect c u) = rect (rotateIndex c) (rotate u) := by
  unfold rotate rect
  simp only [neg_add_rev]
  apply Prod.ext
  · rw [Int.add_comm]
    fin_cases c <;> (simp only [Prod.fst_add, add_right_inj]; decide)
  fin_cases c <;> (simp only [Prod.snd_add, add_right_inj]; decide)

/-- . -/
theorem trafo_preserves_nearby (u v : ℤ × ℤ) (huv: nearby rect u v) (trafo : ℤ×ℤ → ℤ×ℤ)
    (trafoIndex: Fin 4 → Fin 4) (trafo_basic :
    ∀ (u : ℤ × ℤ), ∀ (c: Fin 4), trafo (rect c u) = rect (trafoIndex c) (trafo u)) :
    nearby rect (trafo u) (trafo v) := by
  unfold nearby at *;
  simp only [decide_eq_true_eq, Prod.forall] at *;
  obtain ⟨c,hc⟩ := huv
  exact ⟨(trafoIndex c), hc ▸ trafo_basic u.1 u.2 c⟩

/-- . -/
theorem trafo_preserves_nearby_converse {u v : ℤ × ℤ} {trafo : ℤ×ℤ → ℤ×ℤ}
    {trafoIndex: Fin 4 → Fin 4}
    (trafo_basic : ∀ (u : ℤ × ℤ), ∀ (c: Fin 4), trafo (rect c u) = rect (trafoIndex c) (trafo u))
    (huv: nearby rect (trafo u) (trafo v))
    (hs: Function.Surjective trafoIndex) (hi: Function.Injective trafo) :
    nearby rect u v := by
  unfold nearby at *;
  simp only [Prod.forall, decide_eq_true_eq] at *;
  obtain ⟨c,hc⟩ := huv
  obtain ⟨d,hd⟩ := hs c
  rw [← hd] at hc
  rw [← trafo_basic u.1 u.2 d] at hc
  apply hi at hc
  use d

/-- . -/
theorem rotateIndex_surjective : Function.Surjective rotateIndex := by
  intro b
  fin_cases b
  · use 3;rfl
  · use 2;rfl
  · use 0;rfl
  · use 1;rfl

/-- . -/
theorem reflectIndex_surjective : Function.Surjective reflectIndex := by
  intro b
  fin_cases b
  · use 0;rfl
  · use 1;rfl
  · use 3;rfl
  · use 2;rfl

/-- . -/
theorem rotate_injective : Function.Injective rotate := by
  unfold rotate
  intro x y hxy
  rw [Prod.mk.injEq, neg_inj] at hxy
  exact Prod.ext hxy.2 hxy.1

/-- . -/
theorem reflect_injective : Function.Injective reflect := by
  unfold reflect
  intro x y hxy
  simp only [Prod.mk.injEq, neg_inj] at hxy
  exact Prod.ext hxy.1 hxy.2

/-- . -/
theorem rotate_preserves_nearby_converse {u v : ℤ × ℤ} (huv: nearby rect (rotate u) (rotate v)) :
    nearby rect u v :=
  trafo_preserves_nearby_converse rotate_basic huv rotateIndex_surjective rotate_injective

/-- . -/
theorem reflect_preserves_nearby_converse {u v : ℤ × ℤ} (huv: nearby rect (reflect u) (reflect v)) :
    nearby rect u v :=
  trafo_preserves_nearby_converse reflect_basic huv reflectIndex_surjective reflect_injective


/-- This is a first step towards proving that "rotate" preserves pts_tot' -/
theorem rotate_preserves_nearby {u v : ℤ × ℤ} (huv: nearby rect u v) :
    nearby rect (rotate u) (rotate v) :=
  trafo_preserves_nearby _ _ huv _ rotateIndex rotate_basic

/-- . -/
theorem reflect_preserves_nearby {u v : ℤ × ℤ} (huv: nearby rect u v) :
    nearby rect (reflect u) (reflect v) :=
  trafo_preserves_nearby _ _ huv _ reflectIndex reflect_basic


-- roeu = rotate, essentially unary. NOT ALLOWED because of unused argument.
-- def roeu (a : Fin 4) := fun _ : ℤ×ℤ ↦ rotateIndex a

-- reeu = reflect,essentially unary
-- def reeu (a : Fin 4) := fun _ : ℤ×ℤ ↦ reflectIndex a

-- abbrev ρ := roeu -- fun a _ => reflectIndex a

/-- This can be generalized to be in terms of "trafo_eu" -/
lemma rot_length₀ (moves: List (Fin 4)) (k: Fin (Vector.length (path rect moves))) :
    k.1 < Nat.succ (List.length (morph (fun a _ => rotateIndex a) rect moves)) := by
  rw [morph_len]
  simp

/-- . -/
lemma ref_length₀ (moves: List (Fin 4)) (k: Fin (Vector.length (path rect moves))) :
    k.1 < Nat.succ (List.length (morph (fun a _ => reflectIndex a) rect moves)) := by
  rw [morph_len]
  simp

/-- finished 3/8/24 -/
lemma ref_length₀_morf (moves: List (Fin 4)) (k: Fin (Vector.length (path rect moves))) :
    k.1 < Nat.succ (List.length (morf_list reflectIndex moves)) := by
  rw [morf_len]
  simp

/-- . -/
theorem path_len_aux₁ {hd: Fin 4} {tl: List (Fin 4)} (k: Fin <|Vector.length <|path rect <|hd :: tl)
    {s : ℕ} (hs : k.1 = Nat.succ s) : s < Nat.succ (List.length (tl)) := by
  have h₁: Vector.length (path rect (hd :: tl)) = List.length (path rect (hd :: tl)).1 :=
    (path_len' rect (List.length (hd :: tl)) (hd :: tl) rfl).symm
  exact (path_len' rect tl.length _ rfl) ▸ (Nat.succ_inj'.mp h₁) ▸
    Nat.succ_lt_succ_iff.mp (hs ▸ k.2)

/-- . -/
theorem morph_path_succ_aux {hd: Fin 4} {tl: List (Fin 4)}
    (k: Fin (Vector.length (path rect (hd :: tl)))) {s: ℕ} (hs: k.1 = Nat.succ s) :
    s < Nat.succ (List.length (morph (fun a _ => rotateIndex a) rect tl)) := by
  rw [morph_len]
  exact path_len_aux₁ k hs

/-- . -/
theorem morph_path_succ_aux_reeu {hd: Fin 4} {tl: List (Fin 4)}
    (k: Fin (Vector.length (path rect (hd :: tl)))) {s: ℕ} (hs: k.1 = Nat.succ s) :
    s < Nat.succ (List.length (morph (fun a _ => reflectIndex a) rect tl)) := by
  rw [morph_len]
  exact path_len_aux₁ k hs

/-- . -/
theorem morf_path_succ_aux {hd: Fin 4} {tl: List (Fin 4)}
    (k: Fin (Vector.length (path rect (hd :: tl)))) {s: ℕ} (hs: k.1 = Nat.succ s) :
    s < Nat.succ (List.length (morf_list reflectIndex tl)) := by
  rw [morf_len];
  exact path_len_aux₁ k hs


/-- Here is a version of reflect_morph that is simply scaled down
 to not have the extra argument, and use morf_list -/
lemma reflect_morf_list (moves: List (Fin 4)) (k : Fin (path rect moves).length) :
    reflect ((path rect                  moves ).get  k) =
    (path rect (morf_list reflectIndex moves)).get ⟨k.1, ref_length₀_morf moves k⟩ := by
  induction moves with
  |nil => have : k = 0 := Fin.ext (Fin.val_eq_zero k);rw [this];rfl
  |cons hd tl tail_ih =>
    rw [path_cons_vec]
    by_cases h : k = 0
    · subst h
      simp only [List.length_cons, Vector.get_zero, Vector.head_cons, Fin.val_zero,
        Fin.zero_eta]
      rw [reflect_basic]
      have := tail_ih 0
      have : reflect (path rect tl).head = (path rect (morf_list (reflectIndex) tl)).head := by
        simp_all
      exact congr_arg _ this

    · obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      simp_all only [Nat.succ_eq_add_one, List.length_cons, Vector.get_cons_succ, Fin.val_succ]
      norm_cast


/-- Finished February 26, 2024, although the proof is hard to understand:
 (reflect_morph and rotate_morph can have a common generalization) -/
lemma reflect_morph (moves: List (Fin 4)) (k : Fin (path rect moves).length):
    reflect ((path rect                  moves ).get  k) =
             (path rect (morph (fun a _ => reflectIndex a) rect moves)).get
             ⟨k.1, ref_length₀ moves k⟩ := by
  induction moves with
  | nil => (have : k = 0 := Fin.ext (Fin.val_eq_zero k));subst this;rfl
  | cons hd tl tail_ih =>
    rw [path_cons_vec]
    by_cases h : k = 0
    · subst h
      simp only [List.length_cons, Vector.get_zero, Vector.head_cons,
        Fin.val_zero, Fin.zero_eta];
      rw [reflect_basic]
      have Q := tail_ih 0;
      simp_all
      rw [← Q]
      exact congr_arg _ Q
    · obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      simp_all only [Nat.succ_eq_add_one, List.length_cons, Vector.get_cons_succ, Fin.val_succ]
      norm_cast

/-- . -/
lemma rotate_morph (moves: List (Fin 4)) (k : Fin (path rect moves).length):
    rotate ((path rect                  moves ).get  k) =
            (path rect (morph (fun a _ => rotateIndex a) rect moves)).get
            ⟨k.1, rot_length₀ moves k⟩ := by
  induction moves with
  | nil => (have : k = 0 := Fin.ext (Fin.val_eq_zero k));subst this;rfl
  | cons hd tl tail_ih =>
    rw [path_cons_vec]
    by_cases h : k = 0
    · rw [h]
      simp only [List.length_cons, Vector.get_zero, Vector.head_cons, Fin.val_zero,
        Fin.zero_eta];
      rw [rotate_basic]
      have Q := tail_ih 0
      simp only [Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q
      exact congr_arg _ Q
    · obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      simp_all only [Nat.succ_eq_add_one, List.length_cons, Vector.get_cons_succ, Fin.val_succ]
      norm_cast

-- Completed March 6, 2024:
/-- To avoid type problems,
  1. Separate proofs into their own have-statements
  2. Don't let any variables get automatically cast into ↑↑↑k versions;
  instead specify their type whenever possible. See *** below.
-/
lemma rotate_morphᵥ {l: ℕ} {moves: Vector (Fin 4) l} (k : Fin l.succ):
    rotate ((pathᵥ κ                moves).get  k) =
            (pathᵥ κ (morphᵥ (fun a _ => rotateIndex a) κ moves)).get k := by
  have : k.1 < Vector.length (path κ moves.1) := by
    have R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  have h₁: rotate (Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = rotate (Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [← h₁, rotate_morph]
  norm_cast

/-- reflect_morphᵥ is exactly same proof as rotate_morphᵥ -/
lemma reflect_morphᵥ {l: ℕ} {moves: Vector (Fin 4) l} (k : Fin l.succ):
    reflect ((pathᵥ κ                moves).get  k) =
             (pathᵥ κ (morphᵥ (fun a _ => reflectIndex a) κ moves)).get k := by
  have : k.1 < Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  have h₁: reflect (Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = reflect (Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [← h₁, reflect_morph]
  norm_cast

/-- combine reflect_morphᵥ and reflect_morf_list. completed 3/8/24. -/
lemma reflect_morf {l: ℕ} {moves: Vector (Fin 4) l} (k : Fin l.succ):
    reflect ((pathᵥ κ                moves).get  k) =
            (pathᵥ κ (morf reflectIndex moves)).get k := by
  have : k.1 < Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  have h₁: reflect (Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = reflect (Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [← h₁, reflect_morf_list]
  norm_cast

/-- Finished March 6, 2024. Improving rotate_preserves_pt_loc. -/
theorem rotate_preserves_pt_loc' {l:ℕ} (moves : Vector (Fin 4) l) (i j : Fin l.succ)
    (ph: Vector Bool l.succ) (hpt: pt_loc κ (π κ moves)  i j ph) :
    pt_loc κ (π κ (morphᵥ (fun a _ => rotateIndex a) κ moves)) i j ph := by
  unfold pt_loc at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  have R := rotate_preserves_nearby hpt.2
  rw [rotate_morphᵥ i, rotate_morphᵥ j] at R
  tauto



/-- just like rotate_preserves_pt_loc' -/
theorem reflect_preserves_pt_loc' {l:ℕ} (moves : Vector (Fin 4) l) (i j : Fin l.succ)
    (ph: Vector Bool l.succ) (hpt: pt_loc κ (π κ moves)  i j ph) :
    pt_loc κ (π κ (morphᵥ (fun a _ => reflectIndex a) κ moves)) i j ph := by
  unfold pt_loc at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  have R := reflect_preserves_nearby hpt.2
  rw [reflect_morphᵥ i, reflect_morphᵥ j] at R
  tauto

/-- just like rotate_preserves_pt_loc'. 3/8/24 -/
theorem reflect_preserves_pt_loc'_morf {l:ℕ} (moves : Vector (Fin 4) l) (i j : Fin l.succ)
    (ph: Vector Bool l.succ) (hpt: pt_loc κ (π κ moves)  i j ph) :
                                   pt_loc κ (π κ (morf reflectIndex moves)) i j ph := by
  unfold pt_loc at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  have R := reflect_preserves_nearby hpt.2
  rw [reflect_morf i, reflect_morf j] at R
  tauto

/-- Completed March 6, 2024. So easy :) -/
theorem rotate_pts'_atᵥ {l : ℕ} (k : Fin l.succ) (ph : Vector Bool l.succ)
    (moves : Vector (Fin 4) l) : pts_at' κ k ph (π κ moves) ≤
                                 pts_at' κ k ph (π κ (σ (fun a _ => rotateIndex a) κ moves)) :=
  card_le_card fun i hi => by
  simp only [mem_filter, mem_univ, true_and] at *
  exact rotate_preserves_pt_loc' moves i k ph hi



/-- just like rotate_pts'_atᵥ -/
theorem reflect_pts'_atᵥ {l:ℕ} (k : Fin l.succ) (ph : Vector Bool l.succ)
    (moves : Vector (Fin 4) l):
    pts_at' κ k ph (π κ moves) ≤
    pts_at' κ k ph (π κ (σ (fun a _ => reflectIndex a) κ moves)) :=
  card_le_card fun i hi => by
  simp only [mem_filter, mem_univ, true_and] at *
  exact reflect_preserves_pt_loc' moves i k ph hi

/-- 3/8/24 -/
theorem reflect_pts'_atᵥ_morf {l:ℕ} (k : Fin l.succ) (ph : Vector Bool l.succ)
    (moves : Vector (Fin 4) l) :
    pts_at' κ k ph (π κ moves) ≤
    pts_at' κ k ph (π κ (morf reflectIndex moves)) := card_le_card fun i hi => by
  simp only [mem_filter, mem_univ, true_and] at *
  exact reflect_preserves_pt_loc'_morf moves i k ph hi

/-- . -/
theorem rotate_pts_tot {l : ℕ} (ph : Vector Bool l.succ) (moves : Vector (Fin 4) l) :
    pts_tot' κ ph (π κ moves) ≤
    pts_tot' κ ph (π κ (σ (fun a _ => rotateIndex a) κ moves)) :=
  sum_le_sum fun _ _ => rotate_pts'_atᵥ _ _ _

/-- 3/8/24 -/
theorem reflect_pts_tot_morf {l : ℕ} (ph : Vector Bool l.succ)(moves : Vector (Fin 4) l) :
    pts_tot' κ ph (π κ moves) ≤
    pts_tot' κ ph (π κ (morf reflectIndex moves)) :=
  sum_le_sum fun _ _ => reflect_pts'_atᵥ_morf _ _ _

/-- . -/
theorem reflect_pts_tot {l : ℕ} (ph : Vector Bool l.succ)(moves : Vector (Fin 4) l) :
    pts_tot' κ ph (π κ moves) ≤
    pts_tot' κ ph (π κ (σ (fun a _ => reflectIndex a) κ moves)) :=
  sum_le_sum fun _ _ => reflect_pts'_atᵥ _ _ _

/-- now we want to argue that we can always rotate to make moves start with 0, since: -/
theorem rotate_until_right (k : Fin 4) :
    k = 0 ∨
    rotateIndex k = 0 ∨
    rotateIndex (rotateIndex k) = 0 ∨
    rotateIndex (rotateIndex (rotateIndex k)) = 0 := by
  fin_cases k <;> aesop

/-- . -/
theorem rotate_head {l : ℕ} (moves: Vector (Fin 4) (Nat.succ l)) :
    rotateIndex (Vector.head moves) = Vector.head (σ (fun a _ => rotateIndex a) κ moves) := by
  obtain ⟨a,⟨u,hu⟩⟩ := Vector.exists_eq_cons moves
  rw [hu, Vector.head_cons]
  rfl

 /-- certainly easier with morfF ! -/
theorem rotate_headF {l : ℕ} (moves: Fin l.succ → (Fin 4)) :
    rotateIndex (moves 0) = (morfF rotateIndex moves) 0 := rfl

/-- . -/
theorem towards_orderlyish {l:ℕ} (ph : Vector Bool l.succ.succ) (moves : Vector (Fin 4) l.succ) :
    ∃ moves', moves'.get 0 = 0 ∧ pts_tot' κ ph (π κ moves) ≤
                                 pts_tot' κ ph (π κ moves') := by
  let m₀ := moves
  let m₁ := (σ (fun a _ => rotateIndex a) κ m₀)
  let m₂ := (σ (fun a _ => rotateIndex a) κ m₁)
  let m₃ := (σ (fun a _ => rotateIndex a) κ m₂)
  cases rotate_until_right (moves.get 0) with
  | inl => use m₀
  | inr h =>
    cases h with
    |inl h_1 =>
      use m₁
      constructor
      · rw [← h_1]
        repeat rw [Vector.get_zero]
        exact .symm <| rotate_head _
      · exact rotate_pts_tot ph m₀
    |inr h_1 =>
      cases h_1 with
      |inl h =>
        exists m₂
        constructor
        · rw [← h];simp only [Vector.get_zero]
          rw [rotate_head m₀, rotate_head m₁]
        · calc
            pts_tot' κ ph (π κ m₀) ≤ pts_tot' κ ph (π κ m₁):= rotate_pts_tot ph moves
            _                      ≤ _ := rotate_pts_tot ph m₁
      |inr h =>
        exists m₃;
        constructor;
        · rw [← h];simp only [Vector.get_zero]
          rw [rotate_head m₀,rotate_head m₁,rotate_head m₂]

        · calc
          pts_tot' κ ph (π κ m₀) ≤ pts_tot' κ ph (π κ m₁) := rotate_pts_tot ph m₀
          _                      ≤ pts_tot' κ ph (π κ m₂) := rotate_pts_tot ph m₁
          _                      ≤ _                      := rotate_pts_tot ph m₂

/--
We can always reflect to make the first entry after 0s (and 1s,
although they are ruled out by injectivity)
be a 2.-/
theorem rotate_until_right_reflect (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ reflectIndex k = 2 := by
  fin_cases k <;> aesop


/-- completed 3/8/24. Next we can point out that 0 can't be followed by 1 in injective fold. -/
theorem towards_orderly {l : ℕ} (ph : Vector Bool l.succ.succ) (moves : Vector (Fin 4) l.succ) :
    ∃ moves', moves'.get 0 = 0 ∧
    (∀ j, (∀ i, i < j → moves'.get i = 0 ∨ moves'.get i = 1) → moves'.get j ≠ 3) ∧
    pts_tot' κ ph (π κ moves) ≤
    pts_tot' κ ph (π κ moves') := by
  obtain ⟨moves₀,hmoves₀⟩ := towards_orderlyish ph moves
  by_cases h₃: (∀ j, (∀ i, i < j → moves₀.get i = 0 ∨ moves₀.get i = 1) → moves₀.get j ≠ 3)
  · exists moves₀;tauto
  · have : ∃ (j : Fin (l + 1)),
      (∀ i < j, Vector.get moves₀ i = 0 ∨ Vector.get moves₀ i = 1)
        ∧ Vector.get moves₀ j = 3 := by
        contrapose h₃;
        simp only [ne_eq, not_forall, not_not, exists_prop, not_exists, not_and]
        intro x hx;contrapose h₃;
        simp only [not_exists, not_and, not_forall, not_not, exists_prop];
        simp only [not_not] at h₃;exists x
    obtain ⟨j,hj⟩ := this
    have : Vector.get (morf reflectIndex moves₀) j = 2 := by
      let Q := hj.2;unfold morf reflectIndex;simp only [Vector.get_map];rw [Q]
    exists (morf reflectIndex moves₀)
    constructor
    · let Q := hmoves₀.1;unfold reflectIndex morf; simp only [Vector.get_zero,
      Vector.head_map];
      simp only [Vector.get_zero] at Q;rw [Q]

    · constructor
      · intro j₁ hj₁
        by_cases h : j₁ < j
        · let Q := hj.1 j₁ h
        -- now it's easy using morf
          cases Q with
          |inl h_1 =>
            intro hc;unfold morf at hc; simp only [Vector.get_map] at hc;
            rw [h_1] at hc
            revert hc
            decide
          |inr h_1 =>
            intro hc;unfold morf at hc; simp only [Vector.get_map] at hc;
            rw [h_1] at hc;revert hc;decide
        · by_cases he : j₁ = j
          · subst he;rw [this];symm;decide
          · have : j < j₁ ∨ j = j₁ ∨ j₁ < j := lt_trichotomy j j₁
            have : j < j₁ := by tauto
            have Q := hj.2
            cases hj₁ j this with
            |inl h_1 =>
              unfold morf at h_1; simp only [Vector.get_map] at h_1
              rw [Q] at h_1;exfalso;revert h_1;decide
            |inr h_1 =>
              unfold morf at h_1; simp only [Vector.get_map] at h_1
              rw [Q] at h_1;exfalso;revert h_1;decide
      · calc _ ≤ pts_tot' κ ph (π κ moves₀) := hmoves₀.2
             _ ≤ _                          := reflect_pts_tot_morf ph moves₀


/-- this is just path_len and morph_len and should be generalized -/
theorem path_morph_len {l : ℕ} (moves: Vector (Fin 4) l) :
    (path rect (morph (fun a _ => rotateIndex a) rect moves.1)).1.length = l.succ := by
  let morph_vec :=
    (⟨morph (fun a _ => rotateIndex a) rect moves.1, morph_len _ _ _⟩ :
    Vector (Fin 4) moves.1.length)
  rw [path_len rect morph_vec]
  simp

-- #eval orderly [0,2,2]
-- #eval orderly []
-- #eval orderly_and_nontrivial []

/-- . -/
def pts_tot'_list_rev {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)) : ℕ :=
    dite (moves.length.succ = ph.length)
      (fun h ↦ pts_tot' -- or pts_tot
        go
        (⟨ph, rfl⟩ : Vector Bool ph.length)
        ⟨(path go moves).1.reverse,(by
          rw [List.length_reverse]
          rw [← h,path_len'];rfl
        )⟩) (fun _ ↦ 0)

/-- . -/
def pts_tot'_list_rev' {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)) : ℕ :=
    dite (moves.length.succ = ph.length)
      (fun h ↦ pts_tot' -- or pts_tot
        go
        (⟨ph, by
          rw [← h]
        ⟩ : Vector Bool moves.length.succ)
        ⟨(path go moves).1.reverse,(by
          rw [List.length_reverse]
          simp_rw [h]
          rw [path_len' go _ moves]
          · exact h
          · rfl
        )⟩) (fun _ ↦ 0)

/-- . -/
def pts_tot'_list {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)) : ℕ :=
    dite (moves.length.succ = ph.length)
      (fun h ↦ pts_tot' -- or pts_tot
        go
        (⟨ph, rfl⟩ : Vector Bool ph.length)
        ⟨(path go moves).1,(by rw [← h,path_len'];rfl)⟩
      ) (fun _ ↦ 0)

/-- this causes problems since "orderly" does not apply to arbitrary b -/
def InjectivePath {b:ℕ} (go : Fin b → ℤ × ℤ → ℤ × ℤ) (ph : List Bool) (p:ℕ) : MonoPred b := {
  P := fun moves => Function.Injective fun i ↦ (path go moves).get i
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := fun moves => pts_tot'_list go ph moves ≥ p ∧ orderly_and_nontrivial moves}

/-- . -/
def InjectivePath₄ (go : Fin 4 → ℤ × ℤ → ℤ × ℤ) (ph : List Bool) (p : ℕ) : MonoPred 4 := {
  P := (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (fun moves : List (Fin 4) ↦ pts_tot'_list go ph moves ≥ p ∧ orderly_and_nontrivial moves)}

/-- . -/
def InjectivePath₅ (go : Fin 4 → ℤ × ℤ → ℤ × ℤ) (ph : List Bool) (p : ℕ) : MonoPred 4 := {
  P := fun moves ↦ Function.Injective fun i ↦ (path go moves).get i
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := fun moves : List (Fin 4) ↦ pts_tot'_list_rev' go ph moves ≥ p
    ∧ orderly_and_nontrivial moves}

/-- . -/
instance  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (p : ℕ) :
    DecidablePred (InjectivePath₅ go ph p).P := by
  unfold InjectivePath₅
  exact inferInstance

/-- . -/
instance  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (p : ℕ) :
    DecidablePred (InjectivePath₅ go ph p).Q := by
  unfold InjectivePath₅
  exact inferInstance


/-- Now use this to characterize. First add "M.Q". -/
theorem using_backtracking_verification₀ {k L p : ℕ}
    (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (bound : k ≤ L.succ)
    (w : Vector (Fin 4) (L.succ-k))
    (ph : Vector Bool L.succ.succ)
    [DecidablePred (InjectivePath₄ go ph.1 p).P]
    [DecidablePred (InjectivePath₄ go ph.1 p).Q] :
    Fintype.card {v : Vector (Fin 4) L.succ // ((InjectivePath₄ go ph.1 p).P v.1
      ∧ (InjectivePath₄ go ph.1 p).Q v.1) ∧ w.1 <:+ v.1}
    = num_by_backtracking (InjectivePath₄ go ph.1 p).P (InjectivePath₄ go ph.1 p).Q w :=
  backtracking_verification bound (InjectivePath₄ go ph.1 p) w

/-- . -/
theorem using_backtracking_verification₁ {k L p:ℕ}
    (bound : k ≤ L.succ)
    (w : Vector (Fin 4) (L.succ-k))
    (ph : Vector Bool L.succ.succ)
    [DecidablePred (InjectivePath₄ rect ph.1 p).P]
    [DecidablePred (InjectivePath₄ rect ph.1 p).Q] :
    Fintype.card {v : Vector (Fin 4) L.succ // ((InjectivePath₄ rect ph.1 p).P v.1
      ∧ (fun moves ↦ pts_tot'_list rect ph.1 moves ≥ p ∧ orderly_and_nontrivial moves) v.1)
      ∧ w.1 <:+ v.1}
    = num_by_backtracking
      (InjectivePath₄ rect ph.1 p).P
      (fun moves ↦ pts_tot'_list rect ph.1 moves ≥ p ∧ orderly_and_nontrivial moves) w := by
  have R := backtracking_verification bound (InjectivePath₄ rect ph.1 p) w
  simp only [ge_iff_le]
  have : (InjectivePath₄ rect (ph.1) p).Q =
      fun moves => p ≤ pts_tot'_list rect (ph.1) moves ∧ orderly_and_nontrivial moves := by
    rfl
  simp_rw [← this]
  rw [← R]
  apply Fintype.card_congr
  rfl



/-- make these have "go" as a parameter:  -- (there are 7 moves for a polypeptide of length 8) -/
def set_of_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) {l:ℕ} (p:ℕ)
    (ph : Vector Bool l.succ.succ) :=
    satisfy_and_have_suffix
    (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' b l.succ)

/-- (there are 7 moves for a polypeptide of length 8) -/
def set_of_folds_achieving_pts_rev (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
    {l:ℕ} (p:ℕ) (ph : Vector Bool l.succ.succ) :=
    satisfy_and_have_suffix
    (fun moves : List (Fin 4) ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves : List (Fin 4) ↦ pts_tot'_list_rev go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' 4 l.succ)

/-- really, this should be defined in direct terms and then
 prove that it equals satisfy_and_have_suffix (there are 7 moves for a polypeptide of length 8) -/
def goodFolds (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) {l:ℕ} (p:ℕ) (ph : Vector Bool l.succ.succ) :=
  satisfy_and_have_suffix
    (fun moves : List (Fin 4) ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves : List (Fin 4) ↦ pts_tot'_list_rev' go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' 4 l.succ)

/-- . -/
def equifoldable (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) {l:ℕ} (ph₀ ph₁ : Vector Bool l.succ.succ) (p:ℕ) :=
    goodFolds go p ph₀ = goodFolds go p ph₁

/-- . -/
infix:50 " ∼₃ " => (fun ph₀ ph₁ ↦ equifoldable rect₃ ph₀ ph₁ 2)
/-- . -/
infix:50 " ∼ "  => (fun ph₀ ph₁ ↦ equifoldable rect  ph₀ ph₁ 2)

/-- . -/
theorem equifoldable_equivalence (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) {l:ℕ} (p:ℕ) :
    Equivalence (fun (ph₀ ph₁ : Vector Bool l.succ.succ) ↦ equifoldable go ph₀ ph₁ p) := {
  trans := by intro _ _ _ h₀₁ h₁₂;exact Eq.trans h₀₁ h₁₂
  refl := by intros; rfl
  symm := by intro _ _ h;exact h.symm}

/-- . -/
instance (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) {l : ℕ} (ph₀ ph₁ : Vector Bool l.succ.succ) (p:ℕ) :
    Decidable (equifoldable go ph₀ ph₁ p) := by
  unfold equifoldable goodFolds satisfy_and_have_suffix
  simp only [ge_iff_le]
  exact inferInstance


-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[false,false,true,false,false,true,false,true],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[true,true,true,true,true,true,true,true],rfl⟩

-- def o := false
-- def l := true

-- Words of length 6 that have non-∅ values:
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,o,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,o,l,l,l,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,o,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,o,l,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,l,l,l],rfl⟩
-- {[0, 2, 1, 2, 0], [0, 0, 2, 1, 1]}

/-- . -/
def phtoSet {l : ℕ} (ph : Vector Bool l) := filter (fun i ↦ ph.get i) univ

/-- This result from March 29, 2024 proves the obvious fact that
  more H amino acids leads to more points. -/
theorem toSet_dominates {α β:Type} [Fintype β] [Zero α] [DecidableEq α] (go: β → α→α) {l : ℕ}
    (ph₀ ph₁ : Vector Bool l.succ) (hsub: phtoSet ph₀ ⊆ phtoSet ph₁) :
    HP go ph₀ ≤ HP go ph₁ := by
  apply Nat.find_mono
  intro n h moves h_inj
  let h₁ := h moves h_inj
  unfold pts_tot' at *
  have h₀ : (Finset.sum univ fun i =>
    pts_at' go i ph₀ ⟨ (path go moves.1).1, by rw [path_len]⟩)
          ≤ (Finset.sum univ fun i =>
    pts_at' go i ph₁ ⟨ (path go moves.1).1, by rw [path_len]⟩) := by
    apply sum_le_sum
    intro i _
    apply card_le_card
    intro j hj
    unfold pt_loc at *
    simp only [mem_univ, Bool.and_eq_true, decide_eq_true_eq,
      mem_filter, true_and] at *
    unfold phtoSet at hsub

    have h_ : j ∈ filter (fun i' => Vector.get ph₀ i' = true) univ
            ∧ i ∈ filter (fun i' => Vector.get ph₀ i' = true) univ := by
      simp only [mem_filter, mem_univ, true_and];exact hj.1.1
    have Q := And.intro (hsub h_.1) (hsub h_.2)
    simp only [mem_filter, mem_univ, true_and] at Q
    tauto
  exact le_trans h₀ h₁

/-- . -/
theorem more_pts_of_subset (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} {ph₀ ph₁ : Vector Bool l.succ.succ}
    (w: Gap 4 (Nat.succ l) 0) (hsub: phtoSet ph₀ ⊆ phtoSet ph₁) :
    pts_tot'_list_rev' go ph₀.1 w.1 ≤ pts_tot'_list_rev' go ph₁.1 w.1 := by
  unfold pts_tot'_list_rev'
  have : Nat.succ (List.length w.1) = List.length ph₀.1 := by rw [w.2, ph₀.2];rfl
  rw [dif_pos this]
  have : Nat.succ (List.length w.1) = List.length ph₁.1 := by rw [w.2, ph₁.2];rfl
  rw [dif_pos this]
  apply sum_le_sum;   intro i _; unfold pts_at'
  apply card_le_card; intro j _; unfold pt_loc at *
  simp only [Nat.sub_zero, mem_univ, Bool.and_eq_true, decide_eq_true_eq,
    mem_filter, true_and] at *
  have hi: i.1 < l.succ.succ := by
    have := i.2
    simp_all
  have hj: j.1 < l.succ.succ := by
    have := j.2
    simp_all
  have hi': ⟨i.1,hi⟩ ∈ filter (fun i => Vector.get ph₀ i = true) univ := by
    simp only [Nat.sub_zero, mem_filter, mem_univ, true_and]; tauto
  have hj': ⟨j.1,hj⟩ ∈ filter (fun i => Vector.get ph₀ i = true) univ := by
    simp only [Nat.sub_zero, mem_filter, mem_univ, true_and]; tauto
  unfold phtoSet at hsub
  have hsubj := hsub hj'; simp only [Nat.sub_zero, mem_filter,
    mem_univ, true_and] at hsubj;
  have hsubi := hsub hi'; simp only [Nat.sub_zero, mem_filter,
    mem_univ, true_and] at hsubi;
  tauto

/-- . -/
def meet {l:ℕ} (ph₀ ph₁ : Vector Bool l) : Vector Bool l :=
    Vector.ofFn (fun i ↦ ph₀.get i ∧ ph₁.get i)

/-- . -/
infix:50 " ⊓ " => meet

/-- . -/
lemma meet_get {l :ℕ} {ph₀ ph₁ : Vector Bool l} {i:Fin l} :
    (ph₀ ⊓ ph₁).get i = (ph₀.get i ∧ ph₁.get i) := by
  unfold meet
  simp_all

/-- . -/
theorem meet_basic₀ {l : ℕ} {ph₀ ph₁ : Vector Bool l} : phtoSet (ph₀ ⊓ ph₁) ⊆ phtoSet ph₀ := by
  intro i hi
  unfold phtoSet at *
  simp only [mem_filter, mem_univ, true_and] at *
  exact (meet_get ▸ hi).1


/-- verbatim the same proof -/
theorem meet_basic₁ {l : ℕ} {ph₀ ph₁ : Vector Bool l} : phtoSet (ph₀ ⊓ ph₁) ⊆ phtoSet ph₁ := by
  intro i hi
  unfold phtoSet at *
  simp only [mem_filter, mem_univ, true_and] at *
  exact (meet_get ▸ hi).2

/-- nice to be able to use `verify_those_with_suffix`. -/
theorem goodFolds_monotone (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l :ℕ} (ph₀ ph₁ : Vector Bool l.succ.succ)
    (hsub: phtoSet ph₀ ⊆ phtoSet ph₁) (p:ℕ) : goodFolds go p ph₀ ⊆ goodFolds go p ph₁ := by
  let M₀ := InjectivePath₅ go ph₀.1 p
  let M₁ := InjectivePath₅ go ph₁.1 p
  let u := (Gap_nil' 4 (Nat.succ l))
  have verify₀: satisfy_and_have_suffix M₀.P M₀.Q u =
      filter (fun v  ↦ M₀.P v.1 ∧ M₀.Q v.1 ∧ u.1 <:+ v.1) univ :=
    verify_those_with_suffix (le_refl _) u
  have verify₁:
    satisfy_and_have_suffix M₁.P M₁.Q u = filter
      (fun v  ↦ M₁.P v.1 ∧ M₁.Q v.1 ∧ u.1 <:+ v.1) univ :=
    verify_those_with_suffix (le_refl _) u
  simp only [Nat.succ_eq_add_one]
  unfold InjectivePath₅ at verify₀ verify₁
  unfold goodFolds
  simp only [Nat.succ_eq_add_one, ge_iff_le]
  intro w hw₀
  simp only [Nat.succ_eq_add_one, Nat.sub_zero] at verify₀

  change (satisfy_and_have_suffix
    (InjectivePath₅ go (ph₀.1) p).P
    (InjectivePath₅ go (ph₀.1) p).Q u
  = filter (fun v : Gap 4 l.succ 0 ↦ M₀.P v.1 ∧ M₀.Q v.1 ∧ u.1 <:+ v.1) univ)
    at verify₀
  unfold InjectivePath₅ at verify₀
  simp at verify₀
  rw [verify₀] at hw₀

  simp only [mem_filter, mem_univ, true_and] at hw₀
  have hp: p ≤ pts_tot'_list_rev' go ph₁.1 w.1 := LE.le.trans hw₀.2.1.1
    (more_pts_of_subset go w hsub)

  show  w ∈ satisfy_and_have_suffix M₁.P M₁.Q u
  rw [verify₁]
  simp only [Nat.succ_eq_add_one, Nat.sub_zero, mem_filter, mem_univ, true_and]
  constructor
  · tauto
  constructor
  · have T : (InjectivePath₅ go (ph₀.1) p).Q w.1 := hw₀.2.1
    change (InjectivePath₅ go (ph₁.1) p).Q w.1
    unfold InjectivePath₅ at T
    constructor
    · exact hp
    · simp_all
  · simp_all

/--
For the model `rect`, equifoldability is coNP-complete.
It is in coNP since if `x` and `y` are not equifoldable it suffices to produce a fold by which
`x` achieves `k` points and `y` does not.
It is coNP-hard since `x∼∅ [k]` iff `P(x)<k`.
-/
theorem convex_equifoldable {l : ℕ} {ph₀ ph₁ ph₂: Vector Bool l.succ.succ}
    (h₀₁: phtoSet ph₀ ⊆ phtoSet ph₁) (h₁₂: phtoSet ph₁ ⊆ phtoSet ph₂) (h₀₂: ph₀ ∼ ph₂) :
    ph₀ ∼ ph₁ :=
  Subset.antisymm (goodFolds_monotone rect ph₀ ph₁ h₀₁ 2)
           <|h₀₂ ▸ goodFolds_monotone rect ph₁ ph₂ h₁₂ 2

-- theorem monotonicity_of_sim {k l :ℕ} (x₀ y₀: Vector Bool l.succ.succ)
--  (x₁ y₁: Vector Bool k.succ.succ)
-- (h: Vector.append x₀ x₁ ∼ Vector.append y₀ y₁) : x₀ ∼ y₀ := by
--   -- not true, due to Stecher type phenomena:
--   -- let x be a Stecher string, let x' an all-false string of the same length, and
-- consider x++[1] and x'++[1]
--   sorry


/-- points_tot = Fin.card points_loc -/
def goodPairs (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} (fold : Vector (ℤ×ℤ) l) (ph : Vector Bool l) :=
    filter (fun ik : (Fin l) × (Fin l) ↦ ((pt_loc go fold ik.1 ik.2 ph): Prop)) univ

/-- Note that this is not true for ∪ and join. -/
theorem goodPairs_meet (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} (ph₀ ph₁ : Vector Bool l.succ)
    (fold : Vector (ℤ×ℤ) (Nat.succ l)) :
    goodPairs go fold (ph₀ ⊓ ph₁) = goodPairs go fold ph₀ ∩ goodPairs go fold ph₁ :=
  ext <| fun ij => by
  constructor
  · intro hij
    rw [mem_inter]
    unfold goodPairs at *
    simp only [mem_filter, mem_univ, true_and] at *
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    have hi: ij.1 ∈ filter (fun i => Vector.get (meet ph₀ ph₁) i = true) univ := by
      simp only [mem_filter, mem_univ, true_and]; exact hij.1.1.1
    have hj: ij.2 ∈ filter (fun i => Vector.get (meet ph₀ ph₁) i = true) univ := by
      simp only [mem_filter, mem_univ, true_and]; exact hij.1.1.2
    have Si₀ := meet_basic₀ hi
    have Si₁ := meet_basic₁ hi
    have Sj₀ := meet_basic₀ hj
    have Sj₁ := meet_basic₁ hj
    unfold phtoSet at Si₀ Si₁ Sj₀ Sj₁
    simp only [mem_filter, mem_univ, true_and] at Si₀ Si₁ Sj₀ Sj₁
    tauto
  · simp only [mem_inter, and_imp]
    intro h₀ h₁
    unfold goodPairs pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq, mem_filter,
      mem_univ, true_and] at *
    repeat rw [meet_get]
    tauto



-- Words of length 8 that have non-∅ values:
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,o,o],rfl⟩ -- all ∅
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,l,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,l,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,l,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,l,o,o],rfl⟩
--  [0, 2, 1, 2, 0, 2, 0],
--  [0, 0, 2, 1, 1, 2, 0],
--  [0, 0, 2, 1, 1, 1, 1],
--  [0, 2, 1, 2, 0, 2, 1],
--  [0, 0, 2, 1, 1, 2, 1],
--  [0, 2, 1, 2, 0, 0, 2],
--  [0, 0, 2, 1, 1, 1, 2],
--  [0, 2, 1, 2, 0, 2, 2],
--  [0, 0, 2, 1, 1, 2, 2]}-/

-- #eval (
--   ⟨[true,false,true,false,false,true,false,true],rfl⟩ ∼
--   ⟨[true,true,false,false,false,false,true,true],rfl⟩
-- )
-- #eval (
--   ⟨[false,false,true,false,false,true,false,true],rfl⟩ ∼
--   ⟨[true,true,false,false,false,false,true,true],rfl⟩
-- )


/-- . -/
def num_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
    {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ) : ℕ :=
  num_by_backtracking
    (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)

/-- . -/
def can_achieve_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
    {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ): Prop :=
  set_of_folds_achieving_pts go p ph ≠ ∅

/-- . -/
def x : List Bool := [true,false,true,false,true,false, true,true]
-- #eval HP rect ⟨x,rfl⟩           -- This evaluates to 3 quickly, don't even need the backtracking.
-- #eval HP rect ⟨x ++ [false],rfl⟩-- This evaluates to 2 quickly, don't even need the backtracking.
-- example: HP rect ⟨x ++ [false],rfl⟩ = 2 := by decide
-- #eval pts_tot'_list rect  x [0, 3, 1, 1, 2, 2, 0]
-- #eval pts_tot'_list rect  x [r2.D, r2.S, r2.A, r2.A, r2.W, r2.W, r2.D]
-- #eval pts_tot'_list rect  (x ++ [false]) [0, 3, 1, 1, 2, 2, 0].reverse

-- def quad : Fin 4 → ℤ×ℤ → ℤ×ℤ
-- | 0 => go_D
-- | 1 => go_A
-- | 2 => sp
-- | 3 => sm

/-- . -/
def stecher1 : Prop :=
    satisfy_and_have_suffix
      (fun w ↦ Function.Injective fun i ↦ (path rect w).get i)
      (fun w ↦ pts_tot'_list rect  x w > 2 ∧ orderly_and_nontrivial w)
      (Gap_nil' 4 7) -- (there are 7 moves for a polypeptide of length 8)
    = {⟨[0, 2, 2, 1, 1, 3, 0],rfl⟩} --{⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}

/-- . -/
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}
-- #eval [0,2,1].reverse.getLast?
-- #eval first_nonzero_entry [0,2,1]
-- #eval orderly_and_nontrivial [0,2,1]
-- #eval   (satisfy_and_have_suffix
--     (fun w ↦ Function.Injective (fun i ↦ (path quad w).get i))
--     (fun w ↦ pts_tot'_list rect  ([true,false,false,true]) w > 0 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 3)) -- fixed February 20, 2024

-- #eval   (satisfy_and_have_suffix
--     (fun w ↦ Function.Injective (fun i ↦ (path quad w).get i))
--     (fun w ↦ pts_tot'_list rect  (List.replicate L.succ true) w ≥ 5 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 L)) -- fixed February 20, 2024

-- #eval HP rect ⟨[true],rfl⟩
-- #eval HP rect ⟨List.replicate 9 true,rfl⟩ -- 4
-- #eval HP rect ⟨List.replicate L.succ true,rfl⟩ -- 4
-- #eval HP hex ⟨List.replicate 3 true,rfl⟩ -- amazing


-- example (x : Fin 1 → Bool): HP hex (Vector.ofFn x) = 0 := by
--   unfold Vector.ofFn
--   cases H : x 0 <;> aesop

-- example (x : Fin 2 → Bool): HP hex (Vector.ofFn x) = 0 := by
--   repeat unfold Vector.ofFn
--   cases H : x 0 <;> cases G : x 1 <;> aesop

-- example {b : Bool}: HP hex ⟨[true, b, true],rfl⟩ = 1 := by
--   cases H : b <;> aesop

-- example {a b c : Bool}: HP hex ⟨[a, b, c],rfl⟩ = 0 ↔ a = false ∨ c = false := by
--   cases a <;> cases b <;> (cases c; aesop; decide)

-- example {x : Fin 3 → Bool}: HP hex (Vector.ofFn x) = 0 ↔ x 0 = false ∨ x 2 = false := by
--   repeat unfold Vector.ofFn
--   cases h₀ : x 0 <;> cases h₁ : x 1 <;> (cases h₂ : x 2; aesop; simp_all; decide)

-- #eval HP hex ⟨[false, false, false, false, false, true, true, true],rfl⟩
-- #eval (myvec 4 7).length
-- #eval stecher1

/-- . -/
def stecher2 : Prop :=
satisfy_and_have_suffix
    (fun w ↦ Function.Injective (fun i ↦ (path rect w).get i))
    (fun w ↦ pts_tot'_list rect  (x ++ [false]) w > 2
        ∧ orderly_and_nontrivial w)
    (Gap_nil' 4 8) = ∅

-- #eval (satisfy_and_have_suffix
--     (fun w ↦ Function.Injective (fun i ↦ (path rect w).get i))
--     (fun w ↦ pts_tot'_list rect  x w > 2 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 7))

-- #eval (satisfy_and_have_suffix
--     (fun w ↦ Function.Injective (fun i ↦ w.get i))
--     (fun w ↦ w = [0,0])
--     (Gap_nil' 4 2))

/-- . -/
def stecher_conjecture_counterexample : Prop := stecher1  ∧ stecher2

/-- . -/
instance : Decidable stecher2 := by unfold stecher2; apply decEq

/-- . -/
instance : Decidable stecher_conjecture_counterexample := by
  unfold stecher_conjecture_counterexample; unfold stecher1; unfold stecher2; exact instDecidableAnd
--ONE OPTION IS TO COMMENT OUT EVERYTHING NOT NEEDED FOR THIS INSTANCE
-- #eval stecher1
-- #eval stecher2
-- #reduce stecher_conjecture_counterexample

end Backtracking_usage
