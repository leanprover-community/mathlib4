/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Backtracking.BacktrackingVerification
import Mathlib.Computability.NFA
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Defs
import Batteries.Data.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Backtracking.HydrophobicPolarModel
/-!
# Marginis

-/

-- import Mathlib.Tactic


/-

[
Updated June 30, 2024 to fit
  - new Mathlib
  - match-with use in BacktrackingVerification.lean
]

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

In `HPModel_pathF'.lean` we showed that orderly walks are sufficient,
in particular "3" (down) can be avoided by reflection,
      except got stuck on proving that the moves left followed by right lead to non-injectivity,
      which was not a problem using pathF.
-/


section Backtracking_usage

theorem path_cons_suffix
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: Fin b):
(path go tail).1 <:+ (path go (head :: tail)).1
:= by
  rw [path_cons]
  exact List.suffix_cons (go head (Mathlib.Vector.head (path go tail))) (path go tail).1


theorem path_append_suffix
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: List (Fin b)):
(path go tail).1 <:+ (path go (head ++ tail)).1
:= by
  induction head with
  |nil => simp only [List.nil_append]; exact List.suffix_rfl
  |cons head tail_1 tail_ih =>
    calc _ <:+ (path go (tail_1 ++ tail)).1 := tail_ih
         _ <:+ _                            := path_cons_suffix _ _ _


theorem nodup_path_preserved_under_suffixes
{b: ℕ}
(go: Fin b → ℤ × ℤ → ℤ × ℤ)
: ∀ (u v : List (Fin b)),
  u <:+ v → (fun moves => List.Nodup (path go moves).1) v →
    (fun moves => List.Nodup (path go moves).1) u
:=
  by
      intro u v huv
      obtain ⟨t,ht⟩ := huv
      symm at ht
      subst ht
      simp only
      intro h
      obtain ⟨s,hs⟩ := path_append_suffix go u t
      rw [← hs] at h
      exact List.Nodup.of_append_right h

def NodupPath {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)  : MonoPred b :=
{
  P := (fun moves ↦ List.Nodup (path go moves).1)
  preserved_under_suffixes := nodup_path_preserved_under_suffixes _
}

def first_nonzero_entry (moves : List (Fin 4)) : Option (Fin 4) := by
  induction moves with
  | nil                 => exact none
  | cons head _ tail_ih => exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)

-- Here's the Fin.find version:
def where_first_nonzero_entryF {l:ℕ} (moves : Fin l → (Fin 4)) : Option (Fin l)
  := Fin.find (fun i ↦ moves i ≠ 0)
def first_nonzero_entryF {l:ℕ} (moves : Fin l → (Fin 4)) : Option (Fin 4) :=
dite (Option.isSome (where_first_nonzero_entryF moves))
  (fun h ↦ some (moves ((where_first_nonzero_entryF moves).get h)))
  (fun _ ↦ none
  )



/-- By symmetry we may assume that all walks (folds) are orderly,
  although that in itself could deserve a proof.-/
def orderly_and_nontrivial (moves: List (Fin 4)) := moves.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry moves.reverse = some 2

def orderly (moves: List (Fin 4)) := -- February 24, 2024
  (
    moves.reverse.getLast? = some (0:Fin 4) ∨
    moves.reverse.getLast? = none
  ) ∧ (
    first_nonzero_entry moves.reverse = some 2 ∨
    first_nonzero_entry moves.reverse = none
  )

instance (moves : List (Fin 4)) : Decidable (orderly moves) := by
  unfold orderly; exact instDecidableAnd
instance (moves : List (Fin 4)) : Decidable (orderly_and_nontrivial moves) := by
  unfold orderly_and_nontrivial; exact instDecidableAnd

def rotate : ℤ × ℤ → ℤ × ℤ := fun (x,y) ↦ (-y,x)
def reflect: ℤ × ℤ → ℤ × ℤ := fun (x,y) ↦ (x,-y)
def rotateIndex (a : Fin 4) : Fin 4 := match a with
| 0 => 2
| 1 => 3
| 2 => 1
| 3 => 0

def reflectIndex (a : Fin 4) : Fin 4 := match a with
| 0 => 0
| 1 => 1
| 2 => 3
| 3 => 2

theorem reflect_basic (u : ℤ × ℤ) (c: Fin 4):
reflect (rect c u) = rect (reflectIndex c) (reflect u)
:= by
  unfold reflect rect;simp only [neg_add_rev]
  exact match c with
  | 0 => by
    apply Prod.ext
    · simp only [Prod.fst_add, add_right_inj];
      decide;
    · simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide
  | 1 => by
    apply Prod.ext
    · simp only [Prod.fst_add, add_right_inj];
      decide;
    · simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide
  | 2 => by
    apply Prod.ext
    · simp only [Prod.fst_add, add_right_inj];
      decide;
    · simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide
  | 3 => by
    apply Prod.ext
    · simp only [Prod.fst_add, add_right_inj];
      decide;
    · simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide

theorem rotate_basic (u : ℤ × ℤ) (c: Fin 4):
rotate (rect c u) = rect (rotateIndex c) (rotate u)
:= by
  unfold rotate rect;simp
  exact match c with
  | 0 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide
  | 1 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide
  | 2 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide
  | 3 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide



theorem trafo_preserves_nearby (u v : ℤ × ℤ) (huv: nearby rect u v)
(trafo : ℤ×ℤ → ℤ×ℤ) (trafoIndex: Fin 4 → Fin 4)
(trafo_basic : ∀ (u : ℤ × ℤ), ∀ (c: Fin 4), trafo (rect c u) = rect (trafoIndex c) (trafo u)
)
:
nearby rect (trafo u) (trafo v) := by
  unfold nearby at *;
  simp only [decide_eq_true_eq, Prod.forall] at *;
  obtain ⟨c,hc⟩ := huv
  subst hc;
  exists (trafoIndex c);
  exact trafo_basic u.1 u.2 c

theorem trafo_preserves_nearby_converse {u v : ℤ × ℤ}
{trafo : ℤ×ℤ → ℤ×ℤ} {trafoIndex: Fin 4 → Fin 4} (trafo_basic : ∀ (u : ℤ × ℤ), ∀ (c: Fin 4),
trafo (rect c u) = rect (trafoIndex c) (trafo u)
)
(huv: nearby rect (trafo u) (trafo v))
(hs: Function.Surjective trafoIndex)
(hi: Function.Injective trafo)
:
nearby rect u v := by
  unfold nearby at *;
  simp only [Prod.forall, decide_eq_true_eq] at *;
  obtain ⟨c,hc⟩ := huv
  have : ∃ d, trafoIndex d = c := hs c
  obtain ⟨d,hd⟩ := this
  rw [← hd] at hc
  let Q := trafo_basic u.1 u.2 d
  rw [← Q] at hc
  apply hi at hc
  exists d

lemma four_choices₀ (b : Fin 4): b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 ∨ b.1 = 3 := by
  cases Nat.lt_or_eq_of_le (Fin.is_le b) with
    |inr => tauto
    |inl h =>
      cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h) with
        |inr => tauto
        |inl h_1 =>
          cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_1) with
            |inr => tauto
            |inl h_2 => left;exact Nat.lt_one_iff.mp h_2;

lemma four_choices (b : Fin 4): b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
  cases four_choices₀ b with
  |inl h => left;exact Fin.ext h;
  |inr h =>
    cases h with
    |inl h_1 => right;left;exact Fin.ext h_1
    |inr h_1 =>
      cases h_1 with
      |inl h => right;right; left;exact Fin.ext h
      |inr h => right;right;right;exact Fin.ext h

theorem rotateIndex_surjective : Function.Surjective rotateIndex := by
  intro b
  cases (four_choices b) with
  |inl h₀ => subst h₀; exists 3
  |inr h₀ =>
    cases h₀ with
    |inl h₁ => subst h₁; exists 2
    |inr h₁ =>
      cases h₁ with
      |inl h₂ => subst h₂; exists 0
      |inr h₂ => subst h₂; exists 1

theorem reflectIndex_surjective : Function.Surjective reflectIndex := by
  intro b
  cases (four_choices b) with
  |inl h₀ => subst h₀; exists 0
  |inr h₀ =>
    cases h₀ with
    |inl h₁ => subst h₁; exists 1
    |inr h₁ =>
      cases h₁ with
      |inl h₂ => subst h₂; exists 3
      |inr h₂ => subst h₂; exists 2

theorem rotate_injective : Function.Injective rotate := by
  intro x y hxy;unfold rotate at hxy;simp only [Prod.mk.injEq, neg_inj] at hxy
  apply Prod.ext;tauto;tauto

theorem reflect_injective : Function.Injective reflect := by
  intro x y hxy;unfold reflect at hxy;simp only [Prod.mk.injEq, neg_inj] at hxy
  apply Prod.ext;tauto;tauto


theorem rotate_preserves_nearby_converse {u v : ℤ × ℤ}
(huv: nearby rect (rotate u) (rotate v))
    : nearby rect u v
  := trafo_preserves_nearby_converse rotate_basic huv rotateIndex_surjective rotate_injective

theorem reflect_preserves_nearby_converse {u v : ℤ × ℤ}
(huv: nearby rect (reflect u) (reflect v))
    : nearby rect u v
  := trafo_preserves_nearby_converse reflect_basic huv reflectIndex_surjective reflect_injective


-- This is a first step towards proving that "rotate" preserves pts_tot':
theorem rotate_preserves_nearby {u v : ℤ × ℤ} (huv: nearby rect u v):
nearby rect (rotate u) (rotate v) :=
  trafo_preserves_nearby _ _ huv _ rotateIndex rotate_basic

theorem reflect_preserves_nearby {u v : ℤ × ℤ} (huv: nearby rect u v):
nearby rect (reflect u) (reflect v) :=
    trafo_preserves_nearby _ _ huv _ reflectIndex reflect_basic



def roeu := (fun a : Fin 4 ↦ fun _ : ℤ×ℤ ↦ rotateIndex a) -- roeu = rotate, essentially unary
def reeu := (fun a : Fin 4 ↦ fun _ : ℤ×ℤ ↦ reflectIndex a) -- reeu = reflect,essentially unary
abbrev ρ := roeu

-- This can be generalized to be in terms of "trafo_eu":
lemma rot_length₀ (moves: List (Fin 4))
(k: Fin (Mathlib.Vector.length (path rect moves)))
: k.1 < Nat.succ (List.length (morph roeu rect moves))
:= by
  rw [morph_len];simp;
lemma ref_length₀ (moves: List (Fin 4))
(k: Fin (Mathlib.Vector.length (path rect moves)))
: k.1 < Nat.succ (List.length (morph reeu rect moves))
:= by
  rw [morph_len];simp;

lemma ref_length₀_morf (moves: List (Fin 4))
(k: Fin (Mathlib.Vector.length (path rect moves)))
: k.1 < Nat.succ (List.length (morf_list reflectIndex moves))
:= by
  rw [morf_len];simp; -- finished 3/8/24


theorem path_len_aux₁
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Mathlib.Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (tl))
:= by
      let Q := k.2
      rw [hs] at Q
      have h₀: s <  (Mathlib.Vector.length (path rect tl)) :=
        Nat.succ_lt_succ_iff.mp Q
      have h₁: Mathlib.Vector.length (path rect (hd :: tl))
               = List.length (path rect (hd :: tl)).1 :=
        (path_len' rect (List.length (hd :: tl)) (hd :: tl) rfl).symm
      have h₂: Mathlib.Vector.length (path rect tl)
               = List.length (path rect tl).1 := Nat.succ_inj'.mp h₁
      rw [h₂,path_len' rect tl.length _ rfl] at h₀
      exact h₀

theorem morph_path_succ_aux
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Mathlib.Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (morph roeu rect tl))
:= by
      let h₀ := path_len_aux₁ k hs
      rw [morph_len];
      exact h₀

theorem morph_path_succ_aux_reeu
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Mathlib.Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (morph reeu rect tl))
:= by
      let h₀ := path_len_aux₁ k hs
      rw [morph_len];
      exact h₀

theorem morf_path_succ_aux
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Mathlib.Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (morf_list reflectIndex tl))
:= by
      let h₀ := path_len_aux₁ k hs
      rw [morf_len];
      exact h₀


-- Here is a version of reflect_morph that is simply scaled down
-- to not have the extra argument, and use morf_list
lemma reflect_morf_list (moves: List (Fin 4)) (k : Fin (path rect moves).length):
  reflect ((path rect                  moves ).get  k) =
          (path rect (morf_list reflectIndex moves)).get ⟨k.1, ref_length₀_morf moves k⟩
:= by
  induction moves with
  |nil => (have : k = 0 := Fin.ext (Fin.coe_fin_one k));subst this;rfl
  |cons hd tl tail_ih =>
    rw [path_cons_vec]
    by_cases h : k = 0
    · subst h
      simp only [List.length_cons, Mathlib.Vector.get_zero, Mathlib.Vector.head_cons, Fin.val_zero,
        Fin.zero_eta]
      rw [reflect_basic]
      have : reflect (path rect tl).head = (path rect (morf_list (reflectIndex) tl)).head
      := by
        let Q := tail_ih 0;
        simp only [Mathlib.Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q ;exact Q
      exact congr_arg _ this

    obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
    have g₀: ((rect hd (path rect tl).head) ::ᵥ path rect tl).get (Fin.succ s)
                                            = (path rect tl).get s := rfl
    have g₄: ((rect hd (path rect tl).head) ::ᵥ path rect tl).get k
                                            = (path rect tl).get s := by rw [hs,← g₀]
    rw [g₄]
    have g₁: path rect (morf_list reflectIndex (hd :: tl))
          = path rect ((reflectIndex hd ) :: (morf_list reflectIndex (tl))) := rfl
    rw [g₁,path_cons_vec]
    have hs': k.1 = s.1.succ := Fin.mk_eq_mk.mp hs
    have g₃: k.1 < (morf_list reflectIndex (hd :: tl)).length.succ
      := by rw [morf_len];simp
    have g₂: (
        rect (reflectIndex hd)
        ((path rect (morf_list reflectIndex tl)).head)
      ::ᵥ path rect (morf_list reflectIndex tl)).get ⟨k.1, g₃⟩
      = (path rect (morf_list reflectIndex tl)).get ⟨s, morf_path_succ_aux k hs'⟩
      := by simp_rw [hs'];norm_cast
    · rw [g₂,tail_ih s]


-- Finished February 26, 2024, although the proof is hard to understand:
-- (reflect_morph and rotate_morph can have a common generalization)
lemma reflect_morph (moves: List (Fin 4)) (k : Fin (path rect moves).length):
  reflect ((path rect                  moves ).get  k) =
          (path rect (morph reeu rect moves)).get ⟨k.1, ref_length₀ moves k⟩
:= by
  induction moves with
  | nil => (have : k = 0 := Fin.ext (Fin.coe_fin_one k));subst this;rfl
  | cons hd tl tail_ih =>
    rw [path_cons_vec]
    by_cases h : k = 0
    · -- pos
      subst h; simp only [List.length_cons, Mathlib.Vector.get_zero, Mathlib.Vector.head_cons,
        Fin.val_zero, Fin.zero_eta];
      rw [reflect_basic];let Q := tail_ih 0;
      simp only [Mathlib.Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q ;exact congr_arg _ Q
    · -- neg
      obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      subst hs
      simp only [List.length_cons, Mathlib.Vector.get_cons_succ, Fin.val_succ]
      rw [tail_ih s]
      have g₁: path κ (morph reeu rect (hd :: tl))
             = path κ ((     reeu       hd ((path κ tl).head)) :: (morph reeu κ tl)) := rfl
      rw [g₁, path_cons_vec]
      norm_cast

lemma rotate_morph (moves: List (Fin 4)) (k : Fin (path rect moves).length):
  rotate ((path rect                  moves ).get  k) =
          (path rect (morph roeu rect moves)).get ⟨k.1, rot_length₀ moves k⟩
:= by
  induction moves with
  | nil => (have : k = 0 := Fin.ext (Fin.coe_fin_one k));subst this;rfl
  | cons hd tl tail_ih =>
    rw [path_cons_vec]
    by_cases h : k = 0
    · -- pos
      subst h;
      simp only [List.length_cons, Mathlib.Vector.get_zero, Mathlib.Vector.head_cons, Fin.val_zero,
        Fin.zero_eta];
      rw [rotate_basic];let Q := tail_ih 0;
      simp only [Mathlib.Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q ;exact congr_arg _ Q
    · -- neg
      obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      subst hs
      simp only [List.length_cons, Mathlib.Vector.get_cons_succ, Fin.val_succ]
      rw [tail_ih s]
      have g₁: path κ (morph ρ rect (hd :: tl))
             = path κ ((     ρ       hd ((path κ tl).head)) :: (morph ρ κ tl)) := rfl
      rw [g₁, path_cons_vec]
      norm_cast

-- Completed March 6, 2024:
/- To avoid type problems,
  1. Separate proofs into their own have-statements
  2. Don't let any variables get automatically cast into ↑↑↑k versions;
  instead specify their type whenever possible. See *** below.
-/
lemma rotate_morphᵥ {l: ℕ} {moves: Mathlib.Vector (Fin 4) l} (k : Fin l.succ):
  rotate ((pathᵥ κ                moves).get  k) =
          (pathᵥ κ (morphᵥ roeu κ moves)).get k
:= by
  have : k.1 < Mathlib.Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  let Q := rotate_morph moves.1 ⟨k,this⟩ -- ***
  have h₁: rotate (Mathlib.Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = rotate (Mathlib.Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [h₁] at Q
  rw [← h₁, rotate_morph]
  norm_cast

-- reflect_morphᵥ is exactly same proof as rotate_morphᵥ
lemma reflect_morphᵥ {l: ℕ} {moves: Mathlib.Vector (Fin 4) l} (k : Fin l.succ):
  reflect ((pathᵥ κ                moves).get  k) =
          (pathᵥ κ (morphᵥ reeu κ moves)).get k
:= by
  have : k.1 < Mathlib.Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  let Q := reflect_morph moves.1 ⟨k,this⟩ -- ***
  have h₁: reflect (Mathlib.Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = reflect (Mathlib.Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [h₁] at Q
  rw [← h₁, reflect_morph]
  norm_cast

lemma reflect_morf {l: ℕ} {moves: Mathlib.Vector (Fin 4) l} (k : Fin l.succ):
  reflect ((pathᵥ κ                moves).get  k) =
          (pathᵥ κ (morf reflectIndex moves)).get k
:= by
  -- combine reflect_morphᵥ and reflect_morf_list
  -- completed 3/8/24 !
  have : k.1 < Mathlib.Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  let Q := reflect_morf_list moves.1 ⟨k,this⟩ -- ***
  have h₁: reflect (Mathlib.Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = reflect (Mathlib.Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [h₁] at Q
  rw [← h₁, reflect_morf_list]
  norm_cast

theorem rotate_preserves_pt_loc' {l:ℕ}
-- Finished March 6, 2024. Improving rotate_preserves_pt_loc.
  (moves : Mathlib.Vector (Fin 4) l) (i j : Fin l.succ) (ph: Mathlib.Vector Bool l.succ)
  (hpt: pt_loc κ (π κ             moves)  i j ph)
  :     pt_loc κ (π κ (morphᵥ roeu κ moves)) i j ph
  := by
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := rotate_preserves_nearby hpt.2
    rw [rotate_morphᵥ i, rotate_morphᵥ j] at R
    tauto



theorem reflect_preserves_pt_loc' {l:ℕ}
-- just like rotate_preserves_pt_loc'
  (moves : Mathlib.Vector (Fin 4) l) (i j : Fin l.succ) (ph: Mathlib.Vector Bool l.succ)
  (hpt: pt_loc κ (π κ             moves)  i j ph)
  :     pt_loc κ (π κ (morphᵥ reeu κ moves)) i j ph
  := by
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := reflect_preserves_nearby hpt.2
    rw [reflect_morphᵥ i, reflect_morphᵥ j] at R
    tauto

theorem reflect_preserves_pt_loc'_morf {l:ℕ}
-- just like rotate_preserves_pt_loc'. 3/8/24
  (moves : Mathlib.Vector (Fin 4) l) (i j : Fin l.succ) (ph: Mathlib.Vector Bool l.succ)
  (hpt: pt_loc κ (π κ             moves)  i j ph)
  :     pt_loc κ (π κ (morf reflectIndex moves)) i j ph
  := by
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := reflect_preserves_nearby hpt.2
    rw [reflect_morf i, reflect_morf j] at R
    tauto



theorem rotate_pts'_atᵥ {l:ℕ} (k : Fin l.succ)
  (ph    : Mathlib.Vector Bool    l.succ)
  (moves : Mathlib.Vector (Fin 4) l):
  pts_at' κ k ph (π κ moves) ≤
  pts_at' κ k ph (π κ (σ ρ κ moves)) := by
  -- Completed March 6, 2024. So easy :)
  apply Finset.card_le_card
  intro i hi
  let Q :=  rotate_preserves_pt_loc' moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto



theorem reflect_pts'_atᵥ {l:ℕ} (k : Fin l.succ)
  (ph    : Mathlib.Vector Bool    l.succ)
  (moves : Mathlib.Vector (Fin 4) l):
  pts_at' κ k ph (π κ moves) ≤
  pts_at' κ k ph (π κ (σ reeu κ moves)) := by
  -- just like rotate_pts'_atᵥ
  apply Finset.card_le_card
  intro i hi
  let Q :=  reflect_preserves_pt_loc' moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto

theorem reflect_pts'_atᵥ_morf {l:ℕ} (k : Fin l.succ)
  (ph    : Mathlib.Vector Bool    l.succ)
  (moves : Mathlib.Vector (Fin 4) l):
  -- 3/8/24
  pts_at' κ k ph (π κ moves) ≤
  pts_at' κ k ph (π κ (morf reflectIndex moves)) := by
  apply Finset.card_le_card
  intro i hi
  let Q :=  reflect_preserves_pt_loc'_morf moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto


theorem rotate_pts_tot
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ)(moves : Mathlib.Vector (Fin 4) l):
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ (σ ρ κ moves))
  := by
    unfold pts_tot'
    apply Finset.sum_le_sum
    intro k
    intro
    exact rotate_pts'_atᵥ _ _ _



theorem reflect_pts_tot_morf
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ)(moves : Mathlib.Vector (Fin 4) l):
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ (morf reflectIndex moves))
  -- 3/8/24
  := by
    unfold pts_tot'
    apply Finset.sum_le_sum
    intro k
    intro
    exact reflect_pts'_atᵥ_morf _ _ _


theorem reflect_pts_tot
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ)(moves : Mathlib.Vector (Fin 4) l):
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ (σ reeu κ moves))
  := by
    unfold pts_tot'
    apply Finset.sum_le_sum
    intro k
    intro
    exact reflect_pts'_atᵥ _ _ _

  -- now we want to argue that we can always rotate to make moves start with 0, since:
theorem rotate_until_right : ∀ k : Fin 4,
  k = 0 ∨
  rotateIndex k = 0 ∨
  rotateIndex (rotateIndex k) = 0 ∨
  rotateIndex (rotateIndex (rotateIndex k)) = 0
| 0 => by left;rfl
| 1 => by right;right;left;rfl
| 2 => by right;right;right;rfl
| 3 => by right;left;rfl

theorem rotate_head
{l: ℕ}
(moves: Mathlib.Vector (Fin 4) (Nat.succ l))
: rotateIndex (Mathlib.Vector.head moves) = Mathlib.Vector.head (σ ρ κ moves)
:= by obtain ⟨a,⟨u,hu⟩⟩ := Mathlib.Vector.exists_eq_cons moves;rw [hu, Mathlib.Vector.head_cons];rfl

theorem rotate_headF
{l: ℕ}
(moves: Fin l.succ → (Fin 4))
: rotateIndex (moves 0) = (morfF rotateIndex moves) 0
:= rfl -- certainly easier with morfF !


theorem towards_orderlyish
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ.succ)(moves : Mathlib.Vector (Fin 4) l.succ):
  ∃ moves', moves'.get 0 = 0 ∧
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ moves')
  := by
  let m₀ := moves;let m₁ := (σ ρ κ m₀);let m₂ := (σ ρ κ m₁);let m₃ := (σ ρ κ m₂)
  cases rotate_until_right (moves.get 0) with
  | inl => exists m₀
  | inr h =>
    cases h with
    |inl h_1 =>
      exists m₁
      constructor
      · simp only [Mathlib.Vector.get_zero];
        rw [← h_1];
        simp only [Mathlib.Vector.get_zero];symm;
        simp only [Mathlib.Vector.get_zero] at h_1 ;
        exact rotate_head _
      · exact rotate_pts_tot ph m₀
    |inr h_1 =>
      cases h_1 with
      |inl h =>
        exists m₂
        constructor
        · -- inr.inr.inl.left
          rw [← h];simp only [Mathlib.Vector.get_zero]
          rw [rotate_head m₀, rotate_head m₁]
        · -- inr.inr.inl.right
          calc
            pts_tot' κ ph (π κ m₀) ≤ pts_tot' κ ph (π κ m₁):= rotate_pts_tot ph moves
            _                      ≤ _ := rotate_pts_tot ph m₁
      |inr h =>
        exists m₃;
        constructor;
        · rw [← h];simp only [Mathlib.Vector.get_zero]
          rw [rotate_head m₀,rotate_head m₁,rotate_head m₂]

        · calc
          pts_tot' κ ph (π κ m₀) ≤ pts_tot' κ ph (π κ m₁) := rotate_pts_tot ph m₀
          _                      ≤ pts_tot' κ ph (π κ m₂) := rotate_pts_tot ph m₁
          _                      ≤ _                      := rotate_pts_tot ph m₂

/--
We can always reflect to make the first entry after 0s (and 1s,
although they are ruled out by injectivity)
be a 2.-/
theorem rotate_until_right_reflect : ∀ k : Fin 4,
  k = 0 ∨
  k = 1 ∨
  k = 2 ∨
  reflectIndex k = 2
| 0 => by left;rfl
| 1 => by right;left;rfl
| 2 => by right;right;left;rfl
| 3 => by right;right;right;rfl


theorem towards_orderly
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ.succ)(moves : Mathlib.Vector (Fin 4) l.succ):
  ∃ moves', moves'.get 0 = 0 ∧
  (∀ j, (∀ i, i < j → moves'.get i = 0 ∨ moves'.get i = 1) → moves'.get j ≠ 3) ∧
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ moves')
  -- completed 3/8/24. Next we can point out that 0 can't be followed by 1 in injective fold.
  := by
  obtain ⟨moves₀,hmoves₀⟩ := towards_orderlyish ph moves
  by_cases h₃: (∀ j, (∀ i, i < j → moves₀.get i = 0 ∨ moves₀.get i = 1) → moves₀.get j ≠ 3)
  · -- pos
    exists moves₀;tauto
  · -- neg
    have : ∃ (j : Fin (l + 1)),
      (∀ i < j, Mathlib.Vector.get moves₀ i = 0 ∨ Mathlib.Vector.get moves₀ i = 1)
        ∧ Mathlib.Vector.get moves₀ j = 3
      := by
        contrapose h₃;
        simp only [ne_eq, not_forall, not_not, exists_prop, not_exists, not_and]
        intro x hx;contrapose h₃;
        simp only [not_exists, not_and, not_forall, not_not, exists_prop];
        simp only [not_not] at h₃ ;exists x
    obtain ⟨j,hj⟩ := this
    have : Mathlib.Vector.get (morf reflectIndex moves₀) j = 2 := by
      let Q := hj.2;unfold morf reflectIndex;simp only [Mathlib.Vector.get_map];rw [Q]
    exists (morf reflectIndex moves₀)
    constructor
    · let Q := hmoves₀.1;unfold reflectIndex morf; simp only [Mathlib.Vector.get_zero,
      Mathlib.Vector.head_map];
      simp only [Mathlib.Vector.get_zero] at Q ;rw [Q]

    · -- neg.intro.right
      constructor
      · -- neg.intr.right.left
        intro j₁ hj₁;by_cases h : j₁ < j;let Q := hj.1 j₁ h
        -- now it's easy using morf
        · cases Q with
          |inl h_1 =>
            intro hc;unfold morf at hc; simp only [Mathlib.Vector.get_map] at hc ;
            rw [h_1] at hc;revert hc;decide
          |inr h_1 =>
            intro hc;unfold morf at hc; simp only [Mathlib.Vector.get_map] at hc ;
            rw [h_1] at hc;revert hc;decide
        · by_cases he : j₁ = j
          · -- pos
            subst he;rw [this];symm;decide
          · -- neg
            have : j < j₁ ∨ j = j₁ ∨ j₁ < j := lt_trichotomy j j₁
            have : j < j₁ := by tauto
            let Q := hj.2
            let R := hj₁ j this
            cases R with
            |inl h_1 =>
              unfold morf at h_1; simp only [Mathlib.Vector.get_map] at h_1
              rw [Q] at h_1;exfalso;revert h_1;decide
            |inr h_1 =>
              unfold morf at h_1; simp only [Mathlib.Vector.get_map] at h_1
              rw [Q] at h_1;exfalso;revert h_1;decide
      · -- neg.intr.right.right
        calc
        _ ≤ pts_tot' κ ph (π κ moves₀) := hmoves₀.2
        _ ≤ _                          := reflect_pts_tot_morf ph moves₀


theorem path_morph_len
{l: ℕ}
(moves: Mathlib.Vector (Fin 4) l)
: (path rect (morph roeu rect moves.1)).1.length = l.succ
:= by
  -- this is just path_len and morph_len and should be generalized
  let morph_vec := (⟨morph roeu rect moves.1,morph_len _ _ _⟩
    : Mathlib.Vector (Fin 4) moves.1.length)
  let Q := path_len rect morph_vec
  rw [Q]
  simp

-- #eval orderly [0,2,2]
-- #eval orderly []
-- #eval orderly_and_nontrivial []

def pts_tot'_list_rev {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (fun h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, rfl⟩ : Mathlib.Vector Bool ph.length)
      ⟨(path go moves).1.reverse,(by
        rw [List.length_reverse]
        rw [← h,path_len'];rfl
      )⟩
    )
    (fun _ ↦ 0)

def pts_tot'_list_rev' {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (fun h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, by
        rw [← h]
      ⟩ : Mathlib.Vector Bool moves.length.succ)
      ⟨(path go moves).1.reverse,(by
        rw [List.length_reverse]
        simp_rw [h]
        rw [path_len' go _ moves]
        exact h
        rfl
      )⟩
    )
    (fun _ ↦ 0)


def pts_tot'_list {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (fun h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, rfl⟩ : Mathlib.Vector Bool ph.length)
      ⟨(path go moves).1,(by rw [← h,path_len'];rfl)⟩
    )
    (fun _ ↦ 0)

def InjectivePath {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : MonoPred b :=
{
  P := (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Mathlib.Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (fun moves : List (Fin b) ↦ pts_tot'_list go ph moves ≥ p ∧ orderly_and_nontrivial moves)
  -- this causes problems since "orderly" does not apply to arbitrary b
}

def InjectivePath₄ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : MonoPred 4 :=
{
  P := (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Mathlib.Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (fun moves : List (Fin 4) ↦ pts_tot'_list go ph moves ≥ p ∧ orderly_and_nontrivial moves)
}

def InjectivePath₅ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : MonoPred 4 :=
{
  P := (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Mathlib.Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (fun moves : List (Fin 4) ↦ pts_tot'_list_rev' go ph moves ≥ p
    ∧ orderly_and_nontrivial moves)
}

instance  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : DecidablePred (InjectivePath₅ go ph p).P := by
  unfold InjectivePath₅
  exact inferInstance

instance  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : DecidablePred (InjectivePath₅ go ph p).Q := by
  unfold InjectivePath₅
  exact inferInstance


-- Now use this to characterize. First add "M.Q":
theorem using_backtracking_verification₀ {k L p b:ℕ}
  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  (bound : k ≤ L.succ) (M:MonoPred b)
  [DecidablePred M.P] [DecidablePred M.Q]
  (w : Mathlib.Vector (Fin 4) (L.succ-k))
  (ph : Mathlib.Vector Bool L.succ.succ)
  [DecidablePred (InjectivePath₄ go ph.1 p).P]
  [DecidablePred (InjectivePath₄ go ph.1 p).Q]
  :
  Fintype.card {
    v : Mathlib.Vector (Fin 4) L.succ // ((InjectivePath₄ go ph.1 p).P v.1
    ∧ (InjectivePath₄ go ph.1 p).Q v.1) ∧ w.1 <:+ v.1
  }
  = num_by_backtracking (InjectivePath₄ go ph.1 p).P (InjectivePath₄ go ph.1 p).Q w
:= backtracking_verification bound (InjectivePath₄ go ph.1 p) w

theorem using_backtracking_verification₁ {k L p:ℕ}
  (bound : k ≤ L.succ) (M:MonoPred 4)
  [DecidablePred M.P] [DecidablePred M.Q]
  (w : Mathlib.Vector (Fin 4) (L.succ-k))
  (ph : Mathlib.Vector Bool L.succ.succ)
  [DecidablePred (InjectivePath₄ rect ph.1 p).P]
  [DecidablePred (InjectivePath₄ rect ph.1 p).Q]
  :
  Fintype.card {
    v : Mathlib.Vector (Fin 4) L.succ // ((InjectivePath₄ rect ph.1 p).P v.1
    ∧ (fun moves ↦ pts_tot'_list rect ph.1 moves ≥ p ∧ orderly_and_nontrivial moves) v.1)
      ∧ w.1 <:+ v.1
  }
  = num_by_backtracking
    (InjectivePath₄ rect ph.1 p).P
    (fun moves ↦ pts_tot'_list rect ph.1 moves ≥ p ∧ orderly_and_nontrivial moves) w
:= by
  let R := backtracking_verification bound (InjectivePath₄ rect ph.1 p) w
  simp only [ge_iff_le]
  have : (InjectivePath₄ rect (ph.1) p).Q
  = (fun moves => p ≤ pts_tot'_list rect (ph.1) moves ∧ orderly_and_nontrivial moves)
    := by
      rfl
  simp_rw [← this]
  rw [← R]
  apply Fintype.card_congr
  rfl



-- make these have "go" as a parameter:
def set_of_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (p:ℕ) (ph : Mathlib.Vector Bool l.succ.succ) :=
  those_with_suffix'
    (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)

def set_of_folds_achieving_pts_rev (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (p:ℕ) (ph : Mathlib.Vector Bool l.succ.succ) :=
  those_with_suffix'
    (fun moves : List (Fin 4) ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves : List (Fin 4) ↦ pts_tot'_list_rev go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' 4 l.succ) -- (there are 7 moves for a polypeptide of length 8)

def goodFolds (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (p:ℕ) (ph : Mathlib.Vector Bool l.succ.succ) :=
-- really, this should be defined in direct terms and then prove that it equals those_with_suffix'
  those_with_suffix'
    (fun moves : List (Fin 4) ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves : List (Fin 4) ↦ pts_tot'_list_rev' go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' 4 l.succ) -- (there are 7 moves for a polypeptide of length 8)

def equifoldable (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph₀ ph₁ : Mathlib.Vector Bool l.succ.succ) (p:ℕ) :=
  goodFolds go p ph₀ = goodFolds go p ph₁

infix:50 " ∼₃ " => (fun ph₀ ph₁ ↦ equifoldable rect₃ ph₀ ph₁ 2)
infix:50 " ∼ "  => (fun ph₀ ph₁ ↦ equifoldable rect  ph₀ ph₁ 2)


instance (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ}  (p:ℕ) : Equivalence (fun (ph₀ ph₁ : Mathlib.Vector Bool l.succ.succ) ↦
    equifoldable go ph₀ ph₁ p)
    := {
      trans := by
        unfold equifoldable;intro _ _ _ h₀₁ h₁₂;exact Eq.trans h₀₁ h₁₂
      refl := by
        unfold equifoldable;intro _;rfl
      symm := by
        unfold equifoldable;intro _ _ h;exact h.symm
    }

instance (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph₀ ph₁ : Mathlib.Vector Bool l.succ.succ) (p:ℕ) : Decidable
    (equifoldable go ph₀ ph₁ p) := by
  unfold equifoldable
  unfold goodFolds
  unfold those_with_suffix'
  simp only [ge_iff_le, Nat.zero_eq, Nat.sub_zero]
  exact inferInstance


-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[false,false,true,false,false,true,false,true],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[true,true,true,true,true,true,true,true],rfl⟩

def o := false
def l := true

-- Words of length 6 that have non-∅ values:
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,o,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,o,l,l,l,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,o,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,o,l,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,l,l,l],rfl⟩
-- {[0, 2, 1, 2, 0], [0, 0, 2, 1, 1]}

def toSet
  {l:ℕ} (ph : Mathlib.Vector Bool l) :=
  (Finset.filter (fun i ↦ ph.get i) (Finset.univ : Finset (Fin l)))

/-- This result from March 29, 2024 proves the obvious fact that
  more H amino acids leads to more points. -/
theorem toSet_dominates {α β:Type} [Fintype β] [OfNat α 0] [DecidableEq α]
    (go: β → α→α) {l:ℕ} (ph₀ ph₁ : Mathlib.Vector Bool l.succ) (hsub: toSet ph₀ ⊆ toSet ph₁) :
    HP go ph₀ ≤ HP go ph₁ := by
  apply Nat.find_mono
  intro n h moves h_inj
  let h₁ := h moves h_inj
  unfold pts_tot' at *
  have h₀ : (Finset.sum Finset.univ fun i =>
    pts_at' go i ph₀ ⟨ (path go moves.1).1, by rw [path_len]⟩)
          ≤ (Finset.sum Finset.univ fun i =>
    pts_at' go i ph₁ ⟨ (path go moves.1).1, by rw [path_len]⟩) := by
    apply Finset.sum_le_sum
    intro i; intro
    apply Finset.card_le_card
    intro j hj
    unfold pt_loc at *
    simp only [Finset.mem_univ, Bool.and_eq_true, decide_eq_true_eq,
      Finset.mem_filter, true_and] at *
    unfold toSet at hsub

    have h_ : j ∈ Finset.filter (fun i' => Mathlib.Vector.get ph₀ i' = true) Finset.univ
            ∧ i ∈ Finset.filter (fun i' => Mathlib.Vector.get ph₀ i' = true) Finset.univ := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and];exact hj.1.1
    let Q := And.intro (hsub h_.1) (hsub h_.2)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Q
    tauto
  exact LE.le.trans h₀ h₁

theorem more_pts_of_subset (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l:ℕ} {ph₀ ph₁ : Mathlib.Vector Bool l.succ.succ}
  (w: Gap 4 (Nat.succ l) 0)
              (hsub: toSet ph₀       ⊆ toSet            ph₁)
 :  pts_tot'_list_rev' go       ph₀.1 w.1 ≤ pts_tot'_list_rev' go ph₁.1 w.1 := by
      unfold pts_tot'_list_rev'
      have : Nat.succ (List.length w.1) = List.length ph₀.1 := by rw [w.2, ph₀.2];rfl
      rw [dif_pos this]
      have : Nat.succ (List.length w.1) = List.length ph₁.1 := by rw [w.2, ph₁.2];rfl
      rw [dif_pos this]
      apply Finset.sum_le_sum;   intro i _; unfold pts_at'
      apply Finset.card_le_card; intro j _; unfold pt_loc at *
      simp only [Nat.sub_zero, Finset.mem_univ, Bool.and_eq_true, decide_eq_true_eq,
        Finset.mem_filter, true_and] at *
      have hi: i.1 < l.succ.succ := by let A := i.2;simp_rw [w.2] at A;exact A
      have hj: j.1 < l.succ.succ := by let A := j.2;simp_rw [w.2] at A;exact A
      have hi': ⟨i.1,hi⟩ ∈ Finset.filter (fun i => Mathlib.Vector.get ph₀ i = true)
        Finset.univ := by
        simp only [Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      have hj': ⟨j.1,hj⟩ ∈ Finset.filter (fun i => Mathlib.Vector.get ph₀ i = true)
        Finset.univ := by
        simp only [Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      unfold toSet at hsub
      let hsubj := hsub hj'; simp only [Nat.sub_zero, Finset.mem_filter,
        Finset.mem_univ, true_and] at hsubj ;
      let hsubi := hsub hi'; simp only [Nat.sub_zero, Finset.mem_filter,
        Finset.mem_univ, true_and] at hsubi ;
      tauto


def meet {l:ℕ} (ph₀ ph₁ : Mathlib.Vector Bool l) : Mathlib.Vector Bool l :=
  Mathlib.Vector.ofFn (fun i ↦ ph₀.get i ∧ ph₁.get i)

infix:50 " ⊓ " => meet


lemma meet_get {l :ℕ} {ph₀ ph₁ : Mathlib.Vector Bool l} {i:Fin l}
: (ph₀ ⊓ ph₁).get i = (ph₀.get i ∧ ph₁.get i) := by
  have : (meet ph₀ ph₁).get i = (ph₀.get i && ph₁.get i) := by
    unfold meet
    simp
  rw [this]
  simp

theorem meet_basic₀ {l :ℕ} {ph₀ ph₁ : Mathlib.Vector Bool l}
  : toSet (ph₀ ⊓ ph₁) ⊆ toSet ph₀ := by
  intro i hi;unfold toSet at *;simp only [Finset.mem_filter, Finset.mem_univ,
    true_and] at *;rw [meet_get] at hi;tauto


theorem meet_basic₁
  {l :ℕ} {ph₀ ph₁ : Mathlib.Vector Bool l}
  : toSet (ph₀ ⊓ ph₁) ⊆ toSet ph₁ := by
  -- verbatim the same proof
  intro i hi;unfold toSet at *;simp only [Finset.mem_filter, Finset.mem_univ,
    true_and] at *;rw [meet_get] at hi;tauto


theorem goodFolds_monotone
  (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l :ℕ} (ph₀ ph₁ : Mathlib.Vector Bool l.succ.succ)
                      (hsub: toSet ph₀ ⊆ toSet ph₁) (p:ℕ)
 : goodFolds go p ph₀ ⊆ goodFolds go p ph₁ := by

  let M₀ := InjectivePath₅ go ph₀.1 p
  let M₁ := InjectivePath₅ go ph₁.1 p
  let u := (Gap_nil' 4 (Nat.succ l))
  have verify₀:
    those_with_suffix' M₀.P M₀.Q u =
      Finset.filter (fun v  ↦ M₀.P v.1 ∧ M₀.Q v.1 ∧ u.1 <:+ v.1) Finset.univ
    := verify_those_with_suffix (le_refl _) u -- nice to be able to use that!
  have verify₁:
    those_with_suffix' M₁.P M₁.Q u = Finset.filter
      (fun v  ↦ M₁.P v.1 ∧ M₁.Q v.1 ∧ u.1 <:+ v.1) Finset.univ
    := verify_those_with_suffix (le_refl _) u
  simp only [Nat.succ_eq_add_one]
  -- simp only [Nat.sub_zero, Finset.filter_congr_decidable] at verify₀ verify₁
  unfold InjectivePath₅ at verify₀ verify₁
  -- simp only [ge_iff_le, Finset.filter_congr_decidable] at verify₀ verify₁

  unfold goodFolds
  simp only [Nat.succ_eq_add_one, ge_iff_le]
  intro w hw₀
  simp only [Nat.succ_eq_add_one, Nat.sub_zero] at verify₀

  change (those_with_suffix'
    (InjectivePath₅ go (ph₀.1) p).P
    (InjectivePath₅ go (ph₀.1) p).Q u
  = Finset.filter (fun v : Gap 4 l.succ 0 ↦ M₀.P v.1 ∧ M₀.Q v.1 ∧ u.1 <:+ v.1) Finset.univ)
    at verify₀
  unfold InjectivePath₅ at verify₀
  simp at verify₀
  rw [verify₀] at hw₀

  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₀
  have hp: p ≤ pts_tot'_list_rev' go ph₁.1 w.1 := LE.le.trans hw₀.2.1.1
    (more_pts_of_subset go w hsub)

  show  w ∈ those_with_suffix' M₁.P M₁.Q u
  rw [verify₁]
  simp only [Nat.succ_eq_add_one, Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · tauto
  constructor
  · show (InjectivePath₅ go (ph₁.1) p).Q w.1
    have T := hw₀.2.1
    change ((InjectivePath₅ go (ph₀.1) p).Q w.1) at T
    simp
    unfold InjectivePath₅
    unfold InjectivePath₅ at T
    tauto
  · tauto

/-

For the model `rect`, equifoldability is coNP-complete.
It is in coNP since if `x` and `y` are not equifoldable it suffices to produce a fold by which
`x` achieves `k` points and `y` does not.
It is coNP-hard since `x∼∅ [k]` iff `P(x)<k`.
-/

theorem convex_equifoldable {l :ℕ} (ph₀ ph₁ ph₂: Mathlib.Vector Bool l.succ.succ)
(h₀₁: toSet ph₀ ⊆ toSet ph₁)
                 (h₁₂: toSet ph₁ ⊆ toSet ph₂)
(h₀₂: ph₀ ∼ ph₂) : ph₀ ∼ ph₁ := by
  let Q₀₁ := goodFolds_monotone rect ph₀ ph₁ h₀₁ 2
  let Q₁₂ := goodFolds_monotone rect ph₁ ph₂ h₁₂ 2
  rw [← h₀₂] at Q₁₂
  apply Finset.Subset.antisymm;tauto;tauto

-- theorem monotonicity_of_sim {k l :ℕ} (x₀ y₀: Mathlib.Vector Bool l.succ.succ)
--  (x₁ y₁: Mathlib.Vector Bool k.succ.succ)
-- (h: Mathlib.Vector.append x₀ x₁ ∼ Mathlib.Vector.append y₀ y₁) : x₀ ∼ y₀ := by
--   -- not true, due to Stecher type phenomena:
--   -- let x be a Stecher string, let x' an all-false string of the same length, and
-- consider x++[1] and x'++[1]
--   sorry



def goodPairs -- points_tot = Fin.card points_loc
  (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} (fold : Mathlib.Vector (ℤ×ℤ) l) (ph : Mathlib.Vector Bool l)

  :=
Finset.filter
  (fun ik : (Fin l) × (Fin l) ↦ ((pt_loc go fold ik.1 ik.2 ph): Prop))
  (Finset.univ)

/-- Note that this is not true for ∪ and join. -/
theorem goodPairs_meet
  (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} (ph₀ ph₁ : Mathlib.Vector Bool l.succ)
  (fold : Mathlib.Vector (ℤ×ℤ) (Nat.succ l))
 : goodPairs go fold (ph₀ ⊓ ph₁) =
   goodPairs go fold ph₀ ∩
   goodPairs go fold ph₁ := by
    -- let f := fun ph ↦ goodPairs go fold ph
    -- show f (meet ph₀ ph₁) = f ph₀ ∩ f ph₁
    apply Finset.ext
    intro ij
    constructor
    · -- mp
      intro hij
      rw [Finset.mem_inter]
      unfold goodPairs at *
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
      unfold pt_loc at *
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      have hi: ij.1 ∈ Finset.filter (fun i => Mathlib.Vector.get (meet ph₀ ph₁) i = true)
        Finset.univ
        := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij.1.1.1
      have hj: ij.2 ∈ Finset.filter (fun i => Mathlib.Vector.get (meet ph₀ ph₁) i = true)
        Finset.univ
        := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij.1.1.2
      let Si₀ := meet_basic₀ hi; let Si₁ := meet_basic₁ hi
      let Sj₀ := meet_basic₀ hj; let Sj₁ := meet_basic₁ hj
      unfold toSet at Si₀ Si₁ Sj₀ Sj₁
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Si₀ Si₁ Sj₀ Sj₁
      tauto
    · -- mpr
      simp only [Finset.mem_inter, and_imp]
      intro h₀ h₁
      unfold goodPairs pt_loc at *
      simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at *
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



def num_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ.succ) (p:ℕ) : ℕ :=
  num_by_backtracking
    (fun moves ↦ Function.Injective (fun i ↦ (path go moves).get i))
    (fun moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)


def can_achieve_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Mathlib.Vector Bool l.succ.succ) (p:ℕ): Prop :=
  set_of_folds_achieving_pts go p ph ≠ ∅

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

def stecher1 : Prop :=
  those_with_suffix'
    (fun w ↦ Function.Injective (fun i ↦ (path rect w).get i))
    (fun w ↦ pts_tot'_list rect  x w > 2 ∧ orderly_and_nontrivial w)
    (Gap_nil' 4 7) -- (there are 7 moves for a polypeptide of length 8)
  = {⟨[0, 2, 2, 1, 1, 3, 0],rfl⟩} --{⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}
-- #eval [0,2,1].reverse.getLast?
-- #eval first_nonzero_entry [0,2,1]
-- #eval orderly_and_nontrivial [0,2,1]
-- #eval   (those_with_suffix'
--     (fun w ↦ Function.Injective (fun i ↦ (path quad w).get i))
--     (fun w ↦ pts_tot'_list rect  ([true,false,false,true]) w > 0 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 3)) -- fixed February 20, 2024

-- #eval   (those_with_suffix'
--     (fun w ↦ Function.Injective (fun i ↦ (path quad w).get i))
--     (fun w ↦ pts_tot'_list rect  (List.replicate L.succ true) w ≥ 5 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 L)) -- fixed February 20, 2024

-- #eval HP rect ⟨[true],rfl⟩
-- #eval HP rect ⟨List.replicate 9 true,rfl⟩ -- 4
-- #eval HP rect ⟨List.replicate L.succ true,rfl⟩ -- 4
-- #eval HP hex ⟨List.replicate 3 true,rfl⟩ -- amazing

-- #eval (myvec 4 7).length
-- #eval stecher1

def stecher2 : Prop :=
those_with_suffix'
    (fun w ↦ Function.Injective (fun i ↦ (path rect w).get i))
    (
      fun w ↦ pts_tot'_list rect  (x ++ [false]) w > 2
        ∧ orderly_and_nontrivial w
    )
    (Gap_nil' 4 8) = ∅

#eval (those_with_suffix'
    (fun w ↦ Function.Injective (fun i ↦ (path rect w).get i))
    (fun w ↦ pts_tot'_list rect  x w > 2 ∧ orderly_and_nontrivial w)
    (Gap_nil' 4 7))

#eval (those_with_suffix'
    (fun w ↦ Function.Injective (fun i ↦ w.get i))
    (fun w ↦ w = [0,0])
    (Gap_nil' 4 2))

def stecher_conjecture_counterexample : Prop := stecher1  ∧ stecher2

instance : Decidable stecher2 := by unfold stecher2; apply decEq
instance : Decidable stecher_conjecture_counterexample := by
  unfold stecher_conjecture_counterexample; unfold stecher1; unfold stecher2; exact instDecidableAnd

#eval stecher1
-- #eval stecher2
#reduce stecher_conjecture_counterexample

end Backtracking_usage
