/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Batteries.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.BigOperators.Group.Finset


/-!
# Hydrophobic-polar protein folding model: basics

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
`Fin n → α` instead of `Vector α n`

-/

open Finset Mathlib

/-- `∑₀^(n-1) (k-1) = (n-1)(n-2)/2`. This uses the Lean convention `0-1=0`. -/
lemma sum_pred₀ (n:ℕ) : Finset.sum (range n) (fun k ↦ k-1) = (n-1)*(n-2)/2 := by
  apply sum_range_induction
  · rfl
  · intro n
    simp only [add_tsub_cancel_right, Nat.succ_sub_succ_eq_sub]
    suffices  (n * (n - 1) / 2)*2 = ((n - 1) * (n - 2) / 2 + (n - 1))*2 by
      exact Nat.mul_right_cancel (Nat.zero_lt_two) this
    rw [
      Nat.add_mul,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n),
      Nat.div_two_mul_two_of_even (by exact Nat.even_mul_pred_self (n-1)),
      ← Nat.mul_add
    ]
    cases n with
    | zero => simp
    | succ n_1 =>
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      cases n_1
      · simp
      · simp only [add_tsub_cancel_right]
        ring

/-- `∑ⁿ₀ (k-1) = n (n-1) / 2`. This uses the Lean convention `0-1=0`. -/
 theorem sum_pred (n:ℕ) : Finset.sum (range n.succ) (fun k ↦ k-1) = n*(n-1)/2 :=
  sum_pred₀ n.succ

section Defining_the_protein_folding_moves

/-- The original protein folding model introduced by Ken Dill in 1985. -/
def quad₃ : Fin 6 → ℤ×ℤ×ℤ → ℤ×ℤ×ℤ
  | 0 => (· + ( 1, 0, 0))
  | 1 => (· + (-1, 0, 0))
  | 2 => (· + ( 0, 1, 0))
  | 3 => (· + ( 0,-1, 0))
  | 4 => (· + ( 0, 0, 1))
  | 5 => (· + ( 0, 0,-1))

/-- The convention is that `p` is plus, `m` is minus, and `s` is stationary. -/
def pp : ℤ×ℤ → ℤ×ℤ := (· + ( 1, 1))
/-- When using keys WASD for navigation, this is D. -/
def go_D : ℤ×ℤ → ℤ×ℤ := (· + ( 1, 0))
/-- The convention is that `p` is plus, `m` is minus, and `s` is stationary. -/
def sp : ℤ×ℤ → ℤ×ℤ := (· + ( 0, 1))

/-- The convention is that `p` is plus, `m` is minus, and `s` is stationary. -/
def mm : ℤ×ℤ → ℤ×ℤ := (· + (-1,-1))
/-- When using keys WASD for navigation, this is A. -/
def go_A : ℤ×ℤ → ℤ×ℤ := (· + (-1, 0))
/-- The convention is that `p` is plus, `m` is minus, and `s` is stationary. -/
def sm : ℤ×ℤ → ℤ×ℤ := (· + ( 0,-1))

/-- The convention is that `p` is plus, `m` is minus, and `s` is stationary. -/
def pm : ℤ×ℤ → ℤ×ℤ := (· + ( 1,-1))
/-- The convention is that `p` is plus, `m` is minus, and `s` is stationary. -/
def mp : ℤ×ℤ → ℤ×ℤ := (· + (-1, 1))

/-- When using keys WAZXDE for hexagonal navigation, this is X. -/
def go_X : ℤ×ℤ → ℤ×ℤ := fun x ↦ ite (Even x.2) (sp x) (pp x)
/-- When using keys WAZXDE for hexagonal navigation, this is W. -/
def go_W : ℤ×ℤ → ℤ×ℤ := fun x ↦ ite (Even x.2) (mm x) (sm x)

/-- When using keys WAZXDE for hexagonal navigation, this is Z. -/
def go_Z : ℤ×ℤ → ℤ×ℤ := fun x ↦ ite (Even x.2) (mp x) (sp x)
/-- When using keys WAZXDE for hexagonal navigation, this is E. -/
def go_E : ℤ×ℤ → ℤ×ℤ := fun x ↦ ite (Even x.2) (sm x) (pm x)

/-- The four directions, horizontal and vertical. -/
def rectMap (a : Fin 4) : ℤ×ℤ := match a with
  | 0 => (1,0)
  | 1 => (-1,0)
  | 2 => (0,1)
  | 3 => (0,-1)

/-- Basically a fintype for the directions: left, right, up.-/
def rect₃Map (a : Fin 3) : ℤ×ℤ := match a with
  | 0 => (1,0)
  | 1 => (-1,0)
  | 2 => (0,1)

/-- Three directions: left, right, up. Allows for polynomial-time optimal folding. -/
def rect₃ (a : Fin 3) (x: ℤ×ℤ) : ℤ×ℤ := x + rect₃Map a
/-- The four directions as a map. -/
def rect (a : Fin 4) (x: ℤ×ℤ) : ℤ×ℤ := x + rectMap a

/-- . -/
abbrev κ := rect


/-- move_hex represents the degree-6 hexagonal/triangular lattice,
 although that in itself requires checking.
This representation was designed to make the y-axis vertical to fit with a computer game.
def move_hex : Fin 6 → ℤ×ℤ → ℤ×ℤ
| 0 => go_D
| 1 => go_A
| 2 => go_X
| 3 => go_W
| 4 => go_E
| 5 => go_Z
#eval move_hex 0 (0,0)
#eval move_hex 5 (1,0)
If computer games are not to be used we can use this simpler implementation.-/
def hexMap (a : Fin 6) : ℤ×ℤ := match a with
  | 0 => (1,0) | 1 => (-1,0) | 2 => (0,1) | 3 => (0,-1)| 4 => (1,1)  | 5 => (-1,-1)

/-- A limited move set for `hexMap`. -/
def hex₄Map (a : Fin 4) : ℤ×ℤ := match a with
  | 0 => (1,0) | 1 => (-1,0) | 2 => (0,1) | 3 => (1,1)

/-- `hexMap` as a function on the plane. -/
def hex (a : Fin 6) (x: ℤ×ℤ) : ℤ×ℤ := x + hexMap a

/-- `hex₄Map` as a function on the plane. -/
def hex₄ (a : Fin 4) (x: ℤ×ℤ) : ℤ×ℤ := x + hex₄Map a

/-- `hexMap` is injective. -/
theorem hexMap_injective : Function.Injective hexMap := by decide

/-- In the brick wall lattice, this function goes in whichever vertical direction is available. -/
def go_WS : ℤ×ℤ → ℤ×ℤ := fun x ↦ ite (Even (x.1+x.2)) (sp x) (sm x)

/-- The available moves in brick wall lattice folding. -/
def tri : Fin 3 → ℤ×ℤ → ℤ×ℤ
  | 0 => go_D
  | 1 => go_A
  | 2 => go_WS

end Defining_the_protein_folding_moves

section Setting_up_point_earned

/-- Casting from `Fin k` to `Fin l`, where `k < l`. -/
def Fin_trans {l : ℕ} {k: Fin l} (i : Fin k): Fin l :=
  ⟨i.1, Fin.val_lt_of_le _ (Fin.is_le')⟩

/-- Casting from `Fin k.pred` to `Fin l`, where `k < l`. -/
def Fin_trans_pred {l : ℕ} {k: Fin l} (i : Fin k.1.pred): Fin l :=
  ⟨i.1, Fin.val_lt_of_le i <| Nat.pred_le_iff.mpr <| Nat.le_step <| Fin.is_le'⟩

/-- Two points are nearby if they are one move apart. -/
def nearby {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
    (p q : α) : Bool := ∃ a : β, q = go a p

/-- The (H-P reduced) amino acid sequence `phobic` has a match at locations
  `i`, `j`, according to the fold `fold`. -/
def pt_loc {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
    {l : ℕ} (fold : Vector α l) (i j : Fin l) (phobic : Vector Bool l) : Bool :=
  phobic.get i && phobic.get j && i.1.succ < j.1 && nearby go (fold.get i) (fold.get j)

/-- The number of matches achieved with the fold `fold` for the amino acid sequence `ph`. -/
def pts_at' {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
    {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  card (filter (fun i : Fin l ↦ (pt_loc go fold i k ph)) univ)

/-

  ## Two ways of counting points

  We prove that `pts_at  = pts_at'`,
  where `pts_at'` is more convenient type-theoretically, but
  `pts_at` is more useful for proving a certain bound.
-/


/-- φ maps φ⁻¹' P to P. -/
def map_predicate {β α : Type}[Fintype β] [Fintype α] (P : β → Bool)
    (φ : α → β) [DecidablePred fun i : β => P i] :
    filter (fun i : α  ↦ P (φ i)) univ →
    filter (fun i : β ↦ P    i  ) univ :=
  fun i => ⟨φ i.1, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp i.2).2⟩⟩

/-- Cast a member of P to a member of P. -/
def embed_pred {l:ℕ} (k : Fin l) (P : Fin l → Fin l → Bool) [DecidablePred fun i : Fin l => P i k] :
    filter (fun i : Fin k.1.pred ↦ P (Fin_trans_pred i) k) univ →
    filter (fun i : Fin l        ↦ P                 i  k) univ :=
  map_predicate (fun i => P i k) Fin_trans_pred

/-- `embed_pred` casting is injective. -/
lemma embed_pred_inj  {l:ℕ} (k : Fin l) (P : Fin l → Fin l → Bool)
    [DecidablePred fun i : Fin l => P i k] :
    Function.Injective (embed_pred k P) :=
  fun x y hxy => by
    unfold embed_pred Fin_trans_pred at hxy
    simp only [Nat.pred_eq_sub_one, Subtype.mk.injEq, Fin.mk.injEq] at hxy
    exact Subtype.eq <| Fin.eq_of_val_eq (by
      unfold map_predicate at hxy
      simp only [Subtype.mk.injEq,
      Fin.mk.injEq] at hxy
      exact hxy
    )

/-- `embed_pred` casting is surjective. -/
lemma embed_pred_surj {l:ℕ} (k : Fin l) (P : Fin l → Fin l → Bool)
    [DecidablePred fun i : Fin l => P i k]
    (h: ∀ {x y : Fin l}, P x y → x.1 < y.1.pred) :
    Function.Surjective (embed_pred k P) := by
  intro y
  unfold embed_pred Fin_trans_pred
  simp only [Nat.pred_eq_sub_one, Subtype.exists, mem_filter, mem_univ, true_and]
  use ⟨y.1.1, h (mem_filter.mp y.2).2⟩
  use (mem_filter.mp y.2).2
  unfold map_predicate;simp

/-- `embed_pred` casting is bijective. -/
lemma embed_pred_bij {l:ℕ} (k : Fin l) {P : Fin l → Fin l → Bool}
    [DecidablePred fun i : Fin l => P i k] (h: ∀ {x y : Fin l}, P x y → x.1 < y.1.pred) :
    Function.Bijective (embed_pred k P) :=
  ⟨embed_pred_inj k P, embed_pred_surj k P h⟩



/-- The number of `P`'s is the same if we count beyond the greatest element of `P`. -/
theorem change_type_card_general'' {l:ℕ} (k : Fin l) (P : Fin l → Fin l → Bool)
    [DecidablePred fun i : Fin l => P i k] (h: ∀ {x y : Fin l}, P x y → x.1.succ < y.1) :
    Fintype.card (filter (fun i : Fin l ↦ P i k) univ) =
    Fintype.card (filter (fun i : Fin k.1.pred ↦ (P (Fin_trans_pred i) k)) univ) :=
  .symm <| Fintype.card_of_bijective <| embed_pred_bij k
    <| fun hxy => Nat.lt_pred_iff_succ_lt.mpr <| h hxy

/-- The number of points is the same if we count beyond the last point. -/
theorem change_type_card_improved  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
    [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
    Fintype.card
      (filter (fun i : Fin l        ↦ (pt_loc go fold                 i  k ph)) univ) =
    Fintype.card
      (filter (fun i : Fin k.1.pred ↦ (pt_loc go fold (Fin_trans_pred i) k ph)) univ) := by
  let P := (fun i k : Fin l ↦ ((pt_loc go fold i k ph) : Bool))
  have h : ∀ {x y}, P x y → x.1.succ < y.1 := by
    intro i k hP
    have : i.1.succ < k.1 := by
      have : P i k ↔ pt_loc go fold i k ph := by tauto
      unfold pt_loc at this
      rw [hP] at this
      simp only [Bool.and_eq_true, decide_eq_true_eq, true_iff] at this
      tauto
    exact this
  exact change_type_card_general'' k P h
/-- Helper function for `path_at`. -/
def path_aux {α β: Type} {l: ℕ} (go: β → α → α) (hd: β) (tl: Vector α l.succ) :
    Vector α l.succ.succ := ⟨(go hd tl.head) :: tl.1, by simp⟩
/-- Inductively defined path, starting at `base` (the origin, say),
  and proceeding through all `moves` according to the rules of `go`. -/
def path_at {α:Type} {β : Type} (base:α) (go : β → α → α) :
    (moves : List β) → Vector α moves.length.succ
  | [] => ⟨[base], rfl⟩
  | head :: tail => path_aux go head (path_at base go tail)

/-- Using OfNat here since ℤ×ℤ and ℤ×ℤ×ℤ have a natural notion of base point or zero.-/
def path {α:Type} [Zero α] {β : Type} (go : β → α → α) :
    (moves : List β) → Vector α moves.length.succ := path_at 0 go

end Setting_up_point_earned

section Embedding_one_protein_folding_model_into_another

/-- The move set `go₁` can simulate the move set `go₀`. -/
def embeds_in {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α) :=
  ∀ i : Fin b₀, ∀ x : α, ∃ j : Fin b₁, go₀ i x = go₁ j x

/-- The move set `go₁` simulates the move set `go₀` via the map `f`. -/
def is_embedding {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
    (f : Fin b₀ → α → Fin b₁) :=
  ∀ i : Fin b₀, ∀ x : α, go₀ i x = go₁ (f i x) x

/-- Like `embeds_in`, but with an explicit Skolem function. -/
def embeds_in_strongly {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α) :=
  ∃ f : Fin b₀ → α → Fin b₁, is_embedding go₀ go₁ f

/-- . -/
infix:50 " ≼ " => embeds_in_strongly

/-- Embedding of move sets is transitive. -/
theorem embeds_in_strongly_transitive {α:Type} {b₀ b₁ b₂: ℕ}
    (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α) (go₂ : Fin b₂ → α → α) :
    go₀ ≼ go₁ → go₁ ≼ go₂ → go₀ ≼ go₂ := by
  intro h₀₁ h₁₂
  unfold embeds_in_strongly is_embedding at *
  obtain ⟨f₀₁,hf₀₁⟩ := h₀₁
  obtain ⟨f₁₂,hf₁₂⟩ := h₁₂
  exists (fun i x ↦ f₁₂ (f₀₁ i x) x)
  intro i x
  rw [hf₀₁,hf₁₂]

/-- Embedding of move sets is reflexive. -/
theorem embeds_in_strongly_reflexive {α:Type} {b: ℕ}
    (go : Fin b → α → α) : go ≼ go := by
  unfold embeds_in_strongly is_embedding at *
  exists (fun i _ ↦ i)
  intro i x
  simp

/-- Embedding using a Skolem function implies ordinary embedding. -/
theorem embeds_of_strongly_embeds {α:Type} {b₀ b₁ : ℕ} {go₀ : Fin b₀ → α → α}
    {go₁ : Fin b₁ → α → α} (h_embed: go₀ ≼ go₁):
    embeds_in go₀ go₁ := by
  obtain ⟨f,hf⟩ := h_embed; intro i x; exists f i x; exact hf i x

/-- For tri we can only assert a pointwise version of embed_models:
  It follows from tri_rect_embedding that any sequence of moves under tri
  generates a sequence in ℤ×ℤ that can also be generated using quad.
-/
def tri_rect_embedding : Fin 3 → ℤ×ℤ → Fin 4
  | 0 => fun _ ↦ 0
  | 1 => fun _ ↦ 1
  | 2 => fun x ↦ ite (Even (x.1 + x.2)) 2 3

/-
3n      4n        6n    n(n-1)/2
P_tri   P_rect    P_hex
-/

/-
This is almost an embedding of presented group actions
sending generators to generators, but not quite.
In fact, the map φ that transports a point vertically
across the triple point in the brick wall lattice
is not a translation! But there are two translations (up and down) such that
φ always agree with one or the other.

The map φ has order two and all its orbits have cardinality two.
-/

/-- Hexagonal move set extend rectangular. -/
def rect_hex_embedding : Fin 4 → ℤ×ℤ → Fin 6
  | a => fun _ ↦ a

/-- Rectangular move set extends limited rectangular. -/
def rect₃_rect_embedding : Fin 3 → ℤ×ℤ → Fin 4
  | a => fun _ ↦ a


/-- `rect₃_rect_embedding` works as advertised. -/
theorem rect₃_rect_embedding_is_embedding :
    ∀ i : Fin 3, ∀ x : ℤ×ℤ, rect₃ i x = rect (rect₃_rect_embedding i x) x
  | 0 => fun _ ↦ rfl
  | 1 => fun _ ↦ rfl
  | 2 => fun _ ↦ rfl

/-- `rect_hex_embedding` works as advertised. -/
theorem rect_hex_embedding_is_embedding :
    ∀ i : Fin 4, ∀ x : ℤ×ℤ, rect i x = hex (rect_hex_embedding i x) x
  | 0 => fun _ ↦ rfl
  | 1 => fun _ ↦ rfl
  | 2 => fun _ ↦ rfl
  | 3 => fun _ ↦ rfl

/-- `tri_rect_embedding` works as advertised. -/
theorem tri_rect_embedding_is_embedding :
    ∀ i : Fin 3, ∀ x : ℤ×ℤ, tri i x = rect (tri_rect_embedding i x) x
  | 0 => fun x ↦ rfl
  | 1 => fun x ↦ rfl
  | 2 => fun x ↦ by
    by_cases h: Even (x.1+x.2)
    · show (if Even (x.1 + x.2) then sp x else sm x)  = rect (tri_rect_embedding 2 x) x
      rw [if_pos h]
      have : tri_rect_embedding 2 x = 2 := by
        show (if Even (x.1 + x.2) then 2 else 3) = 2;
        simp only [ite_eq_left_iff]; tauto
      rw [this]
      rfl
    · have : tri_rect_embedding 2 x = 3 := by
        show (if Even (x.1 + x.2) then 2 else 3) = 3;
        simp only [ite_eq_right_iff]; tauto
      rw [this]
      show (if Even (x.1 + x.2) then sp x else sm x) = sm x
      simp only [ite_eq_right_iff]
      tauto

end Embedding_one_protein_folding_model_into_another

section Left_and_right_injectivity

/-- A function of two variables is *left injective* if it is injective in its first argument. -/
def left_injective {α:Type} {β γ: Type} (go : β → α → γ) :=
  ∀ a, Function.Injective (fun b ↦ go b a)

/-- A function of two variables is *right injective* if it is injective in its second argument. -/
def right_injective {α:Type} {β γ: Type} (go : β → α → γ) :=
  ∀ b, Function.Injective (fun a ↦ go b a)

/-- `rect₃_rect_embedding` is left injective. -/
theorem rect₃_rect_embedding_left_injective :
    left_injective rect₃_rect_embedding := by
  unfold left_injective at *
  intro x a b hab
  simp only at *
  unfold rect₃_rect_embedding at hab
  simp only [Fin.coe_eq_castSucc] at hab
  exact Fin.castSucc_inj.mp hab

/-- `tri_rect_embedding` is left injective. -/
theorem tri_rect_embedding_left_injective :
    left_injective tri_rect_embedding := by
  unfold left_injective at *
  intro x
  intro a b hab
  simp only at *
  unfold tri_rect_embedding at *
  contrapose hab
  match a with
  | 0 => match b with
    | 0 => tauto
    | 1 =>
      show  ¬ (0 % 4 : Fin 4) =  1 % 4
      exact ne_of_beq_false rfl
    | 2 =>
      show ¬0 = if Even (x.1 + x.2) then 2 else 3
      by_cases h : Even (x.1+x.2)
      · rw [if_pos h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;simp at Q
      · rw [if_neg h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc; simp only [Fin.val_zero] at Q;tauto
  | 1 => match b with
    | 1 => tauto
    | 0 =>
      show  ¬ (1 % 4 : Fin 4) =  0 % 4
      exact ne_of_beq_false rfl
    | 2 =>
      show  ¬1 = if Even (x.1 + x.2) then 2 else 3
      by_cases h : Even (x.1+x.2)
      · rw [if_pos h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;simp at Q
      · rw [if_neg h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;
        simp only [Fin.val_one] at Q;
        apply Nat.succ_injective at Q
        tauto
  | 2 => match b with
    | 1 =>
      show ¬(if Even (x.1 + x.2) then 2 else 3) = 1
      by_cases h : Even (x.1+x.2)
      · rw [if_pos h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;simp at Q
      · rw [if_neg h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;
        simp only [Fin.val_one] at Q;
        apply Nat.succ_injective at Q
        tauto
    | 0 =>
      show ¬(if Even (x.1 + x.2) then 2 else 3) = 0
      by_cases h : Even (x.1+x.2)
      · rw [if_pos h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;
        simp at Q
      · rw [if_neg h];intro hc
        let Q := congr_arg (fun x ↦ x.1) hc;
        simp only [Fin.val_zero] at Q;
        tauto
    | 2 => tauto

/-- `sp` is injective. -/
theorem sp_injective : Function.Injective sp := by
  intro x y hxy
  unfold sp at *
  rw [add_left_inj] at hxy
  tauto

/-- `sm` is injective. -/
theorem sm_injective : Function.Injective sm := by
  intro x y hxy
  unfold sm at *
  rw [add_left_inj] at hxy;
  tauto


/-- `go_WS` is injective. -/
theorem go_WS_injective : Function.Injective go_WS := by
  intro x y hxy
  unfold go_WS at *
  split_ifs at * with hx hy₀ hy₁
  · exact sp_injective hxy
  · unfold sp sm at hxy
    let Q := Prod.ext_iff.mp hxy
    simp only [Prod.fst_add, add_zero, Prod.snd_add] at Q
    revert hy₀
    contrapose
    simp only [not_not]
    obtain ⟨k,hk⟩ := hx
    intro
    exists (k+1); linarith
  · unfold sm sp at hxy
    let Q := Prod.ext_iff.mp hxy
    simp only [Prod.fst_add, add_zero, Prod.snd_add] at Q
    revert hx
    contrapose
    simp only [not_not]
    obtain ⟨k,hk⟩ := hy₁; intro;exists (k+1); linarith
  · exact sm_injective hxy

/-- `tri` is right injective. -/
theorem right_injective_tri : right_injective tri := by
  unfold tri
  intro a; match a with
  | 0 => exact add_left_injective _
  | 1 => exact add_left_injective _
  | 2 =>
    intro x y hxy;
    contrapose hxy
    show ¬ go_WS x = go_WS y
    contrapose hxy
    rw [not_not] at *
    exact go_WS_injective hxy

/-- `tri` is left injective. -/
theorem left_injective_tri : left_injective tri := by
intro x a b hab; simp at hab; contrapose hab; unfold tri;
exact match a with
| 0 => match b with
  | 0 => by tauto
  | 1 => by
      conv => rhs;lhs;whnf
      conv => rhs;rhs;whnf
      simp
  | 2 => by
    show go_D x ≠ go_WS x;
    unfold go_D go_WS sp sm;
    by_cases h:(Even (x.1 + x.2))
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
| 1 => match b with
  | 0 => by
      conv => rhs;lhs;whnf
      conv => rhs;rhs;whnf
      simp
  | 1 => by tauto
  | 2 => by
    show go_A x ≠ go_WS x;
    unfold go_A go_WS sp sm;
    by_cases h:(Even (x.1 + x.2))
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp
| 2 => match b with
  | 0 => by
    show go_WS x   ≠ go_D x; unfold go_WS go_D sp sm;
    by_cases h:(Even (x.1 + x.2))
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp
  | 1 => by
    show go_WS x   ≠ go_A x; unfold go_WS go_A sm sp;
    by_cases h:(Even (x.1 + x.2))
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  | 2 => by tauto

/-- `rectMap` is injective. -/
theorem rectMap_injective : Function.Injective rectMap := by decide

/-- `rect₃Map` is injective. -/
theorem rect₃Map_injective : Function.Injective rect₃Map := by decide

/-- `hex` is left injective. -/
theorem left_injective_hex : left_injective hex := by
  intro a
  unfold hex
  intro x y hxy
  rw [add_right_inj] at hxy
  exact hexMap_injective hxy

/-- `rect` is left injective. -/
theorem left_injective_rect : left_injective rect := by
  unfold left_injective
  intro a
  unfold rect
  intro x y hxy
  rw [add_right_inj] at hxy
  exact rectMap_injective hxy

/-- `rect₃` is left injective. -/
theorem left_injective_rect₃ : left_injective rect₃ := by
  unfold left_injective
  intro a
  unfold rect₃
  intro x y hxy
  rw [add_right_inj] at hxy
  exact rect₃Map_injective hxy

/-- `rect` is right injective. -/
lemma right_injective_rect : right_injective rect   := fun _ ↦ add_left_injective _

/-- `rect₃` is right injective. -/
lemma right_injective_rect₃ : right_injective rect₃ := fun _ ↦ add_left_injective _

/-- `hex` is right injective. -/
lemma right_injective_hex : right_injective hex   := fun _ ↦ add_left_injective _

end Left_and_right_injectivity


section Equivalent_existential_definitions_of_point_earned

/-- If Anna has a brother, return a boy who has a sister. -/
def choice_ex {β:Type} [Fintype β] {l : ℕ} (P : β → Fin l → Prop)
    [DecidablePred fun a => ∃ i, P a i]
    [DecidablePred fun i => ∃ a, P a i]
    [∀ a, DecidablePred fun n => ∃ (hq : n < l), P a { val := n, isLt := hq }] :
    (filter (fun a ↦ ∃ i, P a i) (univ : Finset β)) →
    (filter (fun i ↦ ∃ a, P a i) (univ : Finset (Fin l))) := by
  intro a; let a₂ := a.2;
  simp only [mem_filter, mem_univ, true_and] at a₂
  have h₀: ∃ (i : ℕ), ∃ (hi : i < l), P a ⟨i,hi⟩ := by
    obtain ⟨i,_⟩ := a₂;exists i.1, i.2
  exact ⟨⟨Nat.find h₀,(Nat.find_spec h₀).1⟩,by simp; exists a; exact (Nat.find_spec h₀).2⟩

/-- If each girl has at most one brother, the map from girl-who-has-a-brother
  to boy-who-has-a-sister is injective. -/
lemma choice_ex_injective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
    [DecidablePred fun a => ∃ i, P a i]
    [DecidablePred fun i => ∃ a, P a i]
    [(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
    (h_unique_dir : ∀ {i a₀ a₁}, P a₀ i → P a₁ i → a₀ = a₁) :
Function.Injective (choice_ex P) := by
  intro a b hab
  unfold choice_ex at hab
  simp only [Subtype.mk.injEq, Fin.mk.injEq] at hab

  let a₂ := a.2; let b₂ := b.2
  simp only [mem_filter, mem_univ, true_and] at a₂ b₂
  rw [Fin.exists_iff] at a₂ b₂
  let ia := (⟨Nat.find a₂, (Nat.find_spec a₂).1⟩ : Fin l.succ)
  let ib := (⟨Nat.find b₂, (Nat.find_spec b₂).1⟩ : Fin l.succ)

  have hib₂: P b ib := (Nat.find_spec b₂).2

  have : ia = ib := Fin.mk_eq_mk.mpr hab
  rw [← this] at hib₂
  exact Subtype.ext (h_unique_dir (Nat.find_spec a₂).2 hib₂)

/-- Anna is a sister of a chosen brother who has Anna as his sister. -/
lemma choice_ex_aux {β:Type} [Fintype β] {l : ℕ} {P: β → Fin l → Prop}
    [DecidablePred fun i => ∃ a, P a i] [DecidablePred fun a => ∃ i, P a i]
    [(a : β) → DecidablePred fun n => ∃ (hq : n < l), P a { val := n, isLt := hq }]
    {i: { x // x ∈ filter (fun i => ∃ a, P a i) univ }}
    {a: β} (ha : P a i) :
    P a ((choice_ex P ⟨a, (by simp; exists i)⟩) : Fin l) := by
  have witness:  ∃ j, ∃ (h : j < l), P a ⟨j,h⟩ := by exists i, i.1.2
  exact (Nat.find_spec witness).2

/-- If each girl has at most one brother, the map from girl-who-has-a-brother
  to boy-who-has-a-sister is surjective. -/
lemma choice_ex_surjective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
    [DecidablePred fun a => ∃ i, P a i] [DecidablePred fun i => ∃ a, P a i]
    [(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a ⟨n, hq⟩]
    (h_unique_loc : ∀ {a i₀ i₁}, P a i₀ → P a i₁ → i₀ = i₁) :
    Function.Surjective (choice_ex P) := by
  intro i
  have i₂ := i.2
  simp only [mem_filter, mem_univ,
    true_and] at i₂;
  obtain ⟨a,ha⟩ := i₂
  exists ⟨a,by
    simp only [mem_filter, mem_univ, true_and]
    exists i
  ⟩
  exact Subtype.ext <|.symm <|h_unique_loc ha <|choice_ex_aux ha
/-- If each boy has at most one sister, and each girl has at most one brother,
  then the map that sends a boy who has a sister to a girl who has a brother is bijective. -/
lemma choice_ex_bijective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
    [DecidablePred fun a => ∃ i, P a i]
    [DecidablePred fun i => ∃ a, P a i]
    [ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
    (h_unique_loc : ∀ {a i₀ i₁}, P a i₀ → P a i₁ → i₀ = i₁)
    (h_unique_dir : ∀ {i a₀ a₁}, P a₀ i → P a₁ i → a₀ = a₁) : Function.Bijective (choice_ex P) :=
  ⟨choice_ex_injective  h_unique_dir, choice_ex_surjective h_unique_loc⟩

/-- If each boy has at most one sister, and each girl has at most one brother, then there are
  an equal number of boys who have a sister and girls who have a brother is bijective. -/
theorem choice_ex_finset_card {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
    [DecidablePred fun a => ∃ i, P a i] [DecidablePred fun i => ∃ a, P a i]
    [(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a     ⟨n,hq⟩]
    (h_unique_loc_dir : (∀ {a i₀ i₁}, P a i₀ → P a i₁ → i₀ = i₁) ∧
      ∀ {i a₀ a₁}, P a₀ i → P a₁ i → a₀ = a₁):
    card (filter (fun a ↦ ∃ i, P a i) univ) =
    card (filter (fun i ↦ ∃ a, P a i) univ) := by
  repeat rw [← Fintype.card_coe]
  exact Fintype.card_of_bijective (choice_ex_bijective h_unique_loc_dir.1 h_unique_loc_dir.2)

end Equivalent_existential_definitions_of_point_earned
