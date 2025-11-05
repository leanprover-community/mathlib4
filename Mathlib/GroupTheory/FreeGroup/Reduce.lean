/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.Sublists
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The maximal reduction of a word in a free group

## Main declarations

* `FreeGroup.reduce`: the maximal reduction of a word in a free group
* `FreeGroup.norm`: the length of the maximal reduction of a word in a free group

-/


namespace FreeGroup

variable {α : Type*}
variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

section Reduce

variable [DecidableEq α]

set_option linter.style.commandStart false in -- TODO fix the linter!
/-- The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
@[to_additive
/-- The maximal reduction of a word. It is computable iff `α` has decidable equality. -/]
def reduce : (L : List (α × Bool)) -> List (α × Bool) :=
  List.rec [] fun hd1 _tl1 ih =>
    List.casesOn ih [hd1] fun hd2 tl2 =>
      if hd1.1 = hd2.1 ∧ hd1.2 = not hd2.2 then tl2 else hd1 :: hd2 :: tl2

@[to_additive (attr := simp)] lemma reduce_nil : reduce ([] : List (α × Bool)) = [] := rfl
@[to_additive] lemma reduce_singleton (s : α × Bool) : reduce [s] = [s] := rfl

@[to_additive (attr := simp)]
theorem reduce.cons (x) :
    reduce (x :: L) =
      List.casesOn (reduce L) [x] fun hd tl =>
        if x.1 = hd.1 ∧ x.2 = not hd.2 then tl else x :: hd :: tl :=
  rfl

@[to_additive (attr := simp)]
theorem reduce_replicate (n : ℕ) (x : α × Bool) :
    reduce (.replicate n x) = .replicate n x := by
  induction n with
  | zero => simp [reduce]
  | succ n ih =>
    rw [List.replicate_succ, reduce.cons, ih]
    cases n with
    | zero => simp
    | succ n => simp [List.replicate_succ]

/-- The first theorem that characterises the function `reduce`: a word reduces to its maximal
  reduction. -/
@[to_additive /-- The first theorem that characterises the function `reduce`: a word reduces to its
  maximal reduction. -/]
theorem reduce.red : Red L (reduce L) := by
  induction L with
  | nil => constructor
  | cons hd1 tl1 ih =>
    dsimp
    revert ih
    generalize htl : reduce tl1 = TL
    intro ih
    cases TL with
    | nil => exact Red.cons_cons ih
    | cons hd2 tl2 =>
      dsimp only
      split_ifs with h
      · cases hd1
        cases hd2
        cases h
        dsimp at *
        subst_vars
        apply Red.trans (Red.cons_cons ih)
        exact Red.Step.cons_not_rev.to_red
      · exact Red.cons_cons ih

@[to_additive]
theorem reduce.not {p : Prop} :
    ∀ {L₁ L₂ L₃ : List (α × Bool)} {x b}, reduce L₁ = L₂ ++ (x, b) :: (x, !b) :: L₃ → p
  | [], L2, L3, _, _ => fun h => by cases L2 <;> injections
  | (x, b) :: L1, L2, L3, x', b' => by
    dsimp
    cases r : reduce L1 with
    | nil =>
      dsimp; intro h
      exfalso
      have := congr_arg List.length h
      grind
    | cons hd tail =>
      obtain ⟨y, c⟩ := hd
      dsimp only
      split_ifs with h <;> intro H
      · rw [H] at r
        exact @reduce.not _ L1 ((y, c) :: L2) L3 x' b' r
      rcases L2 with (_ | ⟨a, L2⟩)
      · injections; subst_vars
        simp at h
      · refine @reduce.not _ L1 L2 L3 x' b' ?_
        rw [List.cons_append] at H
        injection H with _ H
        rw [r, H]

/-- The second theorem that characterises the function `reduce`: the maximal reduction of a word
only reduces to itself. -/
@[to_additive /-- The second theorem that characterises the function `reduce`: the maximal
  reduction of a word only reduces to itself. -/]
theorem reduce.min (H : Red (reduce L₁) L₂) : reduce L₁ = L₂ := by
  induction H with
  | refl => rfl
  | tail _ H1 H2 =>
    obtain ⟨L4, L5, x, b⟩ := H1
    exact reduce.not H2

/-- `reduce` is idempotent, i.e. the maximal reduction of the maximal reduction of a word is the
  maximal reduction of the word. -/
@[to_additive (attr := simp) /-- `reduce` is idempotent, i.e. the maximal reduction of the maximal
  reduction of a word is the maximal reduction of the word. -/]
theorem reduce.idem : reduce (reduce L) = reduce L :=
  Eq.symm <| reduce.min reduce.red

@[to_additive]
theorem reduce.Step.eq (H : Red.Step L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (reduce.red.head H)
  (reduce.min HR13).trans (reduce.min HR23).symm

/-- If a word reduces to another word, then they have a common maximal reduction. -/
@[to_additive /-- If a word reduces to another word, then they have a common maximal reduction. -/]
theorem reduce.eq_of_red (H : Red L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (Red.trans H reduce.red)
  (reduce.min HR13).trans (reduce.min HR23).symm

alias red.reduce_eq := reduce.eq_of_red

alias freeAddGroup.red.reduce_eq := FreeAddGroup.reduce.eq_of_red

@[to_additive]
theorem Red.reduce_right (h : Red L₁ L₂) : Red L₁ (reduce L₂) :=
  reduce.eq_of_red h ▸ reduce.red

@[to_additive]
theorem Red.reduce_left (h : Red L₁ L₂) : Red L₂ (reduce L₁) :=
  (reduce.eq_of_red h).symm ▸ reduce.red

/-- If two words correspond to the same element in the free group, then they
have a common maximal reduction. This is the proof that the function that sends
an element of the free group to its maximal reduction is well-defined. -/
@[to_additive /-- If two words correspond to the same element in the additive free group, then they
  have a common maximal reduction. This is the proof that the function that sends an element of the
  free group to its maximal reduction is well-defined. -/]
theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, H13, H23⟩ := Red.exact.1 H
  (reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

/-- If two words have a common maximal reduction, then they correspond to the same element in the
  free group. -/
@[to_additive /-- If two words have a common maximal reduction, then they correspond to the same
  element in the additive free group. -/]
theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
  Red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

/-- A word and its maximal reduction correspond to the same element of the free group. -/
@[to_additive /-- A word and its maximal reduction correspond to the same element of the additive
  free group. -/]
theorem reduce.self : mk (reduce L) = mk L :=
  reduce.exact reduce.idem

/-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`, then `w₂` reduces to the maximal reduction
  of `w₁`. -/
@[to_additive /-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`, then `w₂` reduces to the
  maximal reduction of `w₁`. -/]
theorem reduce.rev (H : Red L₁ L₂) : Red L₂ (reduce L₁) :=
  (reduce.eq_of_red H).symm ▸ reduce.red

/-- The function that sends an element of the free group to its maximal reduction. -/
@[to_additive /-- The function that sends an element of the additive free group to its maximal
  reduction. -/]
def toWord : FreeGroup α → List (α × Bool) :=
  Quot.lift reduce fun _L₁ _L₂ H => reduce.Step.eq H

@[to_additive]
theorem mk_toWord : ∀ {x : FreeGroup α}, mk (toWord x) = x := by rintro ⟨L⟩; exact reduce.self

@[to_additive]
theorem toWord_injective : Function.Injective (toWord : FreeGroup α → List (α × Bool)) := by
  rintro ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

@[to_additive (attr := simp)]
theorem toWord_inj {x y : FreeGroup α} : toWord x = toWord y ↔ x = y :=
  toWord_injective.eq_iff

@[to_additive (attr := simp)]
theorem toWord_mk : (mk L₁).toWord = reduce L₁ :=
  rfl

@[to_additive (attr := simp)]
theorem toWord_of (a : α) : (of a).toWord = [(a, true)] :=
  rfl

@[to_additive (attr := simp)]
theorem reduce_toWord : ∀ x : FreeGroup α, reduce (toWord x) = toWord x := by
  rintro ⟨L⟩
  exact reduce.idem

@[to_additive (attr := simp)]
theorem toWord_one : (1 : FreeGroup α).toWord = [] :=
  rfl

@[to_additive]
theorem toWord_mul (x y : FreeGroup α) : toWord (x * y) = reduce (toWord x ++ toWord y) := by
  rw [← mk_toWord (x := x), ← mk_toWord (x := y)]
  simp

@[to_additive]
theorem toWord_pow (x : FreeGroup α) (n : ℕ) :
    toWord (x ^ n) = reduce (List.replicate n x.toWord).flatten := by
  rw [← mk_toWord (x := x)]
  simp

@[to_additive (attr := simp)]
theorem toWord_of_pow (a : α) (n : ℕ) : (of a ^ n).toWord = List.replicate n (a, true) := by
  rw [of, pow_mk, List.flatten_replicate_singleton, toWord]
  exact reduce_replicate _ _

@[to_additive (attr := simp)]
theorem toWord_eq_nil_iff {x : FreeGroup α} : x.toWord = [] ↔ x = 1 :=
  toWord_injective.eq_iff' toWord_one

@[to_additive]
theorem reduce_invRev {w : List (α × Bool)} : reduce (invRev w) = invRev (reduce w) := by
  apply reduce.min
  rw [← red_invRev_iff, invRev_invRev]
  apply Red.reduce_left
  have : Red (invRev (invRev w)) (invRev (reduce (invRev w))) := reduce.red.invRev
  rwa [invRev_invRev] at this

@[to_additive (attr := simp)]
theorem toWord_inv (x : FreeGroup α) : x⁻¹.toWord = invRev x.toWord := by
  rcases x with ⟨L⟩
  rw [quot_mk_eq_mk, inv_mk, toWord_mk, toWord_mk, reduce_invRev]

@[to_additive]
theorem reduce_append_reduce_reduce : reduce (reduce L₁ ++ reduce L₂) = reduce (L₁ ++ L₂) := by
  rw [← toWord_mk (L₁ := L₁ ++ L₂), ← mul_mk, toWord_mul, toWord_mk, toWord_mk]

@[to_additive]
theorem reduce_cons_reduce (a : α × Bool) : reduce (a :: reduce L) = reduce (a :: L) := by
  simp

@[to_additive]
theorem reduce_invRev_left_cancel : reduce (invRev L ++ L) = [] := by
  simp [← toWord_mk, ← mul_mk, ← inv_mk]

open List -- for <+ notation

@[to_additive]
lemma toWord_mul_sublist (x y : FreeGroup α) : (x * y).toWord <+ x.toWord ++ y.toWord := by
  refine Red.sublist ?_
  have : x * y = FreeGroup.mk (x.toWord ++ y.toWord) := by
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

/-- **Constructive Church-Rosser theorem** (compare `FreeGroup.Red.church_rosser`). -/
@[to_additive
/-- **Constructive Church-Rosser theorem** (compare `FreeAddGroup.Red.church_rosser`). -/]
def reduce.churchRosser (H12 : Red L₁ L₂) (H13 : Red L₁ L₃) : { L₄ // Red L₂ L₄ ∧ Red L₃ L₄ } :=
  ⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

@[to_additive]
instance : DecidableEq (FreeGroup α) :=
  toWord_injective.decidableEq

-- TODO @[to_additive] doesn't succeed, possibly due to a bug
--    FreeGroup.Red.decidableRel and FreeAddGroup.Red.decidableRel do not generate the same number
--    of equation lemmas.
instance Red.decidableRel : DecidableRel (@Red α)
  | [], [] => isTrue Red.refl
  | [], _hd2 :: _tl2 => isFalse fun H => List.noConfusion (Red.nil_iff.1 H)
  | (x, b) :: tl, [] =>
    match Red.decidableRel tl [(x, not b)] with
    | isTrue H => isTrue <| Red.trans (Red.cons_cons H) <| (@Red.Step.not _ [] [] _ _).to_red
    | isFalse H => isFalse fun H2 => H <| Red.cons_nil_iff_singleton.1 H2
  | (x1, b1) :: tl1, (x2, b2) :: tl2 =>
    if h : (x1, b1) = (x2, b2) then
      match Red.decidableRel tl1 tl2 with
      | isTrue H => isTrue <| h ▸ Red.cons_cons H
      | isFalse H => isFalse fun H2 => H <| (Red.cons_cons_iff _).1 <| h.symm ▸ H2
    else
      match Red.decidableRel tl1 ((x1, ! b1) :: (x2, b2) :: tl2) with
      | isTrue H => isTrue <| (Red.cons_cons H).tail Red.Step.cons_not
      | isFalse H => isFalse fun H2 => H <| Red.inv_of_red_of_ne h H2

/-- A list containing every word that `w₁` reduces to. -/
def Red.enum (L₁ : List (α × Bool)) : List (List (α × Bool)) :=
  List.filter (Red L₁) (List.sublists L₁)

theorem Red.enum.sound (H : L₂ ∈ List.filter (Red L₁) (List.sublists L₁)) : Red L₁ L₂ :=
  of_decide_eq_true (@List.of_mem_filter _ _ L₂ _ H)

theorem Red.enum.complete (H : Red L₁ L₂) : L₂ ∈ Red.enum L₁ :=
  List.mem_filter_of_mem (List.mem_sublists.2 <| Red.sublist H) (decide_eq_true H)

instance (L₁ : List (α × Bool)) : Fintype { L₂ // Red L₁ L₂ } :=
  Fintype.subtype (List.toFinset <| Red.enum L₁) fun _L₂ =>
    ⟨fun H => Red.enum.sound <| List.mem_toFinset.1 H, fun H =>
      List.mem_toFinset.2 <| Red.enum.complete H⟩

@[to_additive]
theorem IsReduced.reduce_eq (h : IsReduced L) : reduce L = L := by
  rw [← h.red_iff_eq]
  exact reduce.red

@[to_additive]
theorem IsReduced.of_reduce_eq (h : reduce L = L) : IsReduced L := by
  rw [IsReduced, List.isChain_iff_forall_rel_of_append_cons_cons]
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl rfl
  rw [eq_comm, ← Bool.ne_not]
  rintro rfl
  exact reduce.not (h.trans hl)

@[to_additive]
theorem isReduced_iff_reduce_eq : IsReduced L ↔ reduce L = L where
  mp h := h.reduce_eq
  mpr := .of_reduce_eq

@[to_additive]
theorem isReduced_toWord {x : FreeGroup α} : IsReduced x.toWord := by
  simp [isReduced_iff_reduce_eq]

end Reduce

@[to_additive (attr := simp)]
theorem one_ne_of (a : α) : 1 ≠ of a :=
  letI := Classical.decEq α; ne_of_apply_ne toWord <| by simp

@[to_additive (attr := simp)]
theorem of_ne_one (a : α) : of a ≠ 1 := one_ne_of _ |>.symm

@[to_additive]
instance [Nonempty α] : Nontrivial (FreeGroup α) where
  exists_pair_ne := let ⟨x⟩ := ‹Nonempty α›; ⟨1, of x, one_ne_of x⟩

section Metric

variable [DecidableEq α]

/-- The length of reduced words provides a norm on a free group. -/
@[to_additive /-- The length of reduced words provides a norm on an additive free group. -/]
def norm (x : FreeGroup α) : ℕ :=
  x.toWord.length

@[to_additive (attr := simp)]
theorem norm_inv_eq {x : FreeGroup α} : norm x⁻¹ = norm x := by
  simp only [norm, toWord_inv, invRev_length]

@[to_additive (attr := simp)]
theorem norm_eq_zero {x : FreeGroup α} : norm x = 0 ↔ x = 1 := by
  simp only [norm, List.length_eq_zero_iff, toWord_eq_nil_iff]

@[to_additive (attr := simp)]
theorem norm_one : norm (1 : FreeGroup α) = 0 :=
  rfl

@[to_additive (attr := simp)]
theorem norm_of (a : α) : norm (of a) = 1 :=
  rfl

@[to_additive]
theorem norm_mk_le : norm (mk L₁) ≤ L₁.length :=
  reduce.red.length_le

@[to_additive]
theorem norm_mul_le (x y : FreeGroup α) : norm (x * y) ≤ norm x + norm y :=
  calc
    norm (x * y) = norm (mk (x.toWord ++ y.toWord)) := by rw [← mul_mk, mk_toWord, mk_toWord]
    _ ≤ (x.toWord ++ y.toWord).length := norm_mk_le
    _ = norm x + norm y := List.length_append

@[to_additive (attr := simp)]
theorem norm_of_pow (a : α) (n : ℕ) : norm (of a ^ n) = n := by
  rw [norm, toWord_of_pow, List.length_replicate]

@[to_additive]
theorem norm_surjective [Nonempty α] : Function.Surjective (norm (α := α)) := by
  let ⟨a⟩ := ‹Nonempty α›
  exact Function.RightInverse.surjective <| norm_of_pow a

end Metric

end FreeGroup
