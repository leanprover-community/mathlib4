/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.List.Chain

/-!
# Free groups

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `FreeGroup` is the left adjoint to the forgetful
functor from groups to types, see `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `FreeGroup`/`FreeAddGroup`: the free group (resp. free additive group) associated to a type
  `α` defined as the words over `a : α × Bool` modulo the relation `a * x * x⁻¹ * b = a * b`.
* `FreeGroup.mk`/`FreeAddGroup.mk`: the canonical quotient map `List (α × Bool) → FreeGroup α`.
* `FreeGroup.of`/`FreeAddGroup.of`: the canonical injection `α → FreeGroup α`.
* `FreeGroup.lift f`/`FreeAddGroup.lift`: the canonical group homomorphism `FreeGroup α →* G`
  given a group `G` and a function `f : α → G`.

## Main statements

* `FreeGroup.Red.church_rosser`/`FreeAddGroup.Red.church_rosser`: The Church-Rosser theorem for word
  reduction (also known as Newman's diamond lemma).
* `FreeGroup.freeGroupUnitEquivInt`: The free group over the one-point type
  is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `FreeGroup.Red.Step`:
`w * x * x⁻¹ * v   ~>   w * v`, its reflexive transitive closure `FreeGroup.Red.trans`
and prove that its join is an equivalence relation. Then we introduce `FreeGroup α` as a quotient
over `FreeGroup.Red.Step`.

For the additive version we introduce the same relation under a different name so that we can
distinguish the quotient types more easily.


## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/

open Relation
open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20to_additive.2Emap_namespace
run_cmd Lean.Elab.Command.liftCoreM <| ToAdditive.insertTranslation `FreeGroup `FreeAddGroup

/-- Reduction step for the additive free group relation: `w + x + (-x) + v ~> w + v` -/
inductive FreeAddGroup.Red.Step : List (α × Bool) → List (α × Bool) → Prop
  | not {L₁ L₂ x b} : FreeAddGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeAddGroup.Red.Step.not

/-- Reduction step for the multiplicative free group relation: `w * x * x⁻¹ * v ~> w * v` -/
@[to_additive]
inductive FreeGroup.Red.Step : List (α × Bool) → List (α × Bool) → Prop
  | not {L₁ L₂ x b} : FreeGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeGroup.Red.Step.not

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/-- Reflexive-transitive closure of `Red.Step` -/
@[to_additive /-- Reflexive-transitive closure of `Red.Step` -/]
def Red : List (α × Bool) → List (α × Bool) → Prop :=
  ReflTransGen Red.Step

@[to_additive (attr := refl)]
theorem Red.refl : Red L L :=
  ReflTransGen.refl

@[to_additive (attr := trans)]
theorem Red.trans : Red L₁ L₂ → Red L₂ L₃ → Red L₁ L₃ :=
  ReflTransGen.trans

namespace Red

/-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄` -/
@[to_additive /-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e.
there are words `w₃ w₄` and letter `x` such that `w₁ = w₃ + x + (-x) + w₄` and `w₂ = w₃w₄` -/]
theorem Step.length : ∀ {L₁ L₂ : List (α × Bool)}, Step L₁ L₂ → L₂.length + 2 = L₁.length
  | _, _, @Red.Step.not _ L1 L2 x b => by rw [List.length_append, List.length_append]; rfl

@[to_additive (attr := simp)]
theorem Step.not_rev {x b} : Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂) := by
  cases b <;> exact Step.not

@[to_additive (attr := simp)]
theorem Step.cons_not {x b} : Red.Step ((x, b) :: (x, !b) :: L) L :=
  @Step.not _ [] _ _ _

@[to_additive (attr := simp)]
theorem Step.cons_not_rev {x b} : Red.Step ((x, !b) :: (x, b) :: L) L :=
  @Red.Step.not_rev _ [] _ _ _

@[to_additive]
theorem Step.append_left : ∀ {L₁ L₂ L₃ : List (α × Bool)}, Step L₂ L₃ → Step (L₁ ++ L₂) (L₁ ++ L₃)
  | _, _, _, Red.Step.not => by rw [← List.append_assoc, ← List.append_assoc]; constructor

@[to_additive]
theorem Step.cons {x} (H : Red.Step L₁ L₂) : Red.Step (x :: L₁) (x :: L₂) :=
  @Step.append_left _ [x] _ _ H

@[to_additive]
theorem Step.append_right : ∀ {L₁ L₂ L₃ : List (α × Bool)}, Step L₁ L₂ → Step (L₁ ++ L₃) (L₂ ++ L₃)
  | _, _, _, Red.Step.not => by simp

@[to_additive]
theorem not_step_nil : ¬Step [] L := by
  generalize h' : [] = L'
  intro h
  rcases h with - | ⟨L₁, L₂⟩
  simp at h'

@[to_additive]
theorem Step.cons_left_iff {a : α} {b : Bool} :
    Step ((a, b) :: L₁) L₂ ↔ (∃ L, Step L₁ L ∧ L₂ = (a, b) :: L) ∨ L₁ = (a, ! b) :: L₂ := by
  constructor
  · generalize hL : ((a, b) :: L₁ : List _) = L
    rintro @⟨_ | ⟨p, s'⟩, e, a', b'⟩ <;> simp_all
  · rintro (⟨L, h, rfl⟩ | rfl)
    · exact Step.cons h
    · exact Step.cons_not

@[to_additive]
theorem not_step_singleton : ∀ {p : α × Bool}, ¬Step [p] L
  | (a, b) => by simp [Step.cons_left_iff, not_step_nil]

@[to_additive]
theorem Step.cons_cons_iff : ∀ {p : α × Bool}, Step (p :: L₁) (p :: L₂) ↔ Step L₁ L₂ := by
  simp +contextual [Step.cons_left_iff, iff_def, or_imp]

@[to_additive]
theorem Step.append_left_iff : ∀ L, Step (L ++ L₁) (L ++ L₂) ↔ Step L₁ L₂
  | [] => by simp
  | p :: l => by simp [Step.append_left_iff l, Step.cons_cons_iff]

@[to_additive]
theorem Step.diamond_aux :
    ∀ {L₁ L₂ L₃ L₄ : List (α × Bool)} {x1 b1 x2 b2},
      L₁ ++ (x1, b1) :: (x1, !b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, !b2) :: L₄ →
        L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, Red.Step (L₁ ++ L₂) L₅ ∧ Red.Step (L₃ ++ L₄) L₅
  | [], _, [], _, _, _, _, _, H => by injections; subst_vars; simp
  | [], _, [(x3, b3)], _, _, _, _, _, H => by injections; subst_vars; simp
  | [(x3, b3)], _, [], _, _, _, _, _, H => by injections; subst_vars; simp
  | [], _, (x3, b3) :: (x4, b4) :: tl, _, _, _, _, _, H => by
    injections; subst_vars; right; exact ⟨_, Red.Step.not, Red.Step.cons_not⟩
  | (x3, b3) :: (x4, b4) :: tl, _, [], _, _, _, _, _, H => by
    injections; subst_vars; right; simpa using ⟨_, Red.Step.cons_not, Red.Step.not⟩
  | (x3, b3) :: tl, _, (x4, b4) :: tl2, _, _, _, _, _, H =>
    let ⟨H1, H2⟩ := List.cons.inj H
    match Step.diamond_aux H2 with
    | Or.inl H3 => Or.inl <| by simp [H1, H3]
    | Or.inr ⟨L₅, H3, H4⟩ => Or.inr ⟨_, Step.cons H3, by simpa [H1] using Step.cons H4⟩

@[to_additive]
theorem Step.diamond :
    ∀ {L₁ L₂ L₃ L₄ : List (α × Bool)},
      Red.Step L₁ L₃ → Red.Step L₂ L₄ → L₁ = L₂ → L₃ = L₄ ∨ ∃ L₅, Red.Step L₃ L₅ ∧ Red.Step L₄ L₅
  | _, _, _, _, Red.Step.not, Red.Step.not, H => Step.diamond_aux H

@[to_additive]
theorem Step.to_red : Step L₁ L₂ → Red L₁ L₂ :=
  ReflTransGen.single

/-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma. -/
@[to_additive
  /-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
  to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
  respectively. This is also known as Newman's diamond lemma. -/]
theorem church_rosser : Red L₁ L₂ → Red L₁ L₃ → Join Red L₂ L₃ :=
  Relation.church_rosser fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, hcd.to_red⟩

@[to_additive]
theorem cons_cons {p} : Red L₁ L₂ → Red (p :: L₁) (p :: L₂) :=
  ReflTransGen.lift (List.cons p) fun _ _ => Step.cons

@[to_additive]
theorem cons_cons_iff (p) : Red (p :: L₁) (p :: L₂) ↔ Red L₁ L₂ :=
  Iff.intro
    (by
      generalize eq₁ : (p :: L₁ : List _) = LL₁
      generalize eq₂ : (p :: L₂ : List _) = LL₂
      intro h
      induction h using Relation.ReflTransGen.head_induction_on generalizing L₁ L₂ with
      | refl =>
        subst_vars
        cases eq₂
        constructor
      | head h₁₂ h ih =>
        subst_vars
        obtain ⟨a, b⟩ := p
        rw [Step.cons_left_iff] at h₁₂
        rcases h₁₂ with (⟨L, h₁₂, rfl⟩ | rfl)
        · exact (ih rfl rfl).head h₁₂
        · exact (cons_cons h).tail Step.cons_not_rev)
    cons_cons

@[to_additive]
theorem append_append_left_iff : ∀ L, Red (L ++ L₁) (L ++ L₂) ↔ Red L₁ L₂
  | [] => Iff.rfl
  | p :: L => by simp [append_append_left_iff L, cons_cons_iff]

@[to_additive]
theorem append_append (h₁ : Red L₁ L₃) (h₂ : Red L₂ L₄) : Red (L₁ ++ L₂) (L₃ ++ L₄) :=
  (h₁.lift (fun L => L ++ L₂) fun _ _ => Step.append_right).trans ((append_append_left_iff _).2 h₂)

@[to_additive]
theorem to_append_iff : Red L (L₁ ++ L₂) ↔ ∃ L₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ ∧ Red L₄ L₂ :=
  Iff.intro
    (by
      generalize eq : L₁ ++ L₂ = L₁₂
      intro h
      induction h generalizing L₁ L₂ with
      | refl => exact ⟨_, _, eq.symm, by rfl, by rfl⟩
      | tail hLL' h ih =>
        obtain @⟨s, e, a, b⟩ := h
        rcases List.append_eq_append_iff.1 eq with (⟨s', rfl, rfl⟩ | ⟨e', rfl, rfl⟩)
        · have : L₁ ++ (s' ++ (a, b) :: (a, not b) :: e) = L₁ ++ s' ++ (a, b) :: (a, not b) :: e :=
            by simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁, h₂.tail Step.not⟩
        · have : s ++ (a, b) :: (a, not b) :: e' ++ L₂ = s ++ (a, b) :: (a, not b) :: (e' ++ L₂) :=
            by simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁.tail Step.not, h₂⟩)
    fun ⟨_, _, Eq, h₃, h₄⟩ => Eq.symm ▸ append_append h₃ h₄

/-- The empty word `[]` only reduces to itself. -/
@[to_additive /-- The empty word `[]` only reduces to itself. -/]
theorem nil_iff : Red [] L ↔ L = [] :=
  reflTransGen_iff_eq fun _ => Red.not_step_nil

/-- A letter only reduces to itself. -/
@[to_additive /-- A letter only reduces to itself. -/]
theorem singleton_iff {x} : Red [x] L₁ ↔ L₁ = [x] :=
  reflTransGen_iff_eq fun _ => not_step_singleton

/-- If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
@[to_additive
  /-- If `x` is a letter and `w` is a word such that `x + w` reduces to the empty word, then `w`
  reduces to `-x`. -/]
theorem cons_nil_iff_singleton {x b} : Red ((x, b) :: L) [] ↔ Red L [(x, not b)] :=
  Iff.intro
    (fun h => by
      have h₁ : Red ((x, not b) :: (x, b) :: L) [(x, not b)] := cons_cons h
      have h₂ : Red ((x, not b) :: (x, b) :: L) L := ReflTransGen.single Step.cons_not_rev
      let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂
      rw [singleton_iff] at h₁
      subst L'
      assumption)
    fun h => (cons_cons h).tail Step.cons_not

@[to_additive]
theorem red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) ≠ (x2, b2)) :
    Red [(x1, !b1), (x2, b2)] L ↔ L = [(x1, !b1), (x2, b2)] := by
  apply reflTransGen_iff_eq
  generalize eq : [(x1, not b1), (x2, b2)] = L'
  intro L h'
  cases h'
  simp only [List.cons_eq_append_iff, List.cons.injEq, Prod.mk.injEq, and_false,
    List.nil_eq_append_iff, exists_const, or_self, or_false, List.cons_ne_nil] at eq
  rcases eq with ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  simp at h

/-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
@[to_additive /-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `x + w₁`
reduces to `y + w₂`, then `w₁` reduces to `-x + y + w₂`. -/]
theorem inv_of_red_of_ne {x1 b1 x2 b2} (H1 : (x1, b1) ≠ (x2, b2))
    (H2 : Red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) : Red L₁ ((x1, not b1) :: (x2, b2) :: L₂) := by
  have : Red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂) := H2
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩
  · simp [nil_iff] at h₁
  · cases eq
    change Red (L₃ ++ L₄) ([(x1, not b1), (x2, b2)] ++ L₂)
    apply append_append _ h₂
    have h₁ : Red ((x1, not b1) :: (x1, b1) :: L₃) [(x1, not b1), (x2, b2)] := cons_cons h₁
    have h₂ : Red ((x1, not b1) :: (x1, b1) :: L₃) L₃ := Step.cons_not_rev.to_red
    rcases church_rosser h₁ h₂ with ⟨L', h₁, h₂⟩
    rw [red_iff_irreducible H1] at h₁
    rwa [h₁] at h₂

open List -- for <+ notation

@[to_additive]
theorem Step.sublist (H : Red.Step L₁ L₂) : L₂ <+ L₁ := by
  cases H; simp

/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
@[to_additive
/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/]
protected theorem sublist : Red L₁ L₂ → L₂ <+ L₁ :=
  @reflTransGen_of_transitive_reflexive
    _ (fun a b => b <+ a) _ _ _
    (fun l => List.Sublist.refl l)
    (fun _a _b _c hab hbc => List.Sublist.trans hbc hab)
    (fun _ _ => Red.Step.sublist)

@[to_additive]
theorem length_le (h : Red L₁ L₂) : L₂.length ≤ L₁.length :=
  h.sublist.length_le


@[to_additive]
theorem sizeof_of_step : ∀ {L₁ L₂ : List (α × Bool)},
    Step L₁ L₂ → sizeOf L₂ < sizeOf L₁
  | _, _, @Step.not _ L1 L2 x b => by
    induction L1 with
    | nil =>
      dsimp
      omega
    | cons hd tl ih =>
      dsimp
      exact Nat.add_lt_add_left ih _

@[to_additive]
theorem length (h : Red L₁ L₂) : ∃ n, L₁.length = L₂.length + 2 * n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _h₁₂ h₂₃ ih =>
    rcases ih with ⟨n, eq⟩
    exists 1 + n
    simp [Nat.mul_add, eq, (Step.length h₂₃).symm, add_assoc]

@[to_additive]
theorem antisymm (h₁₂ : Red L₁ L₂) (h₂₁ : Red L₂ L₁) : L₁ = L₂ :=
  h₂₁.sublist.antisymm h₁₂.sublist

end Red

@[to_additive]
theorem equivalence_join_red : Equivalence (Join (@Red α)) :=
  equivalence_join_reflTransGen fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩

@[to_additive]
theorem join_red_of_step (h : Red.Step L₁ L₂) : Join Red L₁ L₂ :=
  join_of_single reflexive_reflTransGen h.to_red

@[to_additive]
theorem eqvGen_step_iff_join_red : EqvGen Red.Step L₁ L₂ ↔ Join Red L₁ L₂ :=
  Iff.intro
    (fun h =>
      have : EqvGen (Join Red) L₁ L₂ := h.mono fun _ _ => join_red_of_step
      equivalence_join_red.eqvGen_iff.1 this)
    (join_of_equivalence (Relation.EqvGen.is_equivalence _) fun _ _ =>
      reflTransGen_of_equivalence (Relation.EqvGen.is_equivalence _) EqvGen.rel)

/-! ### Reduced words -/

/-- Predicate asserting that the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel. -/
@[to_additive /-- Predicate asserting the word `L` admits no reduction steps,
i.e., no two neighboring elements of the word cancel. -/]
def IsReduced (L : List (α × Bool)) : Prop := L.Chain' fun a b ↦ a.1 = b.1 → a.2 = b.2

section IsReduced

open List

@[to_additive (attr := simp)]
theorem IsReduced.nil : IsReduced ([] : List (α × Bool)) := chain'_nil

@[to_additive (attr := simp)]
theorem IsReduced.singleton {a : α × Bool} : IsReduced [a] := chain'_singleton a

@[to_additive (attr := simp)]
theorem isReduced_cons_cons {a b : (α × Bool)} :
    IsReduced (a :: b :: L) ↔ (a.1 = b.1 → a.2 = b.2) ∧ IsReduced (b :: L) := chain'_cons_cons

@[to_additive]
theorem IsReduced.not_step (h : IsReduced L₁) : ¬ Red.Step L₁ L₂ := fun step ↦ by
  induction step
  simp [IsReduced] at h

@[to_additive]
lemma IsReduced.of_forall_not_step :
    ∀ {L₁ : List (α × Bool)}, (∀ L₂, ¬ Red.Step L₁ L₂) → IsReduced L₁
  | [], _ => .nil
  | [a], _ => .singleton
  | (a₁, b₁) :: (a₂, b₂) :: L₁, hL₁ => by
    rw [isReduced_cons_cons]
    refine ⟨?_, .of_forall_not_step fun L₂ step ↦ hL₁ _ step.cons⟩
    rintro rfl
    symm
    rw [← Bool.ne_not]
    rintro rfl
    exact hL₁ L₁ <| .not (L₁ := [])

@[to_additive]
theorem isReduced_iff_not_step : IsReduced L₁ ↔ ∀ L₂, ¬ Red.Step L₁ L₂ where
  mp h _ := h.not_step
  mpr := .of_forall_not_step

@[to_additive]
theorem IsReduced.red_iff_eq (h : IsReduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]
theorem IsReduced.append_overlap {L₁ L₂ L₃ : List (α × Bool)} (h₁ : IsReduced (L₁ ++ L₂))
    (h₂ : IsReduced (L₂ ++ L₃)) (hn : L₂ ≠ []) : IsReduced (L₁ ++ L₂ ++ L₃) :=
  Chain'.append_overlap h₁ h₂ hn

@[to_additive]
theorem IsReduced.infix (h : IsReduced L₂) (h' : L₁ <:+: L₂) : IsReduced L₁ := Chain'.infix h h'

end IsReduced
end FreeGroup

/--
If `α` is a type, then `FreeGroup α` is the free group generated by `α`.
This is a group equipped with a function `FreeGroup.of : α → FreeGroup α` which has
the following universal property: if `G` is any group, and `f : α → G` is any function,
then this function is the composite of `FreeGroup.of` and a unique group homomorphism
`FreeGroup.lift f : FreeGroup α →* G`.

A typical element of `FreeGroup α` is a formal product of
elements of `α` and their formal inverses, quotient by reduction.
For example if `x` and `y` are terms of type `α` then `x⁻¹ * y * y * x * y⁻¹` is a
"typical" element of `FreeGroup α`. In particular if `α` is empty
then `FreeGroup α` is isomorphic to the trivial group, and if `α` has one term
then `FreeGroup α` is isomorphic to `Multiplicative ℤ`.
If `α` has two or more terms then `FreeGroup α` is not commutative.
-/
@[to_additive
/-- If `α` is a type, then `FreeAddGroup α` is the free additive group generated by `α`.
This is a group equipped with a function `FreeAddGroup.of : α → FreeAddGroup α` which has
the following universal property: if `G` is any group, and `f : α → G` is any function,
then this function is the composite of `FreeAddGroup.of` and a unique group homomorphism
`FreeAddGroup.lift f : FreeAddGroup α →+ G`.

A typical element of `FreeAddGroup α` is a formal sum of
elements of `α` and their formal inverses, quotient by reduction.
For example if `x` and `y` are terms of type `α` then `-x + y + y + x + -y` is a
"typical" element of `FreeAddGroup α`. In particular if `α` is empty
then `FreeAddGroup α` is isomorphic to the trivial group, and if `α` has one term
then `FreeAddGroup α` is isomorphic to `ℤ`.
If `α` has two or more terms then `FreeAddGroup α` is not commutative. -/]
def FreeGroup (α : Type u) : Type u :=
  Quot <| @FreeGroup.Red.Step α

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/-- The canonical map from `List (α × Bool)` to the free group on `α`. -/
@[to_additive /-- The canonical map from `List (α × Bool)` to the free additive group on `α`. -/]
def mk (L : List (α × Bool)) : FreeGroup α :=
  Quot.mk Red.Step L

@[to_additive (attr := simp)]
theorem quot_mk_eq_mk : Quot.mk Red.Step L = mk L :=
  rfl

@[to_additive (attr := simp)]
theorem quot_lift_mk (β : Type v) (f : List (α × Bool) → β)
    (H : ∀ L₁ L₂, Red.Step L₁ L₂ → f L₁ = f L₂) : Quot.lift f H (mk L) = f L :=
  rfl

@[to_additive (attr := simp)]
theorem quot_liftOn_mk (β : Type v) (f : List (α × Bool) → β)
    (H : ∀ L₁ L₂, Red.Step L₁ L₂ → f L₁ = f L₂) : Quot.liftOn (mk L) f H = f L :=
  rfl

open scoped Relator in
@[to_additive (attr := simp)]
theorem quot_map_mk (β : Type v) (f : List (α × Bool) → List (β × Bool))
    (H : (Red.Step ⇒ Red.Step) f f) : Quot.map f H (mk L) = mk (f L) :=
  rfl

@[to_additive]
instance : One (FreeGroup α) :=
  ⟨mk []⟩

@[to_additive]
theorem one_eq_mk : (1 : FreeGroup α) = mk [] :=
  rfl

@[to_additive]
instance : Inhabited (FreeGroup α) :=
  ⟨1⟩

@[to_additive]
instance [IsEmpty α] : Unique (FreeGroup α) := by unfold FreeGroup; infer_instance

@[to_additive]
instance : Mul (FreeGroup α) :=
  ⟨fun x y =>
    Quot.liftOn x
      (fun L₁ =>
        Quot.liftOn y (fun L₂ => mk <| L₁ ++ L₂) fun _L₂ _L₃ H =>
          Quot.sound <| Red.Step.append_left H)
      fun _L₁ _L₂ H => Quot.inductionOn y fun _L₃ => Quot.sound <| Red.Step.append_right H⟩

@[to_additive (attr := simp)]
theorem mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) :=
  rfl

/-- Transform a word representing a free group element into a word representing its inverse. -/
@[to_additive /-- Transform a word representing a free group element into a word representing its
  negative. -/]
def invRev (w : List (α × Bool)) : List (α × Bool) :=
  (List.map (fun g : α × Bool => (g.1, not g.2)) w).reverse

@[to_additive (attr := simp)]
theorem invRev_length : (invRev L₁).length = L₁.length := by simp [invRev]

@[to_additive (attr := simp)]
theorem invRev_invRev : invRev (invRev L₁) = L₁ := by
  simp [invRev, List.map_reverse, Function.comp_def]

@[to_additive (attr := simp)]
theorem invRev_empty : invRev ([] : List (α × Bool)) = [] :=
  rfl

@[to_additive (attr := simp)]
theorem invRev_append : invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁ := by simp [invRev]

@[to_additive]
theorem invRev_cons {a : (α × Bool)} : invRev (a :: L) = invRev L ++ invRev [a] := by
  simp [invRev]

@[to_additive]
theorem invRev_involutive : Function.Involutive (@invRev α) := fun _ => invRev_invRev

@[to_additive]
theorem invRev_injective : Function.Injective (@invRev α) :=
  invRev_involutive.injective

@[to_additive]
theorem invRev_surjective : Function.Surjective (@invRev α) :=
  invRev_involutive.surjective

@[to_additive]
theorem invRev_bijective : Function.Bijective (@invRev α) :=
  invRev_involutive.bijective

@[to_additive]
instance : Inv (FreeGroup α) :=
  ⟨Quot.map invRev
      (by
        intro a b h
        cases h
        simp [invRev])⟩

@[to_additive (attr := simp)]
theorem inv_mk : (mk L)⁻¹ = mk (invRev L) :=
  rfl

@[to_additive]
theorem Red.Step.invRev {L₁ L₂ : List (α × Bool)} (h : Red.Step L₁ L₂) :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) := by
  obtain ⟨a, b, x, y⟩ := h
  simp [FreeGroup.invRev]

@[to_additive]
theorem Red.invRev {L₁ L₂ : List (α × Bool)} (h : Red L₁ L₂) : Red (invRev L₁) (invRev L₂) :=
  Relation.ReflTransGen.lift _ (fun _a _b => Red.Step.invRev) h

@[to_additive (attr := simp)]
theorem Red.step_invRev_iff :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) ↔ Red.Step L₁ L₂ :=
  ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive (attr := simp)]
theorem red_invRev_iff : Red (invRev L₁) (invRev L₂) ↔ Red L₁ L₂ :=
  ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive]
instance : Group (FreeGroup α) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc := by rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp
  one_mul := by rintro ⟨L⟩; rfl
  mul_one := by rintro ⟨L⟩; simp [one_eq_mk]
  inv_mul_cancel := by
    rintro ⟨L⟩
    exact
      List.recOn L rfl fun ⟨x, b⟩ tl ih =>
          Eq.trans (Quot.sound <| by simp [invRev]) ih

@[to_additive (attr := simp)]
theorem pow_mk (n : ℕ) : mk L ^ n = mk (List.flatten <| List.replicate n L) :=
  match n with
  | 0 => rfl
  | n + 1 => by rw [pow_succ', pow_mk, mul_mk, List.replicate_succ, List.flatten_cons]

/-- `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
@[to_additive /-- `of` is the canonical injection from the type to the free group over that type
  by sending each element to the equivalence class of the letter that is the element. -/]
def of (x : α) : FreeGroup α :=
  mk [(x, true)]

@[to_additive (attr := elab_as_elim, induction_eliminator)]
protected lemma induction_on {C : FreeGroup α → Prop} (z : FreeGroup α) (C1 : C 1)
    (of : ∀ x, C <| of x) (inv_of : ∀ x, C (.of x) → C (.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  Quot.inductionOn z fun L ↦ L.recOn C1 fun ⟨x, b⟩ _tl ih ↦
    b.recOn (mul _ _ (inv_of _ <| of x) ih) (mul _ _ (of x) ih)

/-- Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext) /-- Two homomorphisms out of a free additive group are equal if they are
  equal on generators. See note [partially-applied ext lemmas]. -/]
lemma ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α →* M) (h : ∀ a, f (of a) = g (of a)) :
    f = g := by
  ext x
  have this (x) : f (of x)⁻¹ = g (of x)⁻¹ := by
    trans f (of x)⁻¹ * f (of x) * g (of x)⁻¹
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*]

@[to_additive]
theorem Red.exact : mk L₁ = mk L₂ ↔ Join Red L₁ L₂ :=
  calc
    mk L₁ = mk L₂ ↔ EqvGen Red.Step L₁ L₂ := Iff.intro Quot.eqvGen_exact Quot.eqvGen_sound
    _ ↔ Join Red L₁ L₂ := eqvGen_step_iff_join_red

/-- The canonical map from the type to the free group is an injection. -/
@[to_additive /-- The canonical map from the type to the additive free group is an injection. -/]
theorem of_injective : Function.Injective (@of α) := fun _ _ H => by
  let ⟨L₁, hx, hy⟩ := Red.exact.1 H
  simp [Red.singleton_iff] at hx hy; simp_all

section lift

variable {β : Type v} [Group β] (f : α → β) {x y : FreeGroup α}

/-- Given `f : α → β` with `β` a group, the canonical map `List (α × Bool) → β` -/
@[to_additive /-- Given `f : α → β` with `β` an additive group, the canonical map
  `List (α × Bool) → β` -/]
def Lift.aux : List (α × Bool) → β := fun L =>
  List.prod <| L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹

@[to_additive]
theorem Red.Step.lift {f : α → β} (H : Red.Step L₁ L₂) : Lift.aux f L₁ = Lift.aux f L₂ := by
  obtain @⟨_, _, _, b⟩ := H; cases b <;> simp [Lift.aux]

/-- If `β` is a group, then any function from `α` to `β` extends uniquely to a group homomorphism
from the free group over `α` to `β` -/
@[to_additive (attr := simps symm_apply)
  /-- If `β` is an additive group, then any function from `α` to `β` extends uniquely to an
  additive group homomorphism from the free additive group over `α` to `β` -/]
def lift : (α → β) ≃ (FreeGroup α →* β) where
  toFun f :=
    MonoidHom.mk' (Quot.lift (Lift.aux f) fun _ _ => Red.Step.lift) <| by
      rintro ⟨L₁⟩ ⟨L₂⟩; simp [Lift.aux]
  invFun g := g ∘ of
  left_inv f := List.prod_singleton
  right_inv g := by ext; simp [of, Lift.aux]

variable {f}

@[to_additive (attr := simp)]
theorem lift_mk : lift f (mk L) = List.prod (L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹) :=
  rfl

@[to_additive (attr := simp)]
theorem lift_apply_of {x} : lift f (of x) = f x :=
  List.prod_singleton

@[to_additive]
theorem lift_unique (g : FreeGroup α →* β) (hg : ∀ x, g (FreeGroup.of x) = f x) {x} :
    g x = FreeGroup.lift f x :=
  DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ FreeGroup.of = f)) x

@[to_additive]
theorem lift_of_eq_id (α) : lift of = MonoidHom.id (FreeGroup α) :=
  lift.apply_symm_apply (MonoidHom.id _)

@[to_additive]
theorem lift_of_apply (x : FreeGroup α) : lift FreeGroup.of x = x :=
  DFunLike.congr_fun (lift_of_eq_id α) x

@[to_additive]
theorem range_lift_le {s : Subgroup β} (H : Set.range f ⊆ s) : (lift f).range ≤ s := by
  rintro _ ⟨⟨L⟩, rfl⟩
  exact List.recOn L s.one_mem fun ⟨x, b⟩ tl ih ↦
    Bool.recOn b (by simpa using s.mul_mem (s.inv_mem <| H ⟨x, rfl⟩) ih)
      (by simpa using s.mul_mem (H ⟨x, rfl⟩) ih)

@[to_additive]
theorem range_lift_eq_closure : (lift f).range = Subgroup.closure (Set.range f) := by
  apply le_antisymm (range_lift_le Subgroup.subset_closure)
  rw [Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨FreeGroup.of a, by simp only [lift_apply_of]⟩

/-- The generators of `FreeGroup α` generate `FreeGroup α`. That is, the subgroup closure of the
set of generators equals `⊤`. -/
@[to_additive (attr := simp)]
theorem closure_range_of (α) :
    Subgroup.closure (Set.range (FreeGroup.of : α → FreeGroup α)) = ⊤ := by
  rw [← range_lift_eq_closure, lift_of_eq_id]
  exact MonoidHom.range_eq_top.2 Function.surjective_id

end lift

section Map

variable {β : Type v} (f : α → β) {x y : FreeGroup α}

/-- Any function from `α` to `β` extends uniquely to a group homomorphism from the free group over
  `α` to the free group over `β`. -/
@[to_additive /-- Any function from `α` to `β` extends uniquely to an additive group homomorphism
from the additive free group over `α` to the additive free group over `β`. -/]
def map : FreeGroup α →* FreeGroup β :=
  MonoidHom.mk'
    (Quot.map (List.map fun x => (f x.1, x.2)) fun L₁ L₂ H => by cases H; simp)
    (by rintro ⟨L₁⟩ ⟨L₂⟩; simp)

variable {f}

@[to_additive (attr := simp)]
theorem map.mk : map f (mk L) = mk (L.map fun x => (f x.1, x.2)) :=
  rfl

@[to_additive (attr := simp)]
theorem map.id (x : FreeGroup α) : map id x = x := by rcases x with ⟨L⟩; simp [List.map_id']

@[to_additive (attr := simp)]
theorem map.id' (x : FreeGroup α) : map (fun z => z) x = x :=
  map.id x

@[to_additive]
theorem map.comp {γ : Type w} (f : α → β) (g : β → γ) (x) :
    map g (map f x) = map (g ∘ f) x := by
  rcases x with ⟨L⟩; simp [Function.comp_def]

@[to_additive (attr := simp)]
theorem map.of {x} : map f (of x) = of (f x) :=
  rfl

@[to_additive]
theorem map.unique (g : FreeGroup α →* FreeGroup β)
    (hg : ∀ x, g (FreeGroup.of x) = FreeGroup.of (f x)) :
    ∀ {x}, g x = map f x := by
  rintro ⟨L⟩
  exact List.recOn L g.map_one fun ⟨x, b⟩ t (ih : g (FreeGroup.mk t) = map f (FreeGroup.mk t)) =>
    Bool.recOn b
      (show g ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) =
          FreeGroup.map f ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) by
        simp [g.map_mul, g.map_inv, hg, ih])
      (show g (FreeGroup.of x * FreeGroup.mk t) =
          FreeGroup.map f (FreeGroup.of x * FreeGroup.mk t) by simp [g.map_mul, hg, ih])

@[to_additive]
theorem map_eq_lift : map f x = lift (of ∘ f) x :=
  Eq.symm <| map.unique _ fun x => by simp

/-- Equivalent types give rise to multiplicatively equivalent free groups.

The converse can be found in `Mathlib/GroupTheory/FreeGroup/GeneratorEquiv.lean`, as
`Equiv.ofFreeGroupEquiv`. -/
@[to_additive (attr := simps apply)
  /-- Equivalent types give rise to additively equivalent additive free groups. -/]
def freeGroupCongr {α β} (e : α ≃ β) : FreeGroup α ≃* FreeGroup β where
  toFun := map e
  invFun := map e.symm
  left_inv x := by simp [map.comp]
  right_inv x := by simp [map.comp]
  map_mul' := MonoidHom.map_mul _

@[to_additive (attr := simp)]
theorem freeGroupCongr_refl : freeGroupCongr (Equiv.refl α) = MulEquiv.refl _ :=
  MulEquiv.ext map.id

@[to_additive (attr := simp)]
theorem freeGroupCongr_symm {α β} (e : α ≃ β) : (freeGroupCongr e).symm = freeGroupCongr e.symm :=
  rfl

@[to_additive]
theorem freeGroupCongr_trans {α β γ} (e : α ≃ β) (f : β ≃ γ) :
    (freeGroupCongr e).trans (freeGroupCongr f) = freeGroupCongr (e.trans f) :=
  MulEquiv.ext <| map.comp _ _

end Map

section Prod

variable [Group α] (x y : FreeGroup α)

/-- If `α` is a group, then any function from `α` to `α` extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative version of `FreeGroup.sum`. -/
@[to_additive /-- If `α` is an additive group, then any function from `α` to `α` extends uniquely
  to an additive homomorphism from the additive free group over `α` to `α`. -/]
def prod : FreeGroup α →* α :=
  lift id

variable {x y}

@[to_additive (attr := simp)]
theorem prod_mk : prod (mk L) = List.prod (L.map fun x => cond x.2 x.1 x.1⁻¹) :=
  rfl

@[to_additive (attr := simp)]
theorem prod.of {x : α} : prod (of x) = x :=
  lift_apply_of

@[to_additive]
theorem prod.unique (g : FreeGroup α →* α) (hg : ∀ x, g (FreeGroup.of x) = x) {x} : g x = prod x :=
  lift_unique g hg

end Prod

@[to_additive]
theorem lift_eq_prod_map {β : Type v} [Group β] {f : α → β} {x} : lift f x = prod (map f x) := by
  rw [← lift_unique (prod.comp (map f)) (by simp), MonoidHom.coe_comp, Function.comp_apply]

section Sum

variable [AddGroup α] (x y : FreeGroup α)

/-- If `α` is a group, then any function from `α` to `α` extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the additive version of `Prod`. -/
def sum : α :=
  @prod (Multiplicative _) _ x

variable {x y}

@[simp]
theorem sum_mk : sum (mk L) = List.sum (L.map fun x => cond x.2 x.1 (-x.1)) :=
  rfl

@[simp]
theorem sum.of {x : α} : sum (of x) = x :=
  @prod.of _ (_) _

-- note: there are no bundled homs with different notation in the domain and codomain, so we copy
-- these manually
@[simp]
theorem sum.map_mul : sum (x * y) = sum x + sum y :=
  (@prod (Multiplicative _) _).map_mul _ _

@[simp]
theorem sum.map_one : sum (1 : FreeGroup α) = 0 :=
  (@prod (Multiplicative _) _).map_one

@[simp]
theorem sum.map_inv : sum x⁻¹ = -sum x :=
  (prod : FreeGroup (Multiplicative α) →* Multiplicative α).map_inv _

end Sum

/-- The bijection between the free group on the empty type, and a type with one element. -/
@[to_additive /-- The bijection between the additive free group on the empty type, and a type with
  one element. -/]
def freeGroupEmptyEquivUnit : FreeGroup Empty ≃ Unit where
  toFun _ := ()
  invFun _ := 1
  left_inv := by rintro ⟨_ | ⟨⟨⟨⟩, _⟩, _⟩⟩; rfl

/-- The bijection between the free group on a singleton, and the integers. -/
def freeGroupUnitEquivInt : FreeGroup Unit ≃ ℤ where
  toFun x := sum (by
    revert x
    exact ↑(map fun _ => (1 : ℤ)))
  invFun x := of () ^ x
  left_inv := by
    rintro ⟨L⟩
    simp only [quot_mk_eq_mk, map.mk, sum_mk, List.map_map]
    exact List.recOn L
     (by rfl)
     (fun ⟨⟨⟩, b⟩ tl ih => by
        cases b <;> simp [zpow_add] at ih ⊢ <;> rw [ih] <;> rfl)
  right_inv x :=
    Int.induction_on x (by simp)
      (fun i ih => by
        simp only [zpow_natCast, map_pow, map.of] at ih
        simp [zpow_add, ih])
      (fun i ih => by
        simp only [zpow_neg, zpow_natCast, map_inv, map_pow, map.of, sum.map_inv, neg_inj] at ih
        simp [zpow_add, ih, sub_eq_add_neg])

section Category

variable {β : Type u}

@[to_additive]
instance : Monad FreeGroup.{u} where
  pure {_α} := of
  map {_α _β f} := map f
  bind {_α _β x f} := lift f x

@[to_additive]
theorem map_pure (f : α → β) (x : α) : f <$> (pure x : FreeGroup α) = pure (f x) :=
  map.of

@[to_additive (attr := simp)]
theorem map_one (f : α → β) : f <$> (1 : FreeGroup α) = 1 :=
  (map f).map_one

@[to_additive (attr := simp)]
theorem map_mul (f : α → β) (x y : FreeGroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  (map f).map_mul x y

@[to_additive (attr := simp)]
theorem map_inv (f : α → β) (x : FreeGroup α) : f <$> x⁻¹ = (f <$> x)⁻¹ :=
  (map f).map_inv x

@[to_additive]
theorem pure_bind (f : α → FreeGroup β) (x) : pure x >>= f = f x :=
  lift_apply_of

@[to_additive (attr := simp)]
theorem one_bind (f : α → FreeGroup β) : 1 >>= f = 1 :=
  (lift f).map_one

@[to_additive (attr := simp)]
theorem mul_bind (f : α → FreeGroup β) (x y : FreeGroup α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  (lift f).map_mul _ _

@[to_additive (attr := simp)]
theorem inv_bind (f : α → FreeGroup β) (x : FreeGroup α) : x⁻¹ >>= f = (x >>= f)⁻¹ :=
  (lift f).map_inv _

@[to_additive]
instance : LawfulMonad FreeGroup.{u} := LawfulMonad.mk'
  (id_map := fun x =>
    FreeGroup.induction_on x (map_one id) (fun x => map_pure id x) (fun x ih => by rw [map_inv, ih])
      fun x y ihx ihy => by rw [map_mul, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun x => by
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_ <;> simp +contextual [instMonad])
  (bind_pure_comp := fun f x => by
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_ <;> simp +contextual [instMonad])

end Category

end FreeGroup
