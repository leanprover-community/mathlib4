/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.ToDual

/-!
# Shapes of homological complexes

We define a structure `ComplexShape ι` for describing the shapes of homological complexes
indexed by a type `ι`.
This is intended to capture chain complexes and cochain complexes, indexed by either `ℕ` or `ℤ`,
as well as more exotic examples.

Rather than insisting that the indexing type has a `succ` function
specifying where differentials should go,
inside `c : ComplexShape` we have `c.Rel : ι → ι → Prop`,
and when we define `HomologicalComplex`
we only allow nonzero differentials `d i j` from `i` to `j` if `c.Rel i j`.
Further, we require that `{ j // c.Rel i j }` and `{ i // c.Rel i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Convenience functions `c.next` and `c.prev` provide these related elements
when they exist, and return their input otherwise.

This design aims to avoid certain problems arising from dependent type theory.
In particular we never have to ensure morphisms `d i : X i ⟶ X (succ i)` compose as
expected (which would often require rewriting by equations in the indexing type).
Instead such identities become separate proof obligations when verifying that a
complex we've constructed is of the desired shape.

If `α` is an `AddRightCancelSemigroup`, then we define `up α : ComplexShape α`,
the shape appropriate for cohomology, so `d : X i ⟶ X j` is nonzero only when `j = i + 1`,
as well as `down α : ComplexShape α`, appropriate for homology,
so `d : X i ⟶ X j` is nonzero only when `i = j + 1`.
(Later we'll introduce `CochainComplex` and `ChainComplex` as abbreviations for
`HomologicalComplex` with one of these shapes baked in.)
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

/-- A `c : ComplexShape ι` describes the shape of a chain complex,
with chain groups indexed by `ι`.
Typically `ι` will be `ℕ`, `ℤ`, or `Fin n`.

There is a relation `Rel : ι → ι → Prop`,
and we will only allow a non-zero differential from `i` to `j` when `Rel i j`.

There are axioms which imply `{ j // c.Rel i j }` and `{ i // c.Rel i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Below we define `c.next` and `c.prev` which provide these related elements.
-/
@[ext]
structure ComplexShape (ι : Type*) where
  /-- Nonzero differentials `X i ⟶ X j` shall be allowed
  on homological complexes when `Rel i j` holds. -/
  Rel : ι → ι → Prop
  /-- There is at most one nonzero differential from `X i`. -/
  next_eq : ∀ {i j j'}, Rel i j → Rel i j' → j = j'
  /-- There is at most one nonzero differential to `X j`. -/
  prev_eq : ∀ {i i' j}, Rel i j → Rel i' j → i = i'

attribute [to_dual self (reorder := 3 4)] ComplexShape.Rel
attribute [to_dual existing] ComplexShape.next_eq

namespace ComplexShape

variable {ι : Type*}

/-- The complex shape where only differentials from each `X.i` to itself are allowed.

This is mostly only useful so we can describe the relation of "related in `k` steps" below.
-/
@[simps]
def refl (ι : Type*) : ComplexShape ι where
  Rel i j := i = j
  next_eq w w' := w.symm.trans w'
  prev_eq w w' := w.trans w'.symm

/-- The reverse of a `ComplexShape`.
-/
@[simps]
def symm (c : ComplexShape ι) : ComplexShape ι where
  Rel i j := c.Rel j i
  next_eq w w' := c.prev_eq w w'
  prev_eq w w' := c.next_eq w w'

@[simp]
theorem symm_symm (c : ComplexShape ι) : c.symm.symm = c := rfl

theorem symm_bijective :
    Function.Bijective (ComplexShape.symm : ComplexShape ι → ComplexShape ι) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- The "composition" of two `ComplexShape`s.

We need this to define "related in k steps" later.
-/
@[simp]
def trans (c₁ c₂ : ComplexShape ι) : ComplexShape ι where
  Rel := Relation.Comp c₁.Rel c₂.Rel
  next_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₁.next_eq w₁ w₁'] at w₂
    exact c₂.next_eq w₂ w₂'
  prev_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₂.prev_eq w₂ w₂'] at w₁
    exact c₁.prev_eq w₁ w₁'

@[to_dual]
instance subsingleton_next (c : ComplexShape ι) (i : ι) : Subsingleton { j // c.Rel i j } := by
  constructor
  rintro ⟨j, rij⟩ ⟨k, rik⟩
  congr
  exact c.next_eq rij rik

open Classical in
/-- An arbitrary choice of index `j` such that `Rel i j`, if such exists.
Returns `i` otherwise.
-/
@[to_dual
/-- An arbitrary choice of index `i` such that `Rel i j`, if such exists.
Returns `j` otherwise.
-/]
def next (c : ComplexShape ι) (i : ι) : ι :=
  if h : ∃ j, c.Rel i j then h.choose else i

@[to_dual]
theorem next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.next i = j := by
  apply c.next_eq _ h
  rw [next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩

@[to_dual]
lemma next_eq_self' (c : ComplexShape ι) (j : ι) (hj : ∀ k, ¬c.Rel j k) :
    c.next j = j :=
  dif_neg (by simpa using hj)

@[to_dual]
lemma next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬c.Rel j (c.next j)) :
    c.next j = j :=
  c.next_eq_self' j (fun k hk' => hj (by simpa only [c.next_eq' hk'] using hk'))

/-- The `ComplexShape` allowing differentials from `X i` to `X (i+a)`.
(For example when `a = 1`, a cohomology theory indexed by `ℕ` or `ℤ`)
-/
def up' {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) : ComplexShape α where
  Rel i j := i + a = j
  next_eq hi hj := hi.symm.trans hj
  prev_eq hi hj := add_right_cancel (hi.trans hj.symm)

/-- The `ComplexShape` allowing differentials from `X (j+a)` to `X j`.
(For example when `a = 1`, a homology theory indexed by `ℕ` or `ℤ`)
-/
@[to_dual existing (attr := simps) up']
def down' {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) : ComplexShape α where
  Rel i j := j + a = i
  next_eq hi hj := add_right_cancel (hi.trans hj.symm)
  prev_eq hi hj := hi.symm.trans hj

@[to_dual (reorder := i j) down'_mk]
theorem up'_mk {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) (i j : α) (h : i + a = j) :
    (up' a).Rel i j := h

/-- The `ComplexShape` appropriate for cohomology, so `d : X i ⟶ X j` only when `j = i + 1`.
-/
@[to_dual (attr := simps!) down
/-- The `ComplexShape` appropriate for homology, so `d : X i ⟶ X j` only when `i = j + 1`.
-/]
def up (α : Type*) [Add α] [IsRightCancelAdd α] [One α] : ComplexShape α :=
  up' 1

@[to_dual (reorder := i j) down_mk]
theorem up_mk {α : Type*} [Add α] [IsRightCancelAdd α] [One α] (i j : α) (h : i + 1 = j) :
    (up α).Rel i j :=
  up'_mk (1 : α) i j h

end ComplexShape

end

namespace ComplexShape

variable (α : Type*) [AddRightCancelSemigroup α] [DecidableEq α]

set_option backward.defeqAttrib.useBackward true in
@[to_dual instDecidableRelRelDown']
instance instDecidableRelRelUp' (a : α) : DecidableRel (ComplexShape.up' a).Rel :=
  fun _ _ => by dsimp; infer_instance

@[to_dual instDecidableRelRelDown]
instance instDecidableRelRelUp [One α] : DecidableRel (ComplexShape.up α).Rel := by
  dsimp [ComplexShape.up]; infer_instance

end ComplexShape
