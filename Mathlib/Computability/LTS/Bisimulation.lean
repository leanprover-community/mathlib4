/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Computability.LTS.Basic
import Mathlib.Computability.LTS.TraceEq
import Mathlib.Data.Rel

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of an `LTS`, which establishes a tight semantic
correspondence. More specifically, if two states `s1` and `s2` are related by a bisimulation, then
`s1` can mimic all transitions of `s2` and vice versa. Furthermore, the derivatives reaches through
these transitions remain related by the bisimulation.

Bisimilarity is the largest bisimulation: given an `LTS`, it relates any two states that are related
by a bisimulation for that LTS.

For an introduction to theory of bisimulation, we refer to [Sangiorgi2011].

## Main definitions

- `Bisimulation lts r`: the relation `r` on the states of the LTS `lts` is a bisimulation.
- `Bisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some bisimulation on `lts`.
- `BisimulationUpTo lts r`: the relation `r` is a bisimulation up to bisimilarity (this is known as
one of the 'up to' techniques for bisimulation).

## Notations

- `s1 ~[lts] s2`: the states `s1` and `s2` are bisimilar in the LTS `lts`.

## Main statements

- `Bisimulation.inv`: the inverse of a bisimulation is a bisimulation.
- `Bisimilarity.eqRel`: bisimilarity is an equivalence relation (see `Equivalence`).
- `Bisimilarity.is_bisimulation`: bisimilarity is itself a bisimulation.
- `Bisimilarity.largest_bisimulation`: bisimilarity is the largest bisimulation.
- `Bisimilarity.gfp`: the union of bisimilarity and any bisimulation is equal to bisimilarity.
- `Bisimulation.upTo_bisimulation`: any bisimulation up to bisimilarity is a bisimulation.
- `Bisimulation.bisim_trace_eq`: any bisimulation that relates two states implies that they are
trace equivalent (see `TraceEq`).
- `Bisimilarity.deterministic_bisim_eq_trace_eq`: in a deterministic LTS, bisimilarity and trace
equivalence coincide.

-/

universe u v

section Bisimulation

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- A relation is a bisimulation if, whenever it relates two states in an lts,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related. -/
def Bisimulation (lts : LTS State Label) (r : Rel State State) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ, (
    (∀ s1', lts.tr s1 μ s1' → ∃ s2', lts.tr s2 μ s2' ∧ r s1' s2')
    ∧
    (∀ s2', lts.tr s2 μ s2' → ∃ s1', lts.tr s1 μ s1' ∧ r s1' s2')
  )

/-- Two states are bisimilar if they are related by some bisimulation. -/
inductive Bisimilarity (lts : LTS State Label) : Rel State State where
| bisim (s1 s2 : State) (h : ∃ r : Rel State State, r s1 s2 ∧ Bisimulation lts r) :
  Bisimilarity lts s1 s2

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.
-/
notation s " ~[" lts "] " s' => Bisimilarity lts s s'

/-- Bisimilarity is reflexive. -/
theorem Bisimilarity.refl [DecidableEq State] (s : State) : s ~[lts] s := by
  constructor
  let r := (fun (s1 s2 : State) => if s1 = s2 then True else False)
  exists r
  constructor
  case left =>
    simp [r]
  case right =>
    simp only [Bisimulation]
    intro s1 s2 hr μ
    simp [r] at hr
    constructor
    case left =>
      simp [hr]
      intro s1' htr
      exists s1'
      constructor
      · exact htr
      · simp [r]
    case right =>
      simp [hr]
      intro s1' htr
      exists s1'
      constructor
      · exact htr
      · simp [r]

/-- The inverse of a bisimulation is a bisimulation. -/
theorem Bisimulation.inv (r : Rel State State) (h : Bisimulation lts r) :
  Bisimulation lts r.inv := by
  simp only [Bisimulation] at h
  simp only [Bisimulation]
  intro s1 s2 hrinv μ
  constructor
  case left =>
    intro s1' htr
    specialize h s2 s1 hrinv μ
    have h' := h.2 s1' htr
    obtain ⟨ s2', h' ⟩ := h'
    exists s2'
  case right =>
    intro s2' htr
    specialize h s2 s1 hrinv μ
    have h' := h.1 s2' htr
    obtain ⟨ s1', h' ⟩ := h'
    exists s1'

/-- Bisimilarity is symmetric. -/
theorem Bisimilarity.symm {s1 s2 : State} (h : s1 ~[lts] s2) : s2 ~[lts] s1 := by
  cases h
  rename_i h
  obtain ⟨r, hr, hb⟩ := h
  constructor
  exists r.inv
  constructor
  case left =>
    exact hr
  case right =>
    apply Bisimulation.inv
    exact hb

/-- The composition of two bisimulations is a bisimulation. -/
theorem Bisimulation.comp
  (r1 r2 : Rel State State) (h1 : Bisimulation lts r1) (h2 : Bisimulation lts r2) :
  Bisimulation lts (r1.comp r2) := by
  simp_all only [Bisimulation]
  intro s1 s2 hrc μ
  constructor
  case left =>
    intro s1' htr
    rcases hrc with ⟨sb, hr1, hr2⟩
    specialize h1 s1 sb hr1 μ
    specialize h2 sb s2 hr2 μ
    have h1' := h1.1 s1' htr
    obtain ⟨s1'', h1'tr, h1'⟩ := h1'
    have h2' := h2.1 s1'' h1'tr
    obtain ⟨s2'', h2'tr, h2'⟩ := h2'
    exists s2''
    constructor
    · exact h2'tr
    · simp [Rel.comp]
      exists s1''
  case right =>
    intro s2' htr
    rcases hrc with ⟨sb, hr1, hr2⟩
    specialize h1 s1 sb hr1 μ
    specialize h2 sb s2 hr2 μ
    have h2' := h2.2 s2' htr
    obtain ⟨s2'', h2'tr, h2'⟩ := h2'
    have h1' := h1.2 s2'' h2'tr
    obtain ⟨s1'', h1'tr, h1'⟩ := h1'
    exists s1''
    constructor
    · exact h1'tr
    · simp [Rel.comp]
      exists s2''

/-- Bisimilarity is transitive. -/
theorem Bisimilarity.trans
  {s1 s2 s3 : State} (h1 : s1 ~[lts] s2) (h2 : s2 ~[lts] s3) :
  s1 ~[lts] s3 := by
  obtain ⟨_, _, r1, hr1, hr1b⟩ := h1
  obtain ⟨_, _, r2, hr2, hr2b⟩ := h2
  constructor
  exists r1.comp r2
  constructor
  case left =>
    simp only [Rel.comp]
    exists s2
  case right =>
    apply Bisimulation.comp lts r1 r2 hr1b hr2b

/-- Bisimilarity is an equivalence relation. -/
instance Bisimilarity.eqRel [DecidableEq State] (lts : LTS State Label) :
  Equivalence (Bisimilarity lts) where
  refl := Bisimilarity.refl lts
  symm := Bisimilarity.symm lts
  trans := Bisimilarity.trans lts

/-- Bisimilarity is a bisimulation. -/
theorem Bisimilarity.is_bisimulation : Bisimulation lts (Bisimilarity lts) := by
  simp only [Bisimulation]
  intro s1 s2 h μ
  obtain ⟨_, _, r, hr, hb⟩ := h
  have hrBisim := hb
  simp [Bisimulation] at hb
  specialize hb s1 s2
  constructor
  case left =>
    intro s1' htr
    specialize hb hr μ
    obtain ⟨hb1, hb2⟩ := hb
    specialize hb1 s1' htr
    obtain ⟨s2', htr2, hr2⟩ := hb1
    exists s2'
    constructor
    case left =>
      exact htr2
    case right =>
      constructor
      exists r
  case right =>
    intro s2' htr
    specialize hb hr μ
    obtain ⟨hb1, hb2⟩ := hb
    specialize hb2 s2' htr
    obtain ⟨s1', htr1, hr1⟩ := hb2
    exists s1'
    constructor
    case left =>
      exact htr1
    case right =>
      constructor
      exists r

instance bisimilarityIsBisimulation : Bisimulation lts (Bisimilarity lts) :=
  Bisimilarity.is_bisimulation lts

/-- Bisimilarity is the largest bisimulation. -/
theorem Bisimilarity.largest_bisimulation
  (r : Rel State State) (h : Bisimulation lts r) (s1 s2 : State) :
  r s1 s2 → s1 ~[lts] s2 := by
  intro hr
  constructor
  exists r

/-- Union of two relations.

TODO: move to `Rel`? -/
def Rel.union {α β} (r1 r2 : Rel α β) : Rel α β :=
  fun x y => r1 x y ∨ r2 x y

/-- The union of bisimilarity with any bisimulation is bisimilarity. -/
theorem Bisimilarity.gfp (r : Rel State State) (h : Bisimulation lts r) :
  (Bisimilarity lts).union r = Bisimilarity lts := by
  funext s1 s2
  simp [Rel.union]
  apply Bisimilarity.largest_bisimulation lts r h

/-- The relation `r` 'up to' the relation `s`.

TODO: move to `Rel`? -/
def Rel.upTo {α} (r s : Rel α α) : Rel α α := s.comp (r.comp s)

/-- A relation `r` is a bisimulation up to bisimilarity if, whenever it relates two
states in an lts, the transitions originating from these states mimic each other and the reached
derivatives are themselves related by `r` up to bisimilarity. -/
def BisimulationUpTo (lts : LTS State Label) (r : Rel State State) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ, (
    (∀ s1', lts.tr s1 μ s1' → ∃ s2', lts.tr s2 μ s2' ∧ r.upTo (Bisimilarity lts) s1' s2')
    ∧
    (∀ s2', lts.tr s2 μ s2' → ∃ s1', lts.tr s1 μ s1' ∧ r.upTo (Bisimilarity lts) s1' s2')
  )

/-- Any bisimulation up to bisimilarity is a bisimulation. -/
theorem Bisimulation.upTo_bisimulation (r : Rel State State) (h : BisimulationUpTo lts r) :
  Bisimulation lts (r.upTo (Bisimilarity lts)) := by
  simp [Bisimulation]
  simp [BisimulationUpTo] at h
  intro s1 s2 hr μ
  rcases hr with ⟨s1b, hr1b, s2b, hrb, hr2b⟩
  obtain ⟨_, _, r1, hr1, hr1b⟩ := hr1b
  obtain ⟨_, _, r2, hr2, hr2b⟩ := hr2b
  constructor
  case left =>
    intro s1' htr1
    obtain ⟨s1b', hs1b'tr, hs1b'r⟩ := (hr1b _ _ hr1 μ).1 s1' htr1
    obtain ⟨s2b', hs2b'tr, hs2b'r⟩ := (h s1b s2b hrb μ).1 s1b' hs1b'tr
    obtain ⟨s2', hs2btr, hs2br⟩ := (hr2b _ _ hr2 μ).1 _ hs2b'tr
    exists s2'
    constructor
    case left =>
      exact hs2btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs2b'r
      constructor
      constructor
      · apply Bisimilarity.trans lts (Bisimilarity.largest_bisimulation lts r1 hr1b _ _ hs1b'r)
          hsmidb
      · simp [Rel.comp]
        exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans lts hsmidrb
          apply Bisimilarity.largest_bisimulation lts r2 hr2b s2b' s2' hs2br
  case right =>
    intro s2' htr2
    obtain ⟨s2b', hs2b'tr, hs2b'r⟩ := (hr2b _ _ hr2 μ).2 s2' htr2
    obtain ⟨s1b', hs1b'tr, hs1b'r⟩ := (h s1b s2b hrb μ).2 s2b' hs2b'tr
    obtain ⟨s1', hs1btr, hs1br⟩ := (hr1b _ _ hr1 μ).2 _ hs1b'tr
    exists s1'
    constructor
    case left =>
      exact hs1btr
    case right =>
      obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs1b'r
      simp [Rel.upTo, Rel.comp]
      constructor
      constructor
      · apply Bisimilarity.trans lts (Bisimilarity.largest_bisimulation lts r1 hr1b _ _ _) hsmidb
        · exact hs1br
      · exists smid2
        constructor
        · exact hsmidr
        · apply Bisimilarity.trans lts hsmidrb
          apply Bisimilarity.largest_bisimulation lts r2 hr2b s2b' s2' _
          exact hs2b'r

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions. -/
theorem Bisimulation.bisim_trace
  (s1 s2 : State) (r : Rel State State) (hb : Bisimulation lts r) (hr : r s1 s2) :
  ∀ μs s1', lts.mtr s1 μs s1' → ∃ s2', lts.mtr s2 μs s2' ∧ r s1' s2' := by
  intro μs
  induction μs generalizing s1 s2
  case nil =>
    intro s1' hmtr1
    exists s2
    cases hmtr1
    constructor
    constructor
    exact hr
  case cons μ μs' ih =>
    intro s1' hmtr1
    cases hmtr1
    case stepL s1'' htr hmtr =>
      simp [Bisimulation] at hb
      specialize hb s1 s2 hr μ
      have hf := hb.1 s1'' htr
      obtain ⟨s2'', htr2, hb2⟩ := hf
      specialize ih s1'' s2'' hb2 s1' hmtr
      obtain ⟨s2', hmtr2, hr'⟩ := ih
      exists s2'
      constructor
      case left =>
        constructor
        · exact htr2
        · exact hmtr2
      case right =>
        exact hr'

/-- Any bisimulation implies trace equivalence. -/
theorem Bisimulation.bisim_trace_eq
  (s1 s2 : State) (r : Rel State State) (hb : Bisimulation lts r) (hr : r s1 s2) :
  s1 ~tr[lts] s2 := by
  simp [TraceEq, LTS.traces, setOf]
  funext μs
  simp only [eq_iff_iff]
  constructor
  case mp =>
    intro h
    obtain ⟨s1', h⟩ := h
    obtain ⟨s2', hmtr⟩ := @Bisimulation.bisim_trace State Label lts s1 s2 r hb hr μs s1' h
    exists s2'
    exact hmtr.1
  case mpr =>
    intro h
    obtain ⟨s2', h⟩ := h
    have hinv := @Bisimulation.inv State Label lts r hb
    obtain ⟨s1', hmtr⟩ := @Bisimulation.bisim_trace State Label lts s2 s1 r.inv hinv hr μs s2' h
    exists s1'
    exact hmtr.1

/-- Bisimilarity implies trace equivalence. -/
theorem Bisimilarity.bisim_trace_eq (s1 s2 : State) (h : s1 ~[lts] s2) :
  s1 ~tr[lts] s2 := by
  cases h
  case bisim hb =>
    obtain ⟨r, hr, hb⟩ := hb
    apply Bisimulation.bisim_trace_eq lts s1 s2 r hb hr

/-- In a deterministic LTS, trace equivalence is a bisimulation. -/
theorem Bisimulation.deterministic_trace_eq_is_bisim
  (lts : LTS State Label) (hdet : lts.Deterministic) :
  (Bisimulation lts (TraceEq lts)) := by
  simp only [Bisimulation]
  intro s1 s2 hteq μ
  constructor
  case left =>
    apply TraceEq.deterministic_sim lts hdet s1 s2 hteq
  case right =>
    intro s2' htr
    apply TraceEq.symm at hteq
    have h := TraceEq.deterministic_sim lts hdet s2 s1 hteq μ s2' htr
    obtain ⟨s1', h⟩ := h
    exists s1'
    constructor
    case left =>
      exact h.1
    case right =>
      apply h.2.symm

/-- In a deterministic LTS, trace equivalence implies bisimilarity. -/
theorem Bisimilarity.deterministic_trace_eq_bisim
  (lts : LTS State Label) (hdet : lts.Deterministic) (s1 s2 : State) (h : s1 ~tr[lts] s2) :
  (s1 ~[lts] s2) := by
  -- simp [TraceEq, LTS.traces, setOf] at h
  -- simp [LTS.Deterministic] at hdet
  constructor
  exists TraceEq lts
  constructor
  case left =>
    exact h
  case right =>
    apply Bisimulation.deterministic_trace_eq_is_bisim lts hdet

/-- In a deterministic LTS, bisimilarity and trace equivalence coincide. -/
theorem Bisimilarity.deterministic_bisim_eq_trace_eq
  (lts : LTS State Label) (hdet : lts.Deterministic) :
  Bisimilarity lts = TraceEq lts := by
  funext s1 s2
  simp [eq_iff_iff]
  constructor
  case mp =>
    apply Bisimilarity.bisim_trace_eq
  case mpr =>
    apply Bisimilarity.deterministic_trace_eq_bisim lts hdet

end Bisimulation
