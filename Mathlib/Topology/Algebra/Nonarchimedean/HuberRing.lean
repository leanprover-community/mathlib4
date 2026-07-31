/-
Copyright (c) 2026 sfingali. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sfingali
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Huber (f-adic) rings

A topological ring `A` is *Huber* (Wedhorn's *f-adic*) if it contains an open
subring `A₀` whose subspace topology is the `I`-adic topology for a finitely
generated ideal `I` of `A₀`; such a subring is a *ring of definition* and the
pair `(A₀, I)` is a *pair of definition*.

## Main definitions
* `HuberRing.RingOfDefinition` — a ring of definition of `A`: an open subring
  `A₀ ⊆ A` whose subspace topology is the `I`-adic topology for a finitely
  generated ideal `I` of `A₀`. (Records the pair of definition `(A₀, I)`.)
* `HuberRing.IsHuberRing` — a topological ring admitting a ring of definition.

## Main results
* `HuberRing.ringOfDefinition_iff_open_adic` — Wedhorn, Lemma 6.2 (a) ↔ (b),
  p. 46: a subring is a ring of definition iff it is open and adic.

## References
* [Wedhorn] T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, Prop. and Def. 6.1,
  Lemma 6.2, Cor. 6.4 (pp. 46–47). Wedhorn calls Huber rings *f-adic*; the
  modern name (Scholze) is used here for consistency with the Huber pair and
  adic space layers.
-/

namespace HuberRing

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A ring of definition of a topological ring `A`: an open subring `A₀` of `A`
whose subspace topology is the `I`-adic topology for a finitely generated ideal
`I` of `A₀`. (Wedhorn, Prop. and Def. 6.1(ii), p. 46: "A contains an open subring
A₀ such that the subspace topology on A₀ is I-adic, where I is a finitely
generated ideal of A₀.") -/
structure RingOfDefinition (A : Type*) [CommRing A] [TopologicalSpace A] where
  subring : Subring A
  isOpen_subring : IsOpen (subring : Set A)
  I : Ideal subring
  I_fg : I.FG
  isIdealAdic : IsAdic I

/-- A topological ring is Huber (f-adic) if it admits a ring of definition.
(Wedhorn, Prop. and Def. 6.1, p. 46.) -/
def IsHuberRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop :=
  Nonempty (RingOfDefinition A)

/-- A ring of definition witnesses that `A` is a Huber ring. -/
theorem IsHuberRing.of_ringOfDefinition (rd : RingOfDefinition A) : IsHuberRing A :=
  ⟨rd⟩

/-- Wedhorn, Lemma 6.2 (a) ↔ (b), p. 46: a subring `S` of `A` is a ring of
definition iff it is open in `A` and its subspace topology is `I`-adic for some
finitely generated ideal `I` of `S`. -/
theorem ringOfDefinition_iff_open_adic (S : Subring A) :
    (∃ rd : RingOfDefinition A, rd.subring = S) ↔
      IsOpen (S : Set A) ∧ ∃ I : Ideal S, I.FG ∧ IsAdic I := by
  constructor
  · rintro ⟨rd, rfl⟩
    exact ⟨rd.isOpen_subring, rd.I, rd.I_fg, rd.isIdealAdic⟩
  · rintro ⟨hopen, I, hfg, hadic⟩
    let rd : RingOfDefinition A :=
      { subring := S, isOpen_subring := hopen, I := I, I_fg := hfg,
        isIdealAdic := hadic }
    exact ⟨rd, rfl⟩

end HuberRing
