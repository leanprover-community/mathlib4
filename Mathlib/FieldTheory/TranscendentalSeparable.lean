/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Transcendental separable extensions

In this file we introduce the concept of separably generated field extensions and
transcendental separable field extensions.

# Main definitions and results

* `Algebra.IsSeparablyGenerated` : A field extension is separably generated if there exists
  an transcendental basis such that the extension above it is separable.

* `Algebra.IsTranscendentalSeparable` : A field extension is transcendental separable if
  every finitely generated subextension is separably generated.

-/

universe u v w

@[expose] public section

open TensorProduct

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- A field extension is separably generated if there exists an transcendental basis such that
the extension above it is separable. -/
@[mk_iff, stacks 030O "Part 1"]
class Algebra.IsSeparablyGenerated : Prop where
  isSeparable' : ∃ (ι : Type v) (f : ι → K),
    IsTranscendenceBasis k f ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (Set.range f)) K

variable {k K} in
lemma Algebra.isSeparablyGenerated_of_equiv {K' : Type w} [Field K'] [Algebra k K'] (e : K ≃ₐ[k] K')
    [Algebra.IsSeparablyGenerated k K] : Algebra.IsSeparablyGenerated k K' := by
  rcases ‹Algebra.IsSeparablyGenerated k K› with ⟨ι, f, isT, sep⟩
  have : Small.{w} ι := small_of_injective (e.injective.comp isT.1.injective)
  let g := (e ∘ f) ∘ (equivShrink ι).symm
  use Shrink.{w} ι, g, (e.isTranscendenceBasis isT).comp_equiv (equivShrink ι).symm
  have eq : (IntermediateField.adjoin k (Set.range f)).map e =
    (IntermediateField.adjoin k (Set.range g)) := by
    simp [IntermediateField.adjoin_map, g, Set.range_comp e f]
  let e' := ((IntermediateField.adjoin k (Set.range f)).equivMap e.toAlgHom).trans
    (IntermediateField.equivOfEq eq)
  exact Algebra.IsSeparable.of_equiv_equiv e'.toRingEquiv e.toRingEquiv rfl

/-- A field extension is transcendental separable if every finitely generated subextension is
separably generated. -/
@[mk_iff, stacks 030O "Part 2"]
class Algebra.IsTranscendentalSeparable : Prop where
  forall_isSeparablyGenerated : ∀ (A' : IntermediateField k K),
    Algebra.EssFiniteType k A' → Algebra.IsSeparablyGenerated k A'

end
