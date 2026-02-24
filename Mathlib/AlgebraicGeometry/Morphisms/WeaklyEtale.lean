/-
Copyright (c) 2026 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!

# Weakly étale morphisms

A morphism of schemes is weakly étale if it is flat and its diagonal is flat. As
the name suggests any étale morphism is weakly étale and every weakly étale
morphism of finite presentation is étale.

## Main definitions

- `AlgebraicGeometry.WeaklyEtale`: The class of weakly étale morphisms.

## TODOs

- When weakly étale ring homomorphisms are in mathlib, show
  `HasRingHomProperty WeaklyEtale RingHom.WeaklyEtale` (@chrisflav).
- Deduce from this that weakly étale morphisms of finite presentation are étale (@chrisflav).

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is weakly étale if it is flat and the diagonal map is flat. -/
@[mk_iff, stacks 094P]
class WeaklyEtale : Prop where
  flat : Flat f := by infer_instance
  flat_diagonal : Flat (pullback.diagonal f) := by infer_instance

namespace WeaklyEtale

attribute [instance] flat flat_diagonal

theorem weaklyEtale_eq_flat_inf_diagonal_flat :
    @WeaklyEtale = (@Flat ⊓ MorphismProperty.diagonal @Flat : MorphismProperty Scheme.{u}) := by
  ext
  exact weaklyEtale_iff _

/-- Etale morphisms are weakly étale. -/
instance (priority := 900) [Etale f] : WeaklyEtale f where

instance : MorphismProperty.RespectsIso @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

instance : MorphismProperty.IsMultiplicative @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

instance [WeaklyEtale f] [WeaklyEtale g] : WeaklyEtale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

instance : IsZariskiLocalAtSource @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

instance : IsZariskiLocalAtTarget @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [WeaklyEtale g] :
    WeaklyEtale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [WeaklyEtale f] :
    WeaklyEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [WeaklyEtale f] : WeaklyEtale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [WeaklyEtale f] :
    WeaklyEtale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/- This proof is by `inferInstance` and the argument goes through
`IsImmersion (diagonal f) → Mono (diagonal f) → IsIso (diagonal (diagonal f))`. -/
instance (f : X ⟶ Y) [WeaklyEtale f] : WeaklyEtale (pullback.diagonal f) where

@[stacks 0951]
instance : MorphismProperty.HasOfPostcompProperty @WeaklyEtale @WeaklyEtale := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f hf
  exact inferInstanceAs <| WeaklyEtale (pullback.diagonal f)

lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [WeaklyEtale (f ≫ g)] [WeaklyEtale g] : WeaklyEtale f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

end WeaklyEtale

end AlgebraicGeometry
