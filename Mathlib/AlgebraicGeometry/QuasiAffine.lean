/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# Quasi-affine schemes

## Main results
- `IsQuasiAffine`:
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
Despite the definition, any quasi-compact locally closed subscheme of an affine scheme is
quasi-affine. See `IsQuasiAffine.of_isImmersion` -/
@[stacks 01P6]
class IsQuasiAffine (X : Scheme.{u}) : Prop extends
  CompactSpace X, IsOpenImmersion X.toSpecΓ

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := low) [IsAffine X] : X.IsQuasiAffine where

instance (priority := low) [X.IsQuasiAffine] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from X.toSpecΓ]
    infer_instance

/-- Any quasicompact locally closed subscheme of an quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : IsImmersion (X.toSpecΓ ≫ Spec.map (Hom.appTop f)) := by
    rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  have : QuasiCompact X.toSpecΓ := (quasiCompact_over_affine_iff _).mpr ‹_›
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

end AlgebraicGeometry.Scheme
