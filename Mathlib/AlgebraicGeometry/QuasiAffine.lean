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
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
  This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion. -/
@[stacks 01P6]
class IsQuasiAffine (X : Scheme.{u}) : Prop extends
  CompactSpace X, IsImmersion X.toSpecΓ

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := low) [IsAffine X] : X.IsQuasiAffine where

instance (priority := low) [X.IsQuasiAffine] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from X.toSpecΓ]
    infer_instance

instance [X.IsQuasiAffine] : IsOpenImmersion X.toSpecΓ := by
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

/-- Any quasicompact locally closed subscheme of a quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  wlog hY : IsAffine Y
  · refine @this _ _ (f ≫ Y.toSpecΓ) ?_ ?_ _ ?_ <;> clear this <;> infer_instance
  have : QuasiCompact f := by rwa [quasiCompact_iff_compactSpace]
  have : IsAffine f.image :=
    HasAffineProperty.iff_of_isAffine.mp (inferInstanceAs (IsAffineHom f.imageι))
  exact .of_isOpenImmersion f.toImage

end AlgebraicGeometry.Scheme
