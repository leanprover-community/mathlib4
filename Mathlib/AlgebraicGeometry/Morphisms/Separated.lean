/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immmersion.

## TODO

- Show separated is stable under composition and base change (this is immediate if
  we show that closed immersions are stable under base change).
- Show separated is local at the target.
- Show affine morphisms are separated.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is separated if the diagonal map is a closed immersion. -/
@[mk_iff]
class IsSeparated (f : X ⟶ Y) : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  diagonalClosedImmersion : IsClosedImmersion (pullback.diagonal f)

namespace IsSeparated

attribute [instance] diagonalClosedImmersion

theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

/-- Monomorphisms are separated. -/
instance (priority := 900) separatedOfMono {X Y : Scheme} (f : X ⟶ Y) [Mono f] :
    IsSeparated f :=
  ⟨inferInstance⟩

theorem respectsIso : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  apply MorphismProperty.RespectsIso.diagonal
  exact IsClosedImmersion.respectsIso

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsSeparated f] : QuasiSeparated f where
  diagonalQuasiCompact := inferInstance

end IsSeparated

end AlgebraicGeometry
