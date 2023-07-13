import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal


open Affine

variable {𝕜 : Type _} {V : Type _} {P : Type _} [IsROrC 𝕜]

variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [AffineSpace V P]

namespace AffineSubspace

/-- Orthogonal complement to an affine subspace passing through a given point. -/
def orthogonal (s : AffineSubspace 𝕜 P) (b : P) : AffineSubspace 𝕜 P := mk' b s.directionᗮ

end AffineSubspace


namespace AffineSubspace

/-- The proposition that two affine subspaces are orthogonal. -/
def IsOrtho (s t : AffineSubspace 𝕜 P) : Prop := s.direction ⟂ t.direction

/- Ambiguous
@[inherit_doc]
infixl:50 " ⟂ᵥ " => IsOrtho -/

end AffineSubspace
