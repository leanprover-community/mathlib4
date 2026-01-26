
/-!
# Affine monoids embed into `ℤⁿ`

This file proves that finitely generated cancellative torsion-free commutative monoids embed into
`ℤⁿ` for some `n`.
-/

public section

open Algebra AddLocalization Function

variable {M : Type*} [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

namespace AffineAddMonoid

variable (M) in
/-- The dimension of an affine monoid `M`, namely the minimum `n` for which `M` embeds into `ℤⁿ`. -/
noncomputable abbrev dim := Module.finrank ℤ <| GrothendieckAddGroup M

variable (M) in
/-- An arbitrary embedding of an affine monoid `M` into `ℤ ^ dim M`. -/
noncomputable def embedding : M →+ FreeAbelianGroup (Fin (dim M)) :=
  .comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom <|
    .comp (Module.finBasis ℤ _).repr.toAddMonoidHom
      (addMonoidOf ⊤).toAddMonoidHom

lemma embedding_injective : Injective (embedding M) := by
  simpa [embedding] using mk_left_injective 0

end AffineAddMonoid
