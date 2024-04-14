import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Discrete.LocallyConstant

universe u

open CategoryTheory Limits

namespace Condensed

variable {C : Type*} [Category C]
  [HasWeakSheafify (coherentTopology CompHaus) C] (X : Condensed C)

class IsDiscrete : Prop where
  isoDiscrete : ∃ (X' : C), Nonempty (X ≅ (discrete C).obj X')

end Condensed

namespace CondensedSet

open Condensed

variable {X : CondensedSet.{u}}

theorem isDiscrete_iff_nonempty_iso_LC : IsDiscrete X ↔ ∃ X', Nonempty (X ≅ LC'.obj X') := sorry

theorem isDiscrete_of_isLeftKanExtendedAlong (h : ∀ S : Profinite.{u}, IsLeftKanExtendedAlong
  FintypeCat.toProfinite.op (profiniteToCompHaus.op ⋙ X.val)) : IsDiscrete X := sorry

theorem isLeftKanExtendedAlong_of_isDiscrete [IsDiscrete X] (S : Profinite.{u}) :
  IsLeftKanExtendedAlong FintypeCat.toProfinite.op (profiniteToCompHaus.op ⋙ X.val) := sorry

theorem isDiscrete_of_isColimit_mapCone (h : ∀ S : Profinite.{u},
    IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op) :
    IsDiscrete X :=
  sorry

def isColimitMapConeOfIsDiscrete [IsDiscrete X] (S : Profinite.{u}) :
    IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op := sorry
