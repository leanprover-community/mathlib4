-- `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/--
move to `PrimeSpectrum/Basic`

Uses `Ideal.exists_minimalPrimes_comap_eq` and `Ideal.exists_minimalPrimes_le`

-/
lemma PrimeSpectrum.isClosed_range_of_stableUnderSpecialization
    {R S} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : StableUnderSpecialization (Set.range (comap f))) :
    IsClosed (Set.range (comap f)) := by
  rw [isClosed_iff_zeroLocus]
  use (RingHom.ker f)
  sorry

namespace AlgebraicGeometry

open MorphismProperty (topologically)

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Best proved using #14428 -/
lemma isCompact_iff_exists {U : Opens X} :
    IsCompact (U : Set X) ↔
      ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X), Set.range f.1.base = U := sorry

/--
use `isCompact_iff_exists` to reduce to range and use `PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`.

https://stacks.math.columbia.edu/tag/01K9
-/
private lemma isClosedMap_iff_isSpecializingMap_aux {R} (f : X ⟶ Spec R) [QuasiCompact f] :
    IsClosedMap f.1.base ↔ SpecializingMap f.1.base := sorry

/--
use `isClosedMap_iff_isSpecializingMap_aux` and the fact that both sides are local at target.
(maybe postpone this until refactor lands)

https://stacks.math.columbia.edu/tag/01K9
-/
lemma isClosedMap_iff_specializingMap [QuasiCompact f] :
    IsClosedMap f.1.base ↔ SpecializingMap f.1.base := by
  show topologically @IsClosedMap f ↔ topologically @SpecializingMap f
  sorry

/--
use `isClosedMap_iff_specializingMap`
-/
lemma universallyClosed_iff_specializingMap [QuasiCompact f] :
    UniversallyClosed f ↔ (topologically @SpecializingMap).universally f := sorry

/--
For a (formalizable) proof, see https://imgur.com/a/nTDzDFj.

inspired by
https://mathoverflow.net/questions/23337/is-a-universally-closed-morphism-of-schemes-quasi-compact/23528#23528
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := sorry

/--
Use `compactSpace_of_universallyClosed` and `universallyClosed_stableUnderBaseChange` and
`Scheme.Hom.range_fiberι` and `isProperMap_iff_isClosedMap_and_compact_fibers`
-/
lemma isProperMap_of_universallyClosed [UniversallyClosed f] : IsProperMap f.1.base := sorry

/--
Use `IsProperMap.isCompact_preimage`.
This holds for any map between topological spaces. Maybe generalize.
-/
instance (priority := 900) [UniversallyClosed f] : QuasiCompact f := sorry

/-- needs the instance above and `universallyClosed_iff_specializingMap`. -/
lemma universallyClosed_eq_universallySpecializing :
    @UniversallyClosed = (topologically @SpecializingMap).universally ⊓ @QuasiCompact := sorry

end AlgebraicGeometry
