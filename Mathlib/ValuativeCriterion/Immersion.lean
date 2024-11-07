-- `Mathlib/AlgebraicGeometry/Morphisms/Immersion
import Mathlib

/-
This is a stub. I(@erdOne) am working towards a better def via #14748 and #14377.
Feel free to tackle these sorries though. They will be useful regardless.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- Some of these belongs in `AlgebraicGeometry/Pullbacks`
namespace Scheme.Pullback

variable (𝒰 : Y.OpenCover) (𝒱 : ∀ i, (pullback f (𝒰.map i)).OpenCover)

/-
Given `𝒰 i` covering `Y` and `𝒱 i j` covering `𝒰 i`, this is the open cover
`𝒱 i j₁ ×_{𝒰 i} 𝒱 i j₂` ranging over all `i`, `j₁`, `j₂`.
-/
noncomputable
def diagonalCover : (pullback.diagonalObj f).OpenCover :=
(Scheme.Pullback.openCoverOfBase 𝒰 f f).bind
  (fun i ↦ Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒱 i) (pullback.snd _ _) (pullback.snd _ _))

/-- The image of `𝒱 i j₁ ×_{𝒰 i} 𝒱 i j₂` in `diagonalCover` with `j₁ = j₂`  -/
noncomputable
def diagonalCoverDiagonal : (pullback.diagonalObj f).Opens :=
⨆ i : Σ i, (𝒱 i).J, ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange

-- by def
lemma diagonalCover_map (I) : (diagonalCover f 𝒰 𝒱).map I =
    pullback.map _ _ _ _
    ((𝒱 I.fst).map _ ≫ pullback.fst _ _) ((𝒱 I.fst).map _ ≫ pullback.fst _ _) (𝒰.map _)
    (by simp only [Category.assoc, pullback.condition])
    (by simp only [Category.assoc, pullback.condition]) := by
  ext1 <;> simp [diagonalCover]

/--
Needs `Scheme.Pullback.range_map`

inspired by https://stacks.math.columbia.edu/tag/0DVA
-/
lemma diagonalCoverDiagonal_eq_top_of_injective (hf : Function.Injective f.1.base) :
    diagonalCoverDiagonal f 𝒰 𝒱 = ⊤ := sorry

/--
Needs description of the underlying space of `X ×ₛ Y`
-/
lemma range_diagonal_subset_diagonalCoverDiagonal :
    Set.range (pullback.diagonal f).base ⊆ (diagonalCoverDiagonal f 𝒰 𝒱).1 := sorry

-- by category theory
def diagonalRestrictIsoDiagonal (i j) :
    Arrow.mk (pullback.diagonal f ∣_ ((diagonalCover f 𝒰 𝒱).map ⟨i, j, j⟩).opensRange) ≅
    Arrow.mk (pullback.diagonal ((𝒱 i).map j ≫ pullback.snd _ _)) := sorry

/-- By `IsClosedImmersion` is local at target and `diagonalRestrictIsoDiagonal` -/
lemma isClosedImmersion_diagonal_restrict_aux
    (H : ∀ i j, IsClosedImmersion (pullback.diagonal ((𝒱 i).map j ≫ pullback.snd _ _))) :
  IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonal f 𝒰 𝒱) := sorry

/-- By `isClosedImmersion_diagonal_restrict` and
`IsClosedImmersion (pullback.diagonal f)` for affine `f` -/
instance isClosedImmersion_diagonal_restrict :
  IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonal f 𝒰 𝒱) := sorry

end Scheme.Pullback

/--
By `isClosedImmersion_diagonal_restrict` and `range_diagonal_subset_diagonalCoverDiagonal`.

https://stacks.math.columbia.edu/tag/01KJ
-/
instance : IsImmersion (pullback.diagonal f) := sorry

/--
By `isClosedImmersion_diagonal_restrict` and `diagonalCoverDiagonal_eq_top_of_injective`.

https://stacks.math.columbia.edu/tag/0DVA
-/
lemma isClosedImmersion_diagonal_of_injective (hf : Function.Injective f.base) :
    IsClosedImmersion (pullback.diagonal f) := sorry

end AlgebraicGeometry
