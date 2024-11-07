-- `Mathlib/AlgebraicGeometry/Fiber
import Mathlib.AlgebraicGeometry.PullbackCarrier

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

def Scheme.Hom.fiber (f : X.Hom Y) (y : Y) : Scheme :=
  pullback f (Y.fromSpecResidueField y)

def Scheme.Hom.fiberι (f : X.Hom Y) (y : Y) : f.fiber y ⟶ X :=
  pullback.fst _ _

def Scheme.Hom.fiberToResidueField (f : X.Hom Y) (y : Y) :
    f.fiber y ⟶ Spec (Y.residueField y) :=
  pullback.snd _ _

lemma Scheme.Hom.fiber_isPullback (f : X.Hom Y) (y : Y) :
    IsPullback (f.fiberι y) (f.fiberToResidueField y) f (Y.fromSpecResidueField y) :=
  IsPullback.of_hasPullback _ _

lemma Scheme.Hom.range_fiberι (f : X.Hom Y) (y : Y) :
    Set.range (f.fiberι y).1.base = f.1.base ⁻¹' {y} := by
  dsimp [fiber, fiberι]
  rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

end AlgebraicGeometry
