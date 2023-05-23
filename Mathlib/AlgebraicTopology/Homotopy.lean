import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open Simplicial SimplexCategory
open CategoryTheory Limits

namespace CategoryTheory

def Functor.isTerminalOfObjIsTerminal {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) (hF : ∀ X : C, IsTerminal (F.obj X)) :
  IsTerminal F := sorry

end CategoryTheory

namespace SSet

universe u

def 𝕀 : SSet.{0} := Δ[1]
def pt : SSet.{0} := Δ[0]

def i0 : pt ⟶ 𝕀 := SSet.standardSimplex.map (δ 1)
def i1 : pt ⟶ 𝕀 := SSet.standardSimplex.map (δ 0)

def ptIsTerminal : IsTerminal pt := Functor.isTerminalOfObjIsTerminal _ <|
  fun t => show IsTerminal (t.unop ⟶ [0]) by sorry

def binaryFan (X : SSet.{0}) : BinaryFan pt X :=
  BinaryFan.mk (ptIsTerminal.from X) (𝟙 X)

def isLimitBinaryFan (X : SSet.{0}) : IsLimit (binaryFan X) where
  lift := fun (S : BinaryFan _ _) => S.snd
  fac := fun (S : BinaryFan _ _) => by
    rintro ⟨(_|_)⟩
    · apply ptIsTerminal.hom_ext
    · dsimp [binaryFan] ; simp
  uniq := fun (S : BinaryFan _ _) m hm => by
    specialize hm ⟨WalkingPair.right⟩
    simpa [binaryFan] using hm

noncomputable
def leftUnitor (X : SSet.{0}) : pt ⨯ X ≅ X :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitBinaryFan X)

structure homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) where
  F : 𝕀 ⨯ X ⟶ Y
  F0 : (leftUnitor X).inv ≫ (prod.map i0 (𝟙 X)) ≫ F = f
  F1 : (leftUnitor X).inv ≫ (prod.map i1 (𝟙 X)) ≫ F = g

end SSet
