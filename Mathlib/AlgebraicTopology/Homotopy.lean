import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open Simplicial SimplexCategory
open CategoryTheory Limits

namespace CategoryTheory

-- TODO: Do we have such things somewhere?

def isTerminalHom {C : Type _} [Category C] (X Y : C) (hY : IsTerminal Y) :
    IsTerminal (X ⟶ Y) :=
  letI : ∀ (W : Type _), Unique (W ⟶ (X ⟶ Y)) := fun W =>
    { default := fun _ => hY.from _
      uniq := fun a => by ext ; apply hY.hom_ext }
  IsTerminal.ofUnique _

def Functor.isTerminalOfObjIsTerminal {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) (hF : ∀ X : C, IsTerminal (F.obj X)) :
    IsTerminal F :=
  letI : ∀ (G : C ⥤ D), Unique (G ⟶ F) := fun _ => {
    default := {
      app := fun _ => (hF _).from _
      naturality := fun _ _ _ => (hF _).hom_ext _ _ }
    uniq := fun _ => NatTrans.ext _ _ <| funext fun _ => (hF _).hom_ext _ _ }
  IsTerminal.ofUnique _

end CategoryTheory

namespace SimplexCategory

def isTerminalZero : IsTerminal ([0] : SimplexCategory) :=
  letI : ∀ t : SimplexCategory, Unique (t ⟶ [0]) := fun t => {
    default := SimplexCategory.Hom.mk <| OrderHom.const _ 0
    uniq := fun m => SimplexCategory.Hom.ext _ _ <| OrderHom.ext _ _ <|
      funext fun _ => Fin.ext <| by simp }
  IsTerminal.ofUnique _

end SimplexCategory

namespace SSet

universe u

class IsKan (X : SSet) : Prop where
  cond : ∀ n i (f : Λ[n,i] ⟶ X), ∃ (g : Δ[n] ⟶ X), f = hornInclusion _ _ ≫ g

def 𝕀 : SSet.{0} := Δ[1]
def pt : SSet.{0} := Δ[0]

def i0 : pt ⟶ 𝕀 := SSet.standardSimplex.map (δ 1)
def i1 : pt ⟶ 𝕀 := SSet.standardSimplex.map (δ 0)

def ptIsTerminal : IsTerminal pt := Functor.isTerminalOfObjIsTerminal _ <|
  fun t => show IsTerminal (t.unop ⟶ [0]) from isTerminalHom _ _ isTerminalZero

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

structure Path {X : SSet.{0}} (a b : pt ⟶ X) where
  p : 𝕀 ⟶ X
  hp0 : i0 ≫ p = a
  hp1 : i1 ≫ p = b

def Path.rfl {X : SSet.{0}} (a : pt ⟶ X) : Path a a where
  p := ptIsTerminal.from _ ≫ a
  hp0 := by slice_lhs 1 2 => simp
  hp1 := by slice_lhs 1 2 => simp

def Path.trans {X : SSet.{0}} {a b c : pt ⟶ X} [IsKan X] :
  Path a b → Path b c → Path a c := sorry

def Path.symm {X : SSet.{0}} {a b : pt ⟶ X} [IsKan X] :
  Path a b → Path b a := sorry

/-
TODO: Define this in terms of paths.
structure homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) where
  F : 𝕀 ⨯ X ⟶ Y
  F0 : (leftUnitor X).inv ≫ (prod.map i0 (𝟙 X)) ≫ F = f
  F1 : (leftUnitor X).inv ≫ (prod.map i1 (𝟙 X)) ≫ F = g
-/

--class HomotopyInvariant {X : SSet.{0}} (motive : ⦃a b : pt ⟶ X⦄ → Path a b → Sort u) where
--  ind : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ⦃x y : pt ⟶ X⦄ → (p : Path x y) → motive p
--  ind_rfl : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ind rfl (Path.rfl x) = rfl x

end SSet
