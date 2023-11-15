import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Limits Simplicial SimplexCategory

variable (X Y X' Y': SSet) (m n : ℕ) (f : X ⟶ Y)

namespace CategoryTheory

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

def d0 : Δ[0] ⟶ Δ[1] := SSet.standardSimplex.map (δ 1)
def d1 : Δ[0] ⟶ Δ[1] := SSet.standardSimplex.map (δ 0)

def ptIsTerminal : IsTerminal Δ[0] := Functor.isTerminalOfObjIsTerminal _ <|
  fun t => show IsTerminal (t.unop ⟶ [0]) from isTerminalHom _ _ isTerminalZero

def binaryFan (X : SSet.{0}) : BinaryFan Δ[0] X :=
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
def leftUnitor (X : SSet.{0}) : Δ[0] ⨯ X ≅ X :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitBinaryFan X)

structure Path {X : SSet.{0}} (a b : Δ[0] ⟶ X) where
  p : Δ[1] ⟶ X
  hp0 : d0 ≫ p = a
  hp1 : d1 ≫ p = b

def Path.rfl {X : SSet.{0}} (a : Δ[0] ⟶ X) : Path a a where
  p := ptIsTerminal.from _ ≫ a
  hp0 := by slice_lhs 1 2 => simp
  hp1 := by slice_lhs 1 2 => simp

def Path.trans {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b c → Path a c := sorry

def Path.symm {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b a := sorry

noncomputable
def ProdObjIso (X Y : SSet) (n) : (X ⨯ Y).obj n ≅ (X.obj n × Y.obj n) :=
  show ((evaluation _ _).obj n).obj (X ⨯ Y) ≅ _ from
  preservesLimitIso _ _ ≪≫ Limits.HasLimit.isoOfNatIso
    (Limits.pairComp X Y ((evaluation SimplexCategoryᵒᵖ Type).obj n))
    ≪≫ (Types.binaryProductIso _ _)

/-
example (X Y : SSet) (n) : (ProdObjIso X Y n).hom ≫ Limits.prod.fst = (Limits.prod.fst (X := X) (Y := Y)).app n := by
  dsimp [ProdObjIso]
  aesop
-/

def Prod (X Y : SSet) : SSet where
  obj n := X.obj n × Y.obj n
  map := by
    rintro m n f a
    exact ⟨X.map f a.1, Y.map f a.2⟩

noncomputable
def ProdIso (X Y : SSet) : X ⨯ Y ≅ Prod X Y where
  hom := {
    app := fun _ => (ProdObjIso _ _ _).hom
    naturality := by
      intro m n f
      ext a
      simp
      dsimp [Prod, ProdObjIso]
      sorry
  }
  inv := {
    app := fun _ => (ProdObjIso _ _ _).inv
    naturality := by
      sorry
  }
  hom_inv_id := sorry
  inv_hom_id := sorry

noncomputable
def IHom (X Y : SSet) : SSet where
  obj n := X ⨯ (standardSimplex.obj n.unop) ⟶ Y
  map := by
    rintro m n f F
    refine {
      app := fun k => (prod.map (𝟙 X) (standardSimplex.map f.unop)).app k ≫ F.app k
    }
  map_id := by
    intro n
    ext a m h
    simp only [unop_id, smallCategory_id, Hom.id, types_comp_apply, types_id_apply]
    suffices : (prod.map (𝟙 X) (standardSimplex.map (Hom.mk OrderHom.id))).app m h = h
    rw [this]
    suffices : (prod.map (𝟙 X) (standardSimplex.map (Hom.mk OrderHom.id))).app m = id
    rw [this]
    rfl

    aesop_cat

  map_comp := sorry

/-
def IHom (X Y : SSet) : SSet where
  obj n := Prod X (standardSimplex.obj n.unop) ⟶ Y
  map := by
    rintro m n f F
    refine {
      app := by
        rintro k ⟨a, b⟩
        apply F.app k
        refine ⟨a, ?_⟩
        exact ((standardSimplex.map f.unop).app k) b
      naturality := _
    }
  map_id := sorry
  map_comp := sorry
-/

/-
TODO: Define this in terms of paths.
structure homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) where
  F : Δ[1] ⨯ X ⟶ Y
  F0 : (leftUnitor X).inv ≫ (prod.map d0 (𝟙 X)) ≫ F = f
  F1 : (leftUnitor X).inv ≫ (prod.map d1 (𝟙 X)) ≫ F = g
-/

--class HomotopyInvariant {X : SSet.{0}} (motive : ⦃a b : pt ⟶ X⦄ → Path a b → Sort u) where
--  ind : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ⦃x y : pt ⟶ X⦄ → (p : Path x y) → motive p
--  ind_rfl : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ind rfl (Path.rfl x) = rfl x

end section
