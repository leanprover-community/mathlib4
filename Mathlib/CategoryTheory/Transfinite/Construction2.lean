import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.Order.CompleteLattice
import Mathlib.Order.InitialSeg

set_option autoImplicit false

universe v u

local notation C " ~> " D => C ⥤ D
local notation "ID" => CategoryTheory.CategoryStruct.id  -- type as \b1

open CategoryTheory Limits

section Prefix

def Prefix (γ δ : Type v) [PartialOrder γ] [PartialOrder δ] : Type v :=
InitialSeg ((· < ·) : γ → γ → Prop) ((· < ·) : δ → δ → Prop)

instance (γ δ : Type v) [PartialOrder γ] [PartialOrder δ] : CoeFun (Prefix γ δ) (fun _ => γ → δ) where
  coe ι := ι.toFun

def Prefix.functor {γ δ : Type v} [PartialOrder γ] [PartialOrder δ] (ι : Prefix γ δ) : γ ~> δ :=
Monotone.functor $ StrictMono.monotone (fun _ _ => ι.map_rel_iff.2)

def Prefix.fsEquiv {γ δ : Type v} [PartialOrder γ] [PartialOrder δ] (ι : Prefix γ δ) (j : γ) :
  FullSubcategory (fun i => i < j) ≌ FullSubcategory (fun i => i < ι j) where
  functor := {
    obj := fun i => ⟨ι i.1, sorry⟩
    map := fun f => homOfLE sorry
    map_id := sorry
    map_comp := sorry
  }
  inverse := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Prefix

class WellOrderTop (γ : Type v) extends CompleteLinearOrder γ where
  wf_lt : WellFounded ((· < ·) : γ → γ → Prop)

section cocone

variable {γ : Type v} [PartialOrder γ]

-- Do we need this?
def IsBot' (j : γ) : Prop :=
∀ k, k ≤ j → k = j

def IsSucc (i j : γ) : Prop :=
∀ k, k < j ↔ k ≤ i

theorem IsSucc.lt {i j : γ} (h : IsSucc i j) : i < j :=
(h i).2 le_rfl

theorem IsSucc.le {i j : γ} (h : IsSucc i j) : i ≤ j :=
le_of_lt h.lt

def IsSucc.hom {i j : γ} (h : IsSucc i j) : i ⟶ j :=
homOfLE h.le

def IsLimitStage (j : γ) : Prop :=
IsLUB {i | i < j} j

def coconeAt (j : γ) : Cocone (fullSubcategoryInclusion (fun i => i < j)) :=
{ pt := j,
  ι := { app := fun i => homOfLE (le_of_lt i.property) } }

def SmoothAt {C : Type u} [Category.{v} C] (F : γ ~> C) (j : γ) : Prop :=
Nonempty (IsColimit (F.mapCocone (coconeAt j)))

end cocone

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (X : C) (F : C ~> C) (η : Functor.id C ⟶ F)
-- TODO: fancy 1 is untypable, but it's a good thing because it also breaks the server interaction
variable (γ : Type v) [WellOrderTop γ]

structure GoodDiagram where
  fn : γ ~> C
  iso0 : (j : γ) → IsBot j → (fn.obj j ≅ X) -- ??
  isoStep : (i j : γ) → (h : IsSucc i j) → { φ : fn.obj j ≅ F.obj (fn.obj i) // fn.map h.hom ≫ φ.hom = η.app (fn.obj i) }
  smooth : ∀ (j : γ), IsLimitStage j → SmoothAt fn j

@[ext] structure GoodDiagramHom (D1 D2 : GoodDiagram X F η γ) where
  nat : D1.fn ⟶ D2.fn
  iso0 : ∀ j (h : IsBot j), (D1.iso0 j h).hom = nat.app j ≫ (D2.iso0 j h).hom :=
    by aesop_cat
  isoStep : ∀ i j (h : IsSucc i j),
    (D1.isoStep i j h).val.hom ≫ F.map (nat.app i) = nat.app j ≫ (D2.isoStep i j h).val.hom :=
    by aesop_cat

instance : Category (GoodDiagram X F η γ) where
  Hom := GoodDiagramHom X F η γ
  id D := { nat := ID D.fn }
  comp {D1 D2 D3} f g :=
  { nat := f.nat ≫ g.nat,
    iso0 := sorry,
    isoStep := sorry }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

variable {δ : Type v} [WellOrderTop δ]
variable {X F η γ}

def GoodDiagram.restr_obj (ι : Prefix γ δ) (D : GoodDiagram X F η δ) : GoodDiagram X F η γ where
  fn := ι.functor ⋙ D.fn
  iso0 j hj := D.iso0 (ι j) sorry
  isoStep i j hij := D.isoStep (ι i) (ι j) sorry
  smooth j hj := (D.smooth (ι j) sorry).map $ fun hcol => hcol.whiskerEquivalence (ι.fsEquiv j)

def GoodDiagram.restr_hom (ι : Prefix γ δ) {D1 D2 : GoodDiagram X F η δ} (f : D1 ⟶ D2) :
  D1.restr_obj ι ⟶ D2.restr_obj ι where
  nat := whiskerLeft ι.functor f.nat
  iso0 j h := f.iso0 (ι j) sorry
  isoStep i j h := f.isoStep (ι i) (ι j) sorry

def GoodDiagram.restr (ι : Prefix γ δ) : GoodDiagram X F η δ ~> GoodDiagram X F η γ where
  obj := GoodDiagram.restr_obj ι
  map := GoodDiagram.restr_hom ι
  map_id := sorry
  map_comp := sorry

end CategoryTheory
