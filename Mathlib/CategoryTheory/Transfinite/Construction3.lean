import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Transfinite.OrderStuff

set_option autoImplicit false
set_option trace.Meta.isDefEq.assign true
set_option trace.profiler true

universe v u

local notation "ID" => CategoryTheory.CategoryStruct.id

namespace CategoryTheory

open Limits

section Contraction

structure Contraction (C : Type u) [Category.{v} C] where
  center : C
  hom : (X Y : C) → X ⟶ Y
  eq : ∀ {X Y : C} (f g : X ⟶ Y), f = g

variable {C : Type u} [Category.{v} C]

def Contraction.iso (c : Contraction C) (X Y : C) : X ≅ Y where
  hom := c.hom X Y
  inv := c.hom Y X
  hom_inv_id := c.eq _ _
  inv_hom_id := c.eq _ _

def Contraction.toEquivalencePUnit (c : Contraction C) : C ≌ Discrete PUnit where
  functor := Functor.star C
  inverse := Functor.fromPUnit c.center
  unitIso := NatIso.ofComponents (fun X => c.iso X c.center) (fun _ => c.eq _ _)
  counitIso := Functor.pUnitExt _ _

def Contraction.ofEquivalencePUnit (e : C ≌ Discrete PUnit) : Contraction C where
  center := e.inverse.obj ⟨⟨⟩⟩
  hom _ _ := e.functor.preimage $ eqToHom (Subsingleton.elim _ _)
  eq _ _ := e.functor.map_injective (Subsingleton.elim _ _)

def Contraction.transportEquiv {D : Type u} [Category.{v} D] (c : Contraction C) (e : D ≌ C) :
  Contraction D :=
.ofEquivalencePUnit $ e.trans c.toEquivalencePUnit

end Contraction

section misc

def _root_.IsSucc.hom {γ : Type v} [PartialOrder γ] {i j : γ} (h : IsSucc i j) : i ⟶ j :=
homOfLE h.le

def coconeAt {γ : Type v} [PartialOrder γ] (j : γ) : Cocone ((Prefix.open j).functor) :=
{ pt := j,
  ι := { app := fun i => homOfLE (le_of_lt i.property) } }

def SmoothAt {γ : Type v} [PartialOrder γ] {C : Type u} [Category.{v} C] (F : γ ⥤ C) (j : γ) : Prop :=
Nonempty (IsColimit (F.mapCocone (coconeAt j)))

end misc

section good

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable (X : C) (F : C ⥤ C) (η : Functor.id C ⟶ F)
-- TODO: fancy 1 is untypable, but it's a good thing because it also breaks the server interaction
variable (γ : Type v) [WellOrderedLT γ]

structure GoodDiagram where
  fn : γ ⥤ C
  iso0 : (j : γ) → IsBot j → (fn.obj j ≅ X) -- TODO fix precedence
  isoStep : (i j : γ) → (h : IsSucc i j) →
    { φ : fn.obj j ≅ F.obj (fn.obj i) // fn.map h.hom ≫ φ.hom = η.app (fn.obj i) }
  smooth : ∀ (j : γ), IsLimitStage j → SmoothAt fn j

lemma GoodDiagram.isoStep_eq (D : GoodDiagram X F η γ) {i j : γ} (h : IsSucc i j) :
  D.fn.map h.hom ≫ (D.isoStep i j h).val.hom = η.app (D.fn.obj i) :=
(D.isoStep i j h).property

@[ext] structure GoodDiagramHom (D1 D2 : GoodDiagram X F η γ) where
  nat : D1.fn ⟶ D2.fn
  iso0 : ∀ j (h : IsBot j), (D1.iso0 j h).hom = nat.app j ≫ (D2.iso0 j h).hom :=
    by aesop_cat
  isoStep : ∀ i j (h : IsSucc i j),
    (D1.isoStep i j h).val.hom ≫ F.map (nat.app i) = nat.app j ≫ (D2.isoStep i j h).val.hom :=
    by aesop_cat

#print GoodDiagramHom.ext

instance : Quiver (GoodDiagram X F η γ) where
  Hom := GoodDiagramHom X F η γ

@[ext] theorem GoodDiagramHom.ext' {D1 D2 : GoodDiagram X F η γ}
  (x y : D1 ⟶ D2) : x.nat = y.nat → x = y :=
by intros; apply GoodDiagramHom.ext; assumption

instance : Category (GoodDiagram X F η γ) where
  id D := { nat := ID D.fn }
  comp {D1 D2 D3} f g :=
  { nat := f.nat ≫ g.nat,
    iso0 := fun j hj => by
      rw [NatTrans.comp_app, Category.assoc, ← g.iso0, ← f.iso0]
    isoStep := fun i j h => by
      rw [NatTrans.comp_app, NatTrans.comp_app, F.map_comp,
          Category.assoc, ← g.isoStep, ← Category.assoc, ← Category.assoc, ← f.isoStep]
  }
/-
  comp_id := by
    intro D1 D2 f
    apply GoodDiagramHom.ext
    ext
    apply Category.comp_id
  id_comp := by
    intro D1 D2 f
    apply GoodDiagramHom.ext
    ext
    apply Category.id_comp
  assoc := by
    intros
    apply GoodDiagramHom.ext
    ext
    apply Category.assoc
-/

#exit

lemma GoodDiagramHom.iso0_eq {D1 D2 : GoodDiagram X F η γ} (φ : D1 ⟶ D2) {j : γ} (h : IsBot j) :
  φ.nat.app j = (D1.iso0 j h).hom ≫ (D2.iso0 j h).inv :=
by
  have := (φ.iso0 j h).symm
  rw [Iso.eq_comp_inv, this]

lemma GoodDiagramHom.isoStep_eq {D1 D2 : GoodDiagram X F η γ} (φ : D1 ⟶ D2)
  {i j : γ} (h : IsSucc i j) :
  φ.nat.app j = (D1.isoStep i j h).val.hom ≫ F.map (φ.nat.app i) ≫ (D2.isoStep i j h).val.inv :=
by
  have := (φ.isoStep i j h).symm
  rw [← Iso.eq_comp_inv] at this
  simpa

def GoodDiagram.toIso {D1 D2 : GoodDiagram X F η γ} (i : D1 ≅ D2) : (D1.fn ≅ D2.fn) :=
{ hom := i.hom.nat
  inv := i.inv.nat
  hom_inv_id := show (i.hom ≫ i.inv).nat = GoodDiagramHom.nat (ID D1) by simp
  inv_hom_id := show (i.inv ≫ i.hom).nat = GoodDiagramHom.nat (ID D2) by simp }

section functorial

variable {δ : Type v} [WellOrderedLT δ]
variable {X F η γ}

def GoodDiagram.restr_obj (ι : Prefix γ δ) (D : GoodDiagram X F η δ) : GoodDiagram X F η γ where
  fn := ι.functor ⋙ D.fn
  iso0 j hj := D.iso0 (ι j) sorry
  isoStep i j hij := D.isoStep (ι i) (ι j) sorry
  smooth j hj := (D.smooth (ι j) sorry).map $ fun hcol => hcol.whiskerEquivalence (equivOfOrderIso $ ι.fixme j)

def GoodDiagram.restr_hom (ι : Prefix γ δ) {D1 D2 : GoodDiagram X F η δ} (f : D1 ⟶ D2) :
  D1.restr_obj ι ⟶ D2.restr_obj ι where
  nat := whiskerLeft ι.functor f.nat
  iso0 j h := f.iso0 (ι j) sorry
  isoStep i j h := f.isoStep (ι i) (ι j) sorry

def GoodDiagram.restr (ι : Prefix γ δ) : GoodDiagram X F η δ ⥤ GoodDiagram X F η γ where
  obj := GoodDiagram.restr_obj ι
  map := GoodDiagram.restr_hom ι
  map_id := sorry
  map_comp := sorry

-- Pseudofunctoriality of GoodDiagram.restr

def GoodDiagram.restr_id : GoodDiagram.restr (Prefix.id γ) ≅ Functor.id (GoodDiagram X F η γ) :=
Iso.refl _

def GoodDiagram.restr_comp {ε : Type v} [WellOrderedLT ε] (g : Prefix δ ε) (f : Prefix γ δ) :
  GoodDiagram.restr (X := X) (η := η) (F := F) (g.comp f) ≅ GoodDiagram.restr g ⋙ GoodDiagram.restr f :=
Iso.refl _

-- This definition is not as "nice" as it could be,
-- because it is only intended to be used "propositionally".
def GoodDiagram.restr_equiv (ι : Prefix γ δ) (κ : Prefix δ γ) :
  GoodDiagram X F η γ ≌ GoodDiagram X F η δ :=
Equivalence.mk
  (F := GoodDiagram.restr κ)
  (G := GoodDiagram.restr ι)
  (η :=
    GoodDiagram.restr_id.symm ≪≫
    eqToIso (by congr; apply Subsingleton.elim) ≪≫
    GoodDiagram.restr_comp κ ι)
  (ε :=
    (GoodDiagram.restr_comp ι κ).symm ≪≫
    eqToIso (by congr; apply Subsingleton.elim) ≪≫
    GoodDiagram.restr_id)

def GoodDiagram.transportContraction' (ι : Prefix γ δ) (κ : Prefix δ γ) :
  Contraction (GoodDiagram X F η δ) → Contraction (GoodDiagram X F η γ) :=
fun c => c.transportEquiv $ GoodDiagram.restr_equiv ι κ

def GoodDiagram.transportContraction (e : γ ≃o δ) :
  Contraction (GoodDiagram X F η δ) → Contraction (GoodDiagram X F η γ) :=
GoodDiagram.transportContraction' (Prefix.ofOrderIso e) (Prefix.ofOrderIso e.symm)

end functorial

end good

open WithTop in
def extendByCocone {β : Type v} [PartialOrder β] {C : Type u} [Category.{v} C]
    (F : β ⥤ C) (Z : Cocone F) : WithTop β ⥤ C where
  obj := fun
    | (y : β) => F.obj y
    | ⊤ => Z.pt
  map := @fun
    | (y1 : β), (y2 : β), f => F.map (homOfLE $ coe_le_coe.1 $ leOfHom f)
    | (y1 : β), ⊤, _ => Z.ι.app y1
    | ⊤, (y2 : β), f => False.elim (not_top_le_coe _ $ leOfHom f)
    | ⊤, ⊤, _ => ID _
  map_id := fun
    | (y : β) => F.map_id _
    | ⊤ => rfl
  map_comp := @fun
    | (y1 : β), (y2 : β), (y3 : β), f, g => F.map_comp _ _
    | (y1 : β), (y2 : β), ⊤, f, _ => by simp
    | (y1 : β), ⊤, ⊤, _, _ => (Category.comp_id _).symm
    | ⊤, ⊤, ⊤, _, _ => (Category.comp_id _).symm
    | ⊤, (y2 : β), _, f, g => False.elim (not_top_le_coe _ $ leOfHom f)
    | _, ⊤, (y3 : β), f, g => False.elim (not_top_le_coe _ $ leOfHom g)

-- We will prove Contraction (GoodDiagram X F η γ) for all γ by induction.
-- First, we separately handle the three cases: IsBot, IsSucc, IsLimitStage.

section internal

variable {C : Type u} [Category.{v} C]
variable (X : C) (F : C ⥤ C) (η : Functor.id C ⟶ F)

namespace bot

instance : WellOrderedLT PUnit := {}

def aux : Contraction (GoodDiagram X F η PUnit) where
  center := {
    fn := (Functor.const _).obj X
    iso0 := fun j hj => Iso.refl X
    isoStep := fun i j hij => False.elim sorry
    smooth := fun j hj => False.elim sorry
  }
  hom D1 D2 := {
    nat := {
      app := fun i => (D1.iso0 i sorry).hom ≫ (D2.iso0 i sorry).inv
      naturality := @fun i j f => by
        cases i; cases j; cases f
        erw [D1.fn.map_id, D2.fn.map_id]
        rw [Category.id_comp, Category.comp_id]
    }
    iso0 := by intros j hj; simp
    isoStep := fun i j hj => False.elim sorry
  }
  eq {D1} {D2} f g := by
    apply GoodDiagramHom.ext; ext i
    have : IsBot i := sorry
    rw [GoodDiagramHom.iso0_eq X F η _ _ this, GoodDiagramHom.iso0_eq X F η _ _ this]

end bot

namespace succ

section

@[simp]
theorem homOfLE_self {X : Type _} [PartialOrder X] {x : X} (f : x ⟶ x): f = ID x :=
  rfl

variable {β : Type v} [WellOrderedTop β]

open WithTop in
def aux (c : Contraction (GoodDiagram X F η β)) : Contraction (GoodDiagram X F η (WithTop β)) where
  center := {
    fn := extendByCocone c.center.fn {
      pt := F.obj $ c.center.fn.obj ⊤
      ι := {
        app := fun y => c.center.fn.map default ≫ η.app _
        naturality := @fun y1 y2 f => by
          dsimp
          rw [← Category.assoc, Category.comp_id, ← Functor.map_comp]
          rfl
      }
    }
    iso0 := fun
      | (j : β), hj => c.center.iso0 j sorry
      | ⊤, h => False.elim sorry
    isoStep := fun
      | (i : β), (j : β), h => c.center.isoStep i j sorry
      | (i : β), .none, h => by
        rcases eq_top_of_is_succ_top h with rfl
        refine ⟨Iso.refl _, ?_⟩
        simp [extendByCocone]
      | .none, _, h => False.elim sorry
    smooth := fun
      | (i : β), h =>
        (c.center.smooth i sorry).map $ fun hcol =>
          hcol.ofWhiskerEquivalence (equivOfOrderIso $ toWithTop.fixme i)
      | .none, h => False.elim sorry
  }
  hom D1 D2 :=
    have I :=
      c.hom (D1.restr_obj toWithTop) (D2.restr_obj toWithTop)
    { nat := {
        app := fun
          | (i : β) => I.nat.app i
          | ⊤ =>
            (D1.isoStep (⊤ : β) ⊤ isSucc_top).val.hom ≫
            F.map (I.nat.app _) ≫
            (D2.isoStep (⊤ : β) ⊤ isSucc_top).val.inv
        naturality := @fun
          | (i1 : β), (i2 : β), f => I.nat.naturality (homOfLE $ coe_le_coe.1 $ leOfHom f)
          | (i1 : β), ⊤, f => by
            have : f = homOfLE (coe_le_coe.2 le_top) ≫ homOfLE le_top := rfl
            simp only [this, Functor.map_comp, ← Category.assoc, Iso.comp_inv_eq]
            slice_lhs 2 3 => erw [GoodDiagram.isoStep_eq X F η _ D1 isSucc_top]
            slice_rhs 3 4 => erw [GoodDiagram.isoStep_eq X F η _ D2 isSucc_top]
            erw [← η.naturality, ← Category.assoc, ← Category.assoc,
              ← I.nat.naturality (homOfLE (le_top : i1 ≤ ⊤))]
            rfl
          | ⊤, (i2 : β), f => False.elim (not_top_le_coe _ $ leOfHom f)
          | ⊤, ⊤, f => by simp
      }
      iso0 := fun
        | (i : β), hi => by simpa using I.iso0 i sorry
        | ⊤, hi => False.elim sorry
      isoStep := fun
        | (i : β), (j : β), hij => by simpa using I.isoStep i j sorry
        | (i : β), ⊤, hij => by
          rcases eq_top_of_is_succ_top hij with rfl
          simp
        | ⊤, _, hij => False.elim sorry }
  eq := @fun D1 D2 f g => by
    have : ∀ (i : β), f.nat.app i = g.nat.app i := sorry
    apply GoodDiagramHom.ext
    ext i
    induction i using WithTop.recTopCoe
    case coe => apply this
    case top =>
      rw [GoodDiagramHom.isoStep_eq X F η _ f isSucc_top]
      rw [GoodDiagramHom.isoStep_eq X F η _ g isSucc_top]
      rw [this]

end

end succ

namespace limit

variable {β : Type v} [WellOrderedNoTop β]
variable (IH : ∀ (α : β), Contraction (GoodDiagram X F η {i // i ≤ α}))
variable {X F η}

open WithTop

theorem aux_eq {D1 D2 : GoodDiagram X F η (WithTop β)} (f g : D1 ⟶ D2) : f = g := by
  have old : ∀ (α : β), f.nat.app α = g.nat.app α := by
    intro α
    have c := (IH α).eq (GoodDiagram.restr_hom (pref α) f) (GoodDiagram.restr_hom (pref α) g)
    exact congr_arg (fun h => h.nat.app ⟨α, le_rfl⟩) c
  have new : f.nat.app ⊤ = g.nat.app ⊤ := by
    obtain ⟨colim⟩ := D1.smooth ⊤ isLimit_top
    apply colim.hom_ext; rintro ⟨α, hα⟩
    induction α using WithTop.recTopCoe
    case top => exact False.elim $ not_top_lt hα
    case coe α =>
      let φ : (α : WithTop β) ⟶ ⊤ := default
      change D1.fn.map φ ≫ f.nat.app ⊤ = D1.fn.map φ ≫ g.nat.app ⊤
      rw [f.nat.naturality φ, g.nat.naturality φ, old]
  apply GoodDiagramHom.ext; ext i; induction i using WithTop.recTopCoe
  case coe => apply old
  case top => apply new

noncomputable
def aux_hom (D1 D2 : GoodDiagram X F η (WithTop β)) : D1 ⟶ D2 :=
  let ih : (α : β) → D1.restr_obj (pref α) ⟶ D2.restr_obj (pref α) := fun α =>
    ((IH α).hom (D1.restr_obj (pref α)) (D2.restr_obj (pref α)))
  let old_app : (α : β) → D1.fn.obj α ⟶ D2.fn.obj α := fun α =>
    (ih α).nat.app ⟨α, le_rfl⟩
  have old_app' : ∀ {α α' : β} (hα : α ≤ α'), old_app α = (ih α').nat.app ⟨α, hα⟩ := by
    intro α α' hα
    have := (IH α).eq (ih α) (GoodDiagram.restr_hom (pref' α α' hα) (ih α'))
    exact congr_arg (fun h => h.nat.app ⟨α, le_rfl⟩) this
  have old_nat : ∀ {α α' : β} (hα : α ≤ α'),
      D1.fn.map (homOfLE (coe_le_coe.2 hα)) ≫ old_app α' =
      old_app α ≫ D2.fn.map (homOfLE (coe_le_coe.2 hα)) := by
    intros α α' hα
    rw [old_app' (le_refl α'), old_app' hα]
    have φ : (⟨α, hα⟩ : {i // i ≤ α'}) ⟶ (⟨α', le_rfl⟩ : {i // i ≤ α'}) := homOfLE hα
    exact (ih α').nat.naturality φ
  let new_app : D1.fn.obj ⊤ ⟶ D2.fn.obj ⊤ :=
    ((D1.smooth ⊤ isLimit_top).some).map (D2.fn.mapCocone (coconeAt ⊤)) $
    { app := fun
      | .mk (α : β) _ => old_app α
      | .mk ⊤ hα => False.elim $ not_top_lt hα
      naturality := @fun
      | (.mk (α : β) _), (.mk (α' : β) _), f => old_nat $ coe_le_coe.1 $ leOfHom f
      | (.mk ⊤ hα), _, _ => False.elim $ not_top_lt hα
      | _, (.mk ⊤ hα'), _ => False.elim $ not_top_lt hα' }
  let app : D1.fn ⟶ D2.fn := {
    app := fun
      | (α : β) => old_app α
      | ⊤ => new_app
    naturality := @fun
      | (α : β), (α' : β), f => old_nat $ coe_le_coe.1 $ leOfHom f
      | (α : β), ⊤, f => by
        have := ((D1.smooth ⊤ isLimit_top).some).ι_map (D2.fn.mapCocone (coconeAt ⊤))
        apply this _ ⟨α, coe_lt_top α⟩
      | ⊤, (α' : β), f => False.elim sorry
      | ⊤, ⊤, _ => by erw [D1.fn.map_id, D2.fn.map_id]; simp }
  { nat := app
    iso0 := fun
      | (α : β), hα => (ih α).iso0 ⟨α, le_rfl⟩ sorry
      | ⊤, hα => False.elim sorry
    isoStep := fun
      | (α : β), (α' : β), hα => by
        have := (ih α').isoStep ⟨α, coe_le_coe.1 hα.le⟩ ⟨α', le_rfl⟩ sorry
        convert this
        apply old_app'
        done
      | (α : β), ⊤, hα => False.elim sorry
      | ⊤, (α' : β), hα => False.elim sorry
      | ⊤, ⊤, hα => False.elim sorry }

section center

def mk_hom {α i i' : β} (h : i ≤ i') (hi : i' ≤ α) :
  (⟨i, h.trans hi⟩ : {i // i ≤ α}) ⟶ (⟨i', hi⟩ : {i // i ≤ α}) :=
homOfLE h

def aux_iso {α α' i : β} (hi : i ≤ α) (hα : α ≤ α') :
  (IH α).center.fn.obj ⟨i, hi⟩ ≅ (IH α').center.fn.obj ⟨i, hi.trans hα⟩ :=
have := (IH α).iso (IH α).center (((IH α').center).restr_obj (pref' α α' hα))
(GoodDiagram.toIso X F η _ this).app ⟨i, hi⟩

lemma aux_iso_id {α i : β} (hi : i ≤ α) :
  aux_iso IH hi le_rfl = Iso.refl _ := by
  have := (IH α).eq ((IH α).iso (IH α).center (IH α).center).hom (ID _)
  ext
  exact congr_arg (fun h => h.nat.app ⟨i, hi⟩) this

lemma aux_iso_comp {α α' α'' i : β} (hi : i ≤ α) (hα : α ≤ α') (hα' : α' ≤ α'') :
  aux_iso IH hi (hα.trans hα') = aux_iso IH hi hα ≪≫ aux_iso IH (hi.trans hα) hα' := by
  have := (IH α).eq
    (((IH α).iso (IH α).center (((IH α'').center).restr_obj (pref' α α'' (hα.trans hα')))).hom)
    (((IH α).iso (IH α).center (((IH α').center).restr_obj (pref' α α' hα))).hom ≫
     GoodDiagram.restr_hom (pref' α α' hα)
       (((IH α').iso (IH α').center (((IH α'').center).restr_obj (pref' α' α'' hα'))).hom))
  ext
  exact congr_arg (fun h => h.nat.app ⟨i, hi⟩) this

lemma aux_iso_nat {α α' i i' : β} (h : i ≤ i') (hi : i' ≤ α) (hα : α ≤ α') :
  (aux_iso IH (h.trans hi) hα).hom ≫
  (IH α').center.fn.map (mk_hom h (hi.trans hα)) =
  (IH α).center.fn.map (mk_hom h hi) ≫ (aux_iso IH hi hα).hom :=
let I := (IH α).iso (IH α).center (((IH α').center).restr_obj (pref' α α' hα))
(I.hom.nat.naturality (mk_hom h hi)).symm

def aux_open : β ⥤ C where
  obj := fun α => (IH α).center.fn.obj ⟨α, le_rfl⟩
  map := @fun α α' f =>
    (aux_iso IH le_rfl (leOfHom f)).hom ≫
    (IH α').center.fn.map (homOfLE $ leOfHom f)
  map_id := fun α => by simp [aux_iso_id]
  map_comp := @fun α α' α'' f g => by
    have hα : α ≤ α' := leOfHom f
    have hα' : α' ≤ α'' := leOfHom g
    let f' : (⟨α, hα.trans hα'⟩ : {i // i ≤ α''}) ⟶ (⟨α', hα'⟩ : {i // i ≤ α''}) := homOfLE hα
    let g' : (⟨α', hα'⟩ : {i // i ≤ α''}) ⟶ (⟨α'', le_rfl⟩ : {i // i ≤ α''}) := homOfLE hα'
    dsimp
    erw [aux_iso_comp IH le_rfl hα hα', (IH α'').center.fn.map_comp f' g']
    simp only [Iso.trans_hom, Category.assoc, Iso.cancel_iso_hom_left]
    slice_lhs 1 2 => erw [aux_iso_nat IH hα le_rfl hα']
    simp
    rfl

variable [HasColimits C]

noncomputable def aux_closed : WithTop β ⥤ C :=
extendByCocone (aux_open IH) (colimit.cocone _)

noncomputable def aux_center : GoodDiagram X F η (WithTop β) where
  fn := aux_closed IH
  iso0 := fun
    | (j : β), hj => (IH j).center.iso0 ⟨j, le_rfl⟩ sorry
    | ⊤, hj => False.elim sorry
  isoStep := fun
    | (i : β), (j : β), h => {
      val :=
        ((IH j).center.isoStep ⟨i, coe_le_coe.1 h.le⟩ ⟨j, le_rfl⟩ sorry).val ≪≫
        F.mapIso (aux_iso IH le_rfl (coe_le_coe.1 h.le)).symm
      property := by
        simp only [aux_closed, extendByCocone, aux_open, colimit.cocone_x, colimit.cocone_ι,
          Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
        have := ((IH j).center.isoStep ⟨i, coe_le_coe.1 h.le⟩ ⟨j, le_rfl⟩ sorry).property
        slice_lhs 2 3 => erw [this]
        slice_lhs 1 2 => erw [η.naturality]
        slice_lhs 2 3 => erw [← F.map_comp]; simp [aux_iso]
        rw [Category.comp_id] }
    | ⊤, (j : β), h => False.elim sorry
    | (i : β), ⊤, h => False.elim sorry
    | ⊤, ⊤, h => False.elim sorry
  smooth := fun
    | (i : β), h => by
      constructor
      apply IsColimit.ofWhiskerEquivalence
        (equivOfOrderIso $ Prefix.fixme (toWithTop.comp (Prefix.closed i)) ⟨i, le_rfl⟩)
      let G : {j // j ≤ i} ⥤ C := (Prefix.closed i).functor ⋙ aux_open IH
      change IsColimit (G.mapCocone (coconeAt ⟨i, le_rfl⟩))
      have φ : G ≅ (IH i).center.fn := NatIso.ofComponents (fun j => aux_iso IH le_rfl j.2) $ by
        intro j j' f
        dsimp [aux_open, Prefix.functor]
        slice_lhs 2 3 => erw [← aux_iso_nat IH (show j ≤ j' from leOfHom f) le_rfl j'.2]
        slice_lhs 1 2 => erw [← Iso.trans_hom, ← aux_iso_comp]
        done
      apply IsColimit.mapCoconeEquiv φ.symm
      apply ((IH i).center.smooth ⟨i, le_rfl⟩ sorry).some
    | ⊤, _ => by
      constructor
      exact (colimit.isColimit (aux_open IH)).ofWhiskerEquivalence (equivOfOrderIso limit_oe.symm)

noncomputable def aux : Contraction (GoodDiagram X F η (WithTop β)) where
  center := aux_center IH
  hom := aux_hom IH
  eq := aux_eq IH

end center

end limit

end internal

section main

universe w

def orderTypeRec {C : (γ : Type v) → [WellOrderedTop γ] → Type w}
  (h : (γ : Type v) → [WellOrderedTop γ] →
       (IH : (β : Type v) → [WellOrderedTop β] → (hβ : ltType β < ltType γ) → C β) → C γ)
  (γ : Type v) [WellOrderedTop γ] : C γ :=
h γ (fun β _ _ => orderTypeRec h β)
termination_by _ γ h => ltType γ

variable {C : Type u} [Category.{v} C]
variable (X : C) (F : C ⥤ C) (η : Functor.id C ⟶ F)
variable (γ : Type v)

noncomputable def contr [HasColimits C] [WellOrderedTop γ] : Contraction (GoodDiagram X F η γ) := by
  apply orderTypeRec ?_ γ; clear! γ; intros γ _ IH
  rcases analyze (⊤ : γ) with (hγ|⟨α, hγ⟩|hγ)
  case isBot =>
    apply GoodDiagram.transportContraction (isoPUnit_of_isBot_top hγ)
    apply bot.aux
  case isSucc =>
    apply GoodDiagram.transportContraction (isoWithTop_of_isSucc_top α hγ)
    apply succ.aux
    apply IH
    apply ltType_closed_lt
    apply hγ.lt
  case isLimitStage =>
    apply GoodDiagram.transportContraction (isoWithTopOpen (γ := γ))
    let inst := noTop hγ
    apply limit.aux
    intro α
    apply IH
    apply lt_of_le_of_lt (ltType_closed_le _) (ltType_open_lt _)

end main

end CategoryTheory
