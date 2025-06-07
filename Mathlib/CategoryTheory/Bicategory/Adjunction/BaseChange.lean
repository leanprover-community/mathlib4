/-
Copyright (c) 2025 Christian Merten, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.PullbackStruct
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Monad.Comonadicity

/-!
# Base change morphisms associated to commutative squares

-/

namespace CategoryTheory

-- TODO: move
namespace CommSq

variable {C : Type*} [Category C]

def toLoc {C : Type*} [Category C] {W X Y Z : C}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (sq : CommSq f g h i) :
    CommSq f.toLoc g.toLoc h.toLoc i.toLoc where
  w := by simp [← Quiver.Hom.comp_toLoc, sq.w]

end CommSq

open Bicategory Limits Opposite

namespace Bicategory

variable {B : Type*} [Bicategory B] {c d e : B}
  {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : d ⟶ e} {r₂ : e ⟶ d}

@[reassoc (attr := simp)]
lemma Adjunction.whiskerRight_unit_whiskerLeft_counit (adj₁ : Adjunction l₁ r₁) :
    adj₁.unit ▷ l₁ ⊗≫ l₁ ◁ adj₁.counit = (λ_ l₁).hom ≫ (ρ_ l₁).inv :=
  adj₁.left_triangle

@[reassoc (attr := simp)]
lemma Adjunction.whiskerRight_unit_associator_whiskerLeft_counit (adj₁ : Adjunction l₁ r₁) :
    adj₁.unit ▷ l₁ ≫ (α_ _ _ _).hom ≫ l₁ ◁ adj₁.counit = (λ_ l₁).hom ≫ (ρ_ l₁).inv := by
  rw [← adj₁.left_triangle]
  bicategory

lemma mateEquiv_id (adj₁ : Adjunction l₁ r₁) (adj₂ : Adjunction l₂ r₂) :
    mateEquiv adj₁ adj₂ (𝟙 _) = adj₁.counit ≫ adj₂.unit := by
  simp only [mateEquiv_apply,
    Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply]
  trans  𝟙 _ ⊗≫ ((r₁ ≫ l₁) ◁ adj₂.unit ≫ adj₁.counit ▷ _ ) ⊗≫ 𝟙 _
  · bicategory
  · rw [whisker_exchange]
    bicategory

lemma Adjunction.homEquiv₁_symm_whiskerRight {b c d e : B} {l : b ⟶ c}
    {r : c ⟶ b} (adj : l ⊣ r) {g : b ⟶ d} {h : c ⟶ d} (β : r ≫ g ⟶ h) (u : d ⟶ e) :
    adj.homEquiv₁.symm ((α_ _ _ _).inv ≫ β ▷ u) =
      adj.homEquiv₁.symm β ▷ u ≫ (α_ _ _ _).hom := by
  simp [homEquiv₁_symm_apply]

lemma Adjunction.homEquiv₁_symm_comp {b c d : B} {l : b ⟶ c}
    {r : c ⟶ b} (adj : l ⊣ r) {g : b ⟶ d} {h h' : c ⟶ d} (β : r ≫ g ⟶ h) (α : h ⟶ h') :
    adj.homEquiv₁.symm (β ≫ α) =
      adj.homEquiv₁.symm β ≫ l ◁ α := by
  simp [homEquiv₁_symm_apply]

@[reassoc]
lemma whiskerLeft_whiskerLeft_associator_whiskerRight
    {x y z u v : B} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
    (g' : z ⟶ u) (f' : u ⟶ v) (h' : z ⟶ v)
    (α : f ≫ g ⟶ h) (β : g' ≫ f' ⟶ h') :
    f ◁ g ◁ β ≫ (α_ _ _ _).inv ≫ α ▷ _ =
      (α_ _ _ _).inv ≫
      α ▷ _ ≫ _ ◁ β := by
  rw [← whisker_exchange]
  simp

end Bicategory

variable {C : Type*} [Category C]

namespace Pseudofunctor

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat)) {X S  : C} (f : X ⟶ S)

/-
Let us think that `sq` is a square in `LocallyDiscrete B₀ᵒᵖ` that is dual to a square in `B₀`
```
  t                      b.unop
X₁ ⟶ Y₁                  Y₂ ⟶ X₂
l|    |r   dual of  r.unop|    | l.unop
v    v                   v    v
X₂ ⟶ Y₂                  Y₁ ⟶ X₁
  b                      t.unop
```
This is the base change natural transformation
`l_* ≫ t^* ⟶ b^* ≫ r_*`
-/
def baseChange
  {B C : Type*} [Bicategory B] [Strict B] [Bicategory C] (F : Pseudofunctor B (Adj C))
  {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂}
  {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b) :
  (F.map l).r ≫ (F.map t).l ⟶ (F.map b).l ≫ (F.map r).r :=
Bicategory.mateEquiv (F.map l).adj (F.map r).adj (F.isoMapOfCommSq sq).hom.τl

variable {B C : Type*} [Bicategory B] [Strict B] [Bicategory C] (F : Pseudofunctor B (Adj C))
  {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂}
  {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b)

/--
This is the base change natural transformation whiskered on the right with `r^*` and
composed with the counit of `r^*`, i.e. the composition
`l_* ≫ t^* ≫ r^* ⟶ b^* ≫ r_* ≫ r^* ⟶ b^*`.

This is used to construct the morphism in `DescentData'` from a `DescentDataAsCoalgebra`. We
postpone descending to the level of objects as long as possible and hence
state all necessary compatibility properties for `whiskerBaseChange` instead.
-/
def whiskerBaseChange : (F.map l).r ≫ (F.map t).l ≫ (F.map r).l ⟶ (F.map b).l :=
  (F.map l).adj.homEquiv₁ (F.isoMapOfCommSq sq).hom.τl

lemma whiskerBaseChange_eq : F.whiskerBaseChange sq =
    (F.map l).adj.homEquiv₁ (F.isoMapOfCommSq sq).hom.τl := rfl

lemma whiskerBaseChange_eq' : F.whiskerBaseChange sq =
    (α_ _ _ _).inv ≫ (F.map r).adj.homEquiv₂.symm (F.baseChange sq) := by
  dsimp only [baseChange]
  rw [mateEquiv_apply', Equiv.symm_apply_apply, Iso.inv_hom_id_assoc,
    whiskerBaseChange]

lemma whiskerBaseChange_eq_whiskerLeft_isoMapOfCommSq :
    F.whiskerBaseChange sq =
      (F.map l).r ◁ (F.isoMapOfCommSq sq).hom.τl ≫
      (α_ _ _ _).inv ≫
      (F.map l).adj.counit ▷ _ ≫
      (λ_ _).hom :=
  rfl

lemma whiskerBaseChange_eq_whiskerRight_baseChange :
    F.whiskerBaseChange sq =
      (α_ _ _ _).inv ≫ F.baseChange sq ▷ (F.map r).l ≫
      (α_ _ _ _).hom ≫ (F.map b).l ◁ (F.map r).adj.counit ≫ (ρ_ _).hom := by
  apply (F.map l).adj.homEquiv₁.symm.injective
  rw [whiskerBaseChange]
  simp only [Equiv.symm_apply_apply]
  rw [← Category.assoc]
  rw [Adjunction.homEquiv₁_symm_comp]
  rw [Adjunction.homEquiv₁_symm_whiskerRight]
  rw [baseChange, Bicategory.mateEquiv_apply]
  simp only [Equiv.symm_apply_apply, comp_whiskerRight, Category.assoc, Bicategory.whiskerLeft_comp,
    whiskerLeft_rightUnitor, pentagon_assoc]
  rw [Adjunction.homEquiv₂_apply]
  simp only [comp_whiskerRight, whisker_assoc, Category.assoc, triangle_assoc_comp_right_inv_assoc]
  have :
    (F.isoMapOfCommSq sq).hom.τl ▷ (F.map r).r ▷ (F.map r).l ≫
      (α_ ((F.map l).l ≫ (F.map b).l) (F.map r).r (F.map r).l).hom ≫
        (α_ (F.map l).l (F.map b).l ((F.map r).r ≫ (F.map r).l)).hom ≫
          (F.map l).l ◁ (F.map b).l ◁ (F.map r).adj.counit =
      (α_ _ _ _).hom ≫
      _ ◁ (F.map r).adj.counit ≫
      (F.isoMapOfCommSq sq).hom.τl ▷ _ ≫
      (α_ _ _ _).hom := by
    rw [whisker_exchange_assoc]
    simp
  rw [reassoc_of% this]
  simp only [Adj.comp_l, comp_whiskerLeft, Bicategory.whiskerRight_id, Iso.hom_inv_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, pentagon_inv_hom_hom_hom_hom_assoc,
    Iso.inv_hom_id_assoc]
  nth_rw 2 [← Bicategory.whiskerLeft_comp_assoc]
  nth_rw 2 [← Bicategory.whiskerLeft_comp_assoc]
  rw [Category.assoc]
  simp

section Unit

variable {B C : Type*} [Bicategory B] [Strict B] [Bicategory C]
  (F : Pseudofunctor B (Adj C))

variable {X Y : B} (f : X ⟶ Y)

lemma baseChange_id_id_eq_unit :
    F.baseChange (t := 𝟙 X) (l := 𝟙 X) (b := f) (r := f) ⟨rfl⟩ =
      (F.map (𝟙 X)).r ◁ (F.mapId _).hom.τl ≫
      (ρ_ _).hom ≫
      (F.mapId _).inv.τr ≫
      (F.map f).adj.unit := by
  simp only [baseChange, isoMapOfCommSq_self_self, Iso.refl_hom, Adj.id_τl, Adj.comp_l]
  rw [mateEquiv_id, Adj.counit_map_id, ← whisker_exchange_assoc]
  simp

end Unit

section Horizontal

variable {B C : Type*} [Bicategory B] [Strict B] [Bicategory C]
(F : Pseudofunctor B (Adj C))

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : B} {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
  {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
  {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
  (sq : CommSq t l m b) (sq' : CommSq t' m r b')
  {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
  (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

lemma baseChange_horiz_comp' :
  baseChange F (sq.horiz_comp' sq' ht hb) =
    (F.map l).r ◁ ((F.comp Adj.forget₁).mapComp' t t' t'' ht).hom ≫
    (α_ _ _ _).inv ≫
    baseChange F sq ▷ (F.map t').l ≫
    (α_ _ _ _).hom ≫
    (F.map b).l ◁ baseChange F sq' ≫
    (α_ _ _ _).inv ≫
    ((F.comp Adj.forget₁).mapComp' b b' b'' hb).inv ▷ (F.map r).r := by
  sorry

end Horizontal

section Vertical

variable {B C : Type*} [Bicategory B] [Strict B] [Bicategory C]
  (F : Pseudofunctor B (Adj C))

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B}
  {t : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂} {b : X₃ ⟶ Y₃}
  {l : X₁ ⟶ X₂} {l' : X₂ ⟶ X₃}
  {r : Y₁ ⟶ Y₂} {r' : Y₂ ⟶ Y₃}
  (sq : CommSq t l r m)
  (sq' : CommSq m l' r' b)
  {l'' : X₁ ⟶ X₃} {r'' : Y₁ ⟶ Y₃}
  (hl : l ≫ l' = l'') (hr : r ≫ r' = r'')

lemma baseChange_vert_comp' :
    baseChange F (sq.vert_comp' sq' hl hr) =
    Adj.forget₂.map₂ (F.mapComp' l l' l'').inv.op ▷ (F.map t).l ≫
    (α_ _ _ _).hom ≫
    (F.map l').r ◁ baseChange F sq ≫
    (α_ _ _ _).inv ≫
    baseChange F sq' ▷ (F.map r).r ≫
    (α_ _ _ _).hom ≫
    _ ◁ Adj.forget₂.map₂ (F.mapComp' r r' r'').hom.op := by
  sorry

end Vertical

section Square

variable {B C : Type*} [Bicategory B] [Strict B] [Bicategory C]
  (F : Pseudofunctor B (Adj C))

-- 3 by 3 square from left to right `X` -> `Y` -> `Z` and from
-- top to bottom `_₁` -> `_₂` -> `_₃`
variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : B}
  {tl : X₁ ⟶ Y₁} {tr : Y₁ ⟶ Z₁}
  {ml : X₂ ⟶ Y₂} {mr : Y₂ ⟶ Z₂}
  {bl : X₃ ⟶ Y₃} {br : Y₃ ⟶ Z₃}
  {lt : X₁ ⟶ X₂} {lb : X₂ ⟶ X₃}
  {mt : Y₁ ⟶ Y₂} {mb : Y₂ ⟶ Y₃}
  {rt : Z₁ ⟶ Z₂} {rb : Z₂ ⟶ Z₃}
  {t : X₁ ⟶ Z₁} {l : X₁ ⟶ X₃} {r : Z₁ ⟶ Z₃} {b : X₃ ⟶ Z₃}
  (sqtl : CommSq tl lt mt ml)
  (sqtr : CommSq tr mt rt mr)
  (sqbl : CommSq ml lb mb bl)
  (sqbr : CommSq mr mb rb br)
  (sq : CommSq t l r b)
  (ht : tl ≫ tr = t)
  (hl : lt ≫ lb = l)
  (hr : rt ≫ rb = r)
  (hb : bl ≫ br = b)

lemma baseChange_square :
    F.baseChange sq =
      (F.mapComp' lt lb l hl).inv.τr ▷ _ ≫
      (α_ _ _ _).hom ≫
      (F.map lb).r ◁ _ ◁ (F.mapComp' tl tr t ht).hom.τl ≫
      (F.map lb).r ◁ (α_ _ _ _).inv ≫
      (F.map lb).r ◁ F.baseChange sqtl ▷ _ ≫
      (F.map lb).r ◁ (α_ _ _ _).hom ≫
      (F.map lb).r ◁ (F.map ml).l ◁ F.baseChange sqtr ≫
      (α_ _ _ _).inv ≫
      (α_ _ _ _).inv ≫
      F.baseChange sqbl ▷ (F.map mr).l ▷ (F.map rt).r ≫
      (α_ _ _ _).hom ▷ (F.map rt).r ≫
      (α_ _ _ _).hom ≫
      (F.map bl).l ◁ F.baseChange sqbr ▷ (F.map rt).r ≫
      (F.map bl).l ◁ (α_ _ _ _).hom ≫
      (F.map bl).l ◁ (F.map br).l ◁ (F.mapComp' rt rb r hr).hom.τr ≫
      (α_ _ _ _).inv ≫
      (F.mapComp' bl br b hb).inv.τl ▷ (F.map r).r := by
  let sqt : CommSq t lt rt (ml ≫ mr) := ⟨by simp [← ht, sqtr.1, reassoc_of% sqtl.1]⟩
  let sqb : CommSq (ml ≫ mr) lb rb b := ⟨by simp [← hb, sqbr.1, reassoc_of% sqbl.1]⟩
  rw [F.baseChange_vert_comp' sqt sqb hl hr]
  rw [F.baseChange_horiz_comp' sqtl sqtr ht rfl]
  rw [F.baseChange_horiz_comp' sqbl sqbr rfl hb]
  simp only [Adj.forget₂_obj, Adj.forget₂_map, Quiver.Hom.unop_op', Adj.comp_r, Adj.forget₂_map₂,
    Quiver.Hom.unop_op, comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Adj.mapComp'_comp_adjForget₁_hom,
    Adj.mapComp'_comp_adjForget₁_inv, Bicategory.whiskerLeft_comp, comp_whiskerRight, whisker_assoc,
    Category.assoc, Iso.inv_hom_id_assoc, Adj.comp_l]
  congr 7
  slice_lhs 2 3 =>
    rw [← Bicategory.whiskerLeft_comp, ← Bicategory.comp_whiskerRight]
    simp only [Adj.inv_hom_id_τl, Adj.comp_l, id_whiskerRight, Bicategory.whiskerLeft_id]
  simp only [Category.id_comp, Category.assoc, pentagon_inv_assoc, Iso.cancel_iso_inv_left]
  congr 4
  simp [whiskerLeft_whiskerLeft_associator_whiskerRight]

end Square

section

lemma baseChange_self_self {S X Y : B} (f : S ⟶ X) (g : X ⟶ Y) :
    F.baseChange (l := f) (t := f) (b := g) (r := g) (by simp) =
      (F.map f).adj.counit ≫ (F.map g).adj.unit := by
  simp [baseChange, mateEquiv_id]

lemma whiskerBaseChange_self_self {S X Y : B} (f : S ⟶ X) (g : X ⟶ Y) :
    F.whiskerBaseChange (t := f) (l := f) (r := g) (b := g) ⟨by simp⟩ =
      (α_ _ _ _).inv ≫ (F.map f).adj.counit ▷ _ ≫ (λ_ _).hom := by
  simp [whiskerBaseChange_eq, Adjunction.homEquiv₁_apply, baseChange_self_self]

variable {Z : B} (b' : X₂ ⟶ Z) (r' : Y₁ ⟶ Z) (d : Y₂ ⟶ Z)
  (hbd : b ≫ d = b') (hrd : r ≫ d = r')

lemma baseChange_id_left (b' : X₁ ⟶ Y₂) (hlb : l ≫ b = b') :
    F.baseChange (t := t) (l := 𝟙 _) (r := r) (b := b') ⟨by simpa [hlb] using sq.1⟩ =
      (F.mapId _).inv.τr ▷ _ ≫
      (F.map l).adj.unit ▷ _ ≫
      (α_ _ _ _).hom ≫
      _ ◁ F.baseChange sq ≫
      (α_ _ _ _).inv ≫
      (F.mapComp' l b b' hlb).inv.τl ▷ _ :=
  sorry

lemma baseChange_id_comp :
    F.baseChange (t := 𝟙 Y₁) (l := r) (r := r ≫ d) (b := d) (by simp) =
      (F.map r).r ◁ ((F.comp Adj.forget₁).mapId _).hom ≫
      (ρ_ _).hom ≫ (λ_ _).inv ≫
      (F.map d).adj.unit ▷ _ ≫
      (α_ _ _ _).hom ≫
      (F.map d).l ◁ (Adj.forget₂.map₂ (F.mapComp r d).hom.op) :=
  sorry

lemma baseChange_of_comp_eq :
    F.baseChange (l := l) (t := t) (b := b') (r := r') ⟨by rw [← hrd, ← hbd, sq.w_assoc]⟩ =
      F.baseChange sq ≫ (F.map b).l ◁ ((λ_ _).inv ≫ (F.map d).adj.unit ▷ _) ≫
      ((F.map b).l ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫
      _ ◁ (Adj.forget₂.map₂ (F.mapComp' _ _ _ hrd).hom.op) ≫
        ((F.comp Adj.forget₁).mapComp' _ _ _ hbd).inv ▷ (F.map r').r := by
  subst hbd hrd
  let sq'' : CommSq t l (r ≫ d) (b ≫ d) := ⟨by rw [sq.w_assoc]⟩
  let sq' : CommSq (𝟙 _) r (r ≫ d) d := ⟨by simp⟩
  have : sq'' = sq.horiz_comp' sq' (by simp) rfl := rfl
  show F.baseChange (sq.horiz_comp' sq' (by simp) rfl) = _
  rw [F.baseChange_horiz_comp' sq sq' (by simp) rfl]
  simp only [Adj.forget₁_obj, Adj.forget₁_map, Adj.comp_l, comp_toPrelaxFunctor,
    PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
    Prefunctor.comp_obj, Prefunctor.comp_map, Bicategory.whiskerLeft_comp, Adj.forget₂_map,
    Quiver.Hom.unop_op', comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  rw [F.baseChange_id_comp]
  simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Adj.forget₂_map, Quiver.Hom.unop_op', comp_mapId,
    Adj.id_l, Iso.trans_hom, Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map,
    Bicategory.whiskerLeft_comp, Category.assoc, whiskerLeft_rightUnitor]
  simp_rw [← Category.assoc]
  rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp]
  congr 6
  simp only [Category.assoc]
  have : (Adj.forget₁.mapId (F.obj Y₁)).hom = 𝟙 _ := rfl
  rw [this]
  simp only [Adj.forget₁_obj, Adj.forget₁_map, Adj.id_l, Bicategory.whiskerLeft_id,
    Category.id_comp]
  rw [mapComp'_comp_id]
  have : (Adj.forget₁.mapId (F.obj Y₁)).inv = 𝟙 _ := rfl
  simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, comp_mapId, Adj.id_l, Iso.trans_symm, Iso.trans_hom,
    Iso.symm_hom, whiskerLeftIso_hom, this, Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map,
    Category.id_comp, Bicategory.whiskerLeft_comp, whiskerLeft_rightUnitor_inv, Category.assoc]
  rw [← comp_whiskerLeft_assoc, whisker_exchange_assoc, comp_whiskerLeft]
  simp only [Bicategory.whiskerRight_id, Category.assoc]
  simp [← Bicategory.whiskerLeft_comp_assoc, ← Bicategory.whiskerLeft_comp]

lemma whiskerRight_whiskerBaseChange :
    F.whiskerBaseChange sq ▷ (F.map d).l =
      (α_ _ _ _).hom ≫
      (F.map l).r ◁ ((α_ _ _ _).hom ≫ (F.map t).l ◁ ((F.comp Adj.forget₁).mapComp' _ _ _ hrd).inv) ≫
      F.whiskerBaseChange (l := l) (t := t) (b := b') (r := r') ⟨by rw [← hrd, ← hbd, sq.w_assoc]⟩ ≫
      ((F.comp Adj.forget₁).mapComp' _ _ _ hbd).hom := by
  dsimp
  simp only [Bicategory.whiskerLeft_comp, Category.assoc]
  simp only [whiskerBaseChange_eq', Adjunction.homEquiv₂_symm_apply,
    comp_whiskerRight, whisker_assoc, Category.assoc,
    triangle_assoc_comp_right]
  rw [F.baseChange_of_comp_eq sq b' r' d hbd hrd]
  simp [Adj.comp_forget₁_mapComp']
  rw [Bicategory.associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]
  simp only [Bicategory.whiskerRight_comp, comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
    pentagon_hom_inv_inv_inv_inv_assoc, Iso.hom_inv_id_assoc]
  congr 2
  dsimp
  rw [← Bicategory.associator_inv_naturality_left_assoc,
    Iso.inv_hom_id_assoc, ← whisker_exchange_assoc,
    Bicategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc,
    Adj.inv_hom_id_τl]
  dsimp
  rw [Category.comp_id, comp_whiskerLeft_assoc, Iso.inv_hom_id_assoc]
  simp only [← Bicategory.whiskerLeft_comp_assoc,
    Category.assoc]
  rw [Adj.unit_comp_mapComp'_hom_τr_comp_counit F r d r' hrd,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, ← Bicategory.whiskerLeft_comp_assoc,
    Adj.inv_hom_id_τl]
  simp

end

section Codiag

variable {S X Y : B} (f : S ⟶ X) (r b : X ⟶ Y) (sq : CommSq f f r b) (d : Y ⟶ X)
    (hrd : r ≫ d = 𝟙 _) (hbd : b ≫ d = 𝟙 _)

lemma whiskerRight_whiskerBaseChange_self_self :
    F.whiskerBaseChange sq ▷ (F.map d).l  =
    ((α_ _ _ _).inv ≫ (F.map f).adj.counit ▷ (F.map r).l ≫ (λ_ _).hom) ▷ (F.map d).l ≫
    ((F.comp Adj.forget₁).mapComp' r d (𝟙 X) hrd).inv ≫
    ((F.comp Adj.forget₁).mapComp' b d (𝟙 X) hbd).hom := by
  rw [F.whiskerRight_whiskerBaseChange sq _ _ _ hbd hrd, whiskerBaseChange_self_self]
  let a := ((F.map f).r ≫ (F.map f).l) ◁ ((F.comp Adj.forget₁).mapComp' r d (𝟙 X) hrd).inv ≫
    (F.map f).adj.counit ▷ _
  let b := ((F.comp Adj.forget₁).mapComp' b d (𝟙 X) hbd).hom
  dsimp at a b ⊢
  trans 𝟙 _ ⊗≫ a ⊗≫ b ⊗≫ 𝟙 _ <;> dsimp [a, b]
  · simp [bicategoricalComp] -- why does not `bicategory` work?!
  · rw [whisker_exchange]
    simp [bicategoricalComp]

end Codiag

section Triple

variable {S X₁ X₂ X₃ : B} {f₁ : S ⟶ X₁} {f₂ : S ⟶ X₂} {f₃ : S ⟶ X₃}
  {P₁₂ P₂₃ P₁₃ P₁₂₃ : B}
  {u₁₂ : X₁ ⟶ P₁₂} {u₂₁ : X₂ ⟶ P₁₂} {u₂₃ : X₂ ⟶ P₂₃} {u₃₂ : X₃ ⟶ P₂₃}
  {u₁₃ : X₁ ⟶ P₁₃} {u₃₁ : X₃ ⟶ P₁₃}
  {p₁₂ : P₁₂ ⟶ P₁₂₃} {p₂₃ : P₂₃ ⟶ P₁₂₃} {p₁₃ : P₁₃ ⟶ P₁₂₃}
  (sq₁₂ : CommSq f₁ f₂ u₁₂ u₂₁)
  (sq₂₃ : CommSq f₂ f₃ u₂₃ u₃₂)
  (sq₁₃ : CommSq f₁ f₃ u₁₃ u₃₁)
  (h₁₃₁₂ : CommSq u₁₃ u₁₂ p₁₃ p₁₂)
  (h₂₁₂₃ : CommSq u₂₁ u₂₃ p₁₂ p₂₃)
  (h₃₂₃₁ : CommSq u₃₂ u₃₁ p₂₃ p₁₃)
  (p₁ : X₁ ⟶ P₁₂₃) (p₂ : X₂ ⟶ P₁₂₃) (p₃ : X₃ ⟶ P₁₂₃)
  (hp₁ : u₁₂ ≫ p₁₂ = p₁)
  (hp₂ : u₂₃ ≫ p₂₃ = p₂)
  (hp₃ : u₃₂ ≫ p₂₃ = p₃)

-- TODO: this lemma should not be needed, but `bicategory` can't prove this
omit [Strict B] in
@[reassoc]
private lemma aux (x : (F.map f₃).r ≫ (F.map f₁).l ⟶ (F.map u₃₁).l ≫ (F.map u₁₃).r) :
    (ρ_ (F.map f₃)).hom.τr ▷ (F.map f₁).l ≫
      (F.map f₃ ◁ (F.mapId X₃).hom).τr ▷ (F.map f₁).l ≫
        (α_ (F.map (𝟙 X₃)).r (F.map f₃).r (F.map f₁).l).hom ≫
          (F.map (𝟙 X₃)).r ◁ x = x ≫ (λ_ _).inv ≫
            (F.mapId _).hom.τr ▷ _ := by
  have : (ρ_ (F.map f₃)).hom.τr = (λ_ _).inv := rfl
  rw [this]
  dsimp
  simp only [Bicategory.whiskerRight_comp]
  rw [← cancel_mono (α_ (F.map (𝟙 X₃)).r (F.map u₃₁).l (F.map u₁₃).r).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [whiskerRight_comp_symm]
  simp_rw [Category.assoc]
  rw [Iso.inv_hom_id_assoc, whiskerRight_comp_symm, Iso.inv_hom_id_assoc, ← whisker_exchange_assoc]
  simp

lemma baseChange_triple' :
    F.baseChange sq₁₃ ≫
      (F.map u₃₁).l ◁ (λ_ _).inv ≫ (F.map u₃₁).l ◁ ((F.map p₁₃).adj.unit ▷ (F.map u₁₃).r) ≫
      (F.map u₃₁).l ◁ (α_ _ _ _).hom ≫
      (α_ _ _ _).inv ≫
      (F.mapComp' u₃₁ p₁₃ p₃ (hp₃ ▸ h₃₂₃₁.1.symm)).inv.τl ▷ _ ≫
      _ ◁ (F.mapComp' u₁₃ p₁₃ p₁ (hp₁ ▸ h₁₃₁₂.1)).hom.τr =
    (F.map f₃).r ◁ (λ_ _).inv ≫ (F.map f₃).r ◁ ((F.map f₂).adj.unit ▷ (F.map f₁).l) ≫
      (F.map f₃).r ◁ (α_ _ _ _).hom ≫
      (F.map f₃).r ◁ (F.map f₂).l ◁ F.baseChange sq₁₂ ≫
      (α_ _ _ _).inv ≫
      (F.baseChange sq₂₃) ▷ ((F.map u₂₁).l ≫ (F.map u₁₂).r) ≫
      (α_ _ _ _).hom ≫
      (F.map u₃₂).l ◁ (α_ _ _ _).inv ≫
      (F.map u₃₂).l ◁ (F.baseChange h₂₁₂₃ ▷ (F.map u₁₂).r) ≫
      (F.map u₃₂).l ◁ (α_ _ _ _).hom ≫
      (F.map u₃₂).l ◁ (F.map p₂₃).l ◁ (F.mapComp' u₁₂ p₁₂ p₁ hp₁).hom.τr ≫
      (α_ _ _ _).inv ≫
      (F.mapComp' u₃₂ p₂₃ p₃ hp₃).inv.τl ▷ (F.map p₁).r := by
  let sq₃₁₃ : CommSq u₃₁ (𝟙 X₃) p₁₃ p₃ := ⟨by simp [← hp₃, h₃₂₃₁.1]⟩
  let bigsq : CommSq f₁ f₃ p₁ p₃ := sq₁₃.vert_comp' sq₃₁₃ (by simp) (by simp [← hp₁, h₁₃₁₂.1])
  trans F.baseChange bigsq
  · rw [F.baseChange_vert_comp' (sq := sq₁₃) (sq' := sq₃₁₃) (l'' := f₃) (r'' := p₁) (by simp)
      (by simp [← hp₁, h₁₃₁₂.1])]
    simp only [Adj.forget₂_obj, Adj.forget₂_map, Quiver.Hom.unop_op', Adj.comp_r, Adj.forget₂_map₂,
      Quiver.Hom.unop_op]
    rw [mapComp'_comp_id]
    simp only [Iso.trans_inv, whiskerLeftIso_inv, Iso.symm_inv, Adj.comp_τr, Adj.comp_r, Adj.id_r,
      comp_whiskerRight, Category.assoc]
    rw [F.baseChange_id_left (t := u₃₁) (b' := p₃) (r := p₁₃) (l := u₃₁) (b := p₁₃) (by simp)
      (by simp [← hp₃, h₃₂₃₁.1])]
    rw [F.baseChange_self_self]
    simp only [Adj.comp_l, Bicategory.whiskerRight_comp, Category.assoc,
      pentagon_hom_inv_inv_inv_inv_assoc, Adj.id_r, Bicategory.whiskerLeft_comp,
      Adjunction.whiskerRight_unit_associator_whiskerLeft_counit_assoc, comp_whiskerRight,
      leftUnitor_whiskerRight, whisker_assoc, triangle_assoc_comp_right_inv_assoc]
    rw [aux_assoc]
    simp [← comp_whiskerRight_assoc, ← comp_whiskerRight]
  · let sqtl : CommSq (𝟙 _) (𝟙 _) f₂ f₂ := ⟨rfl⟩
    have := F.baseChange_square sqtl sq₁₂ sq₂₃ h₂₁₂₃ bigsq (by simp) (by simp) hp₁ hp₃
    rw [this]
    rw [baseChange_id_id_eq_unit]
    simp only [Adj.comp_r, mapComp'_id_comp, Iso.trans_inv, whiskerRightIso_inv, Iso.symm_inv,
      Adj.comp_τr, Adj.id_r, Adj.whiskerRight_τr', comp_whiskerRight, whisker_assoc, Adj.comp_l,
      Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Adj.comp_τl, Adj.id_l, Adj.whiskerRight_τl',
      Bicategory.whiskerLeft_comp, Category.assoc, triangle_assoc_comp_right_assoc,
      whiskerLeft_inv_hom_assoc, Iso.inv_hom_id_assoc, Bicategory.whiskerRight_comp,
      pentagon_hom_inv_inv_inv_inv_assoc, pentagon_hom_hom_inv_hom_hom_assoc]
    have :
      (λ_ (F.map f₃)).hom.τr ▷ (F.map f₁).l ≫
        (α_ (F.map f₃).r (𝟙 (F.obj S).obj) (F.map f₁).l).hom ≫
        (F.map f₃).r ◁ (F.mapId S).hom.τr ▷ (F.map f₁).l ≫
        (F.map f₃).r ◁ (F.map (𝟙 S)).r ◁ (λ_ (F.map f₁)).inv.τl ≫
        (F.map f₃).r ◁ (F.map (𝟙 S)).r ◁ (F.mapId S).inv.τl ▷ (F.map f₁).l ≫
        (F.map f₃).r ◁ (F.map (𝟙 S)).r ◁ (F.mapId S).hom.τl ▷ (F.map f₁).l ≫
        (F.map f₃).r ◁ (F.map (𝟙 S)).r ◁ (λ_ (F.map f₁).l).hom ≫
        (F.map f₃).r ◁ (F.mapId S).inv.τr ▷ (F.map f₁).l =
        (F.map f₃).r ◁ (λ_ (F.map f₁).l).inv := by
      nth_rw 3 [← Bicategory.whiskerLeft_comp_assoc (F.map f₃).r]
      rw [← Bicategory.whiskerLeft_comp (F.map (𝟙 S)).r]
      rw [← Bicategory.comp_whiskerRight, Adj.inv_hom_id_τl]
      have : (λ_ (F.map f₁)).inv.τl = (λ_ _).inv := rfl
      simp only [Adj.id_r, Adj.comp_r, Adj.comp_l, Adj.id_l, this, id_whiskerRight,
        Bicategory.whiskerLeft_id, Category.id_comp]
      nth_rw 2 [← Bicategory.whiskerLeft_comp_assoc (F.map f₃).r]
      rw [← Bicategory.whiskerLeft_comp (F.map (𝟙 S)).r]
      simp only [Iso.inv_hom_id, Bicategory.whiskerLeft_id, Category.id_comp]
      nth_rw 1 [← Bicategory.whiskerLeft_comp (F.map f₃).r]
      rw [← Bicategory.comp_whiskerRight]
      have : (λ_ (F.map f₃)).hom.τr = (ρ_ _).inv := rfl
      simp [this]
    rw [reassoc_of% this]

-- TODO: improve this, intentionally ungolfed for now
lemma baseChange_triple :
    F.baseChange sq₁₃ ≫
      (F.map u₃₁).l ◁ (λ_ _).inv ≫ (F.map u₃₁).l ◁ ((F.map p₁₃).adj.unit ▷ (F.map u₁₃).r) ≫
      (F.map u₃₁).l ◁ (α_ _ _ _).hom =
    (F.map f₃).r ◁ (λ_ _).inv ≫ (F.map f₃).r ◁ ((F.map f₂).adj.unit ▷ (F.map f₁).l) ≫
      (F.map f₃).r ◁ (α_ _ _ _).hom ≫
      (F.map f₃).r ◁ (F.map f₂).l ◁ F.baseChange sq₁₂ ≫
      (α_ _ _ _).inv ≫
      (F.baseChange sq₂₃) ▷ ((F.map u₂₁).l ≫ (F.map u₁₂).r) ≫
      (α_ _ _ _).hom ≫
      (F.map u₃₂).l ◁ (α_ _ _ _).inv ≫
      (F.map u₃₂).l ◁ (F.baseChange h₂₁₂₃ ▷ (F.map u₁₂).r) ≫
      (F.map u₃₂).l ◁ (α_ _ _ _).hom ≫
      (α_ _ _ _).inv ≫
      (F.isoMapOfCommSq h₃₂₃₁).hom.τl ▷ _ ≫
      (α_ _ _ _).hom ≫
      _ ◁ _ ◁ (F.isoMapOfCommSq h₁₃₁₂).hom.τr := by
  let p₁ : X₁ ⟶ P₁₂₃ := u₁₂ ≫ p₁₂
  let p₃ : X₃ ⟶ P₁₂₃ := u₃₂ ≫ p₂₃
  rw [← cancel_mono (α_ _ _ _).inv, ← cancel_mono ((F.mapComp' _ _ p₃ (h₃₂₃₁.1.symm)).inv.τl ▷ _)]
  rw [← cancel_mono (_ ◁ (F.mapComp' _ _ p₁ (h₁₃₁₂.1)).hom.τr)]
  simp_rw [Category.assoc]
  rw [F.baseChange_triple' sq₁₂ sq₂₃ sq₁₃ h₁₃₁₂ h₂₁₂₃ h₃₂₃₁ p₁ p₃ rfl rfl]
  rw [isoMapOfCommSq_eq _ _ p₁ h₁₃₁₂.1]
  rw [isoMapOfCommSq_eq _ _ p₃ rfl]
  simp only [Bicategory.whiskerRight_comp, Adj.comp_l, Category.assoc,
    pentagon_hom_hom_inv_hom_hom_assoc, Iso.trans_hom, Iso.symm_hom, Adj.comp_τl, comp_whiskerRight,
    Adj.comp_r, Adj.comp_τr, Bicategory.whiskerLeft_comp, pentagon_hom_inv_inv_inv_inv_assoc]
  congr 10
  rw [← pentagon_inv_assoc]
  rw [← pentagon_assoc]
  have :
      (F.map u₃₁).l ◁ (F.map p₁₃).l ◁ (F.mapComp' u₁₃ p₁₃ p₁ h₁₃₁₂.1).inv.τr ≫
      (α_ (F.map u₃₁).l (F.map p₁₃).l ((F.map p₁₃).r ≫ (F.map u₁₃).r)).inv ≫
      (α_ ((F.map u₃₁).l ≫ (F.map p₁₃).l) (F.map p₁₃).r (F.map u₁₃).r).inv ≫
      (F.mapComp' u₃₁ p₁₃ p₃ (h₃₂₃₁.1.symm)).inv.τl ▷ (F.map p₁₃).r ▷ (F.map u₁₃).r =
      (α_ _ _ _).inv ≫
      (F.mapComp' u₃₁ p₁₃ p₃ (h₃₂₃₁.1.symm)).inv.τl ▷ (F.map p₁).r ≫
      (F.map p₃).l ◁ (F.mapComp' u₁₃ p₁₃ p₁ h₁₃₁₂.1).inv.τr ≫
      (α_ _ _ _).inv := by
    rw [← whisker_exchange_assoc]
    simp
  have : (F.mapComp' u₃₁ p₁₃ p₃ (h₃₂₃₁.1.symm)).hom.τl ▷ (F.map p₁₂).r ▷ (F.map u₁₂).r ≫
          (α_ (F.map u₃₁).l (F.map p₁₃).l (F.map p₁₂).r).hom ▷ (F.map u₁₂).r ≫
          (α_ (F.map u₃₁).l ((F.map p₁₃).l ≫ (F.map p₁₂).r) (F.map u₁₂).r).hom ≫
          (F.map u₃₁).l ◁ (α_ (F.map p₁₃).l (F.map p₁₂).r (F.map u₁₂).r).hom ≫
          (F.map u₃₁).l ◁ (F.map p₁₃).l ◁ (F.mapComp' u₁₂ p₁₂ p₁ rfl).hom.τr ≫
          (F.map u₃₁).l ◁ (F.map p₁₃).l ◁ (F.mapComp' u₁₃ p₁₃ p₁ h₁₃₁₂.1).inv.τr ≫
          (F.map u₃₁).l ◁ (α_ (F.map p₁₃).l (F.map p₁₃).r (F.map u₁₃).r).inv ≫
          (α_ (F.map u₃₁).l ((F.map p₁₃).l ≫ (F.map p₁₃).r) (F.map u₁₃).r).inv ≫
          (α_ (F.map u₃₁).l (F.map p₁₃).l (F.map p₁₃).r).inv ▷ (F.map u₁₃).r ≫
          (F.mapComp' u₃₁ p₁₃ p₃ (h₃₂₃₁.1.symm)).inv.τl ▷ (F.map p₁₃).r ▷ (F.map u₁₃).r =
          (F.mapComp' u₃₁ p₁₃ p₃ (h₃₂₃₁.1.symm)).hom.τl ▷ (F.map p₁₂).r ▷ (F.map u₁₂).r ≫
          (F.mapComp' u₃₁ p₁₃ p₃ (h₃₂₃₁.1.symm)).inv.τl ▷ _ ▷ _ ≫
          (α_ _ _ _).hom ≫
          (F.map p₃).l ◁ (F.mapComp' u₁₂ p₁₂ p₁ rfl).hom.τr ≫
          (F.map p₃).l ◁ (F.mapComp' u₁₃ p₁₃ p₁ h₁₃₁₂.1).inv.τr ≫
          (α_ _ _ _).inv := by
    congr 1
    simp only [Adj.comp_l, Adj.comp_r, pentagon_inv_assoc, pentagon_assoc]
    rw [this]
    have :
        (F.map u₃₁).l ◁ (F.map p₁₃).l ◁ (F.mapComp' u₁₂ p₁₂ p₁ rfl).hom.τr ≫
          (α_ _ _ _).inv ≫
          (F.mapComp' u₃₁ p₁₃ p₃ h₃₂₃₁.1.symm).inv.τl ▷ (F.map p₁).r =
          (α_ _ _ _).inv ≫
          (F.mapComp' u₃₁ p₁₃ p₃ h₃₂₃₁.1.symm).inv.τl ▷ _ ≫
          _ ◁ (F.mapComp' u₁₂ p₁₂ p₁ rfl).hom.τr := by
      rw [← whisker_exchange]
      simp
    rw [reassoc_of% this]
    simp
  rw [reassoc_of% this]
  nth_rw 3 [← Bicategory.comp_whiskerRight_assoc]
  rw [← Bicategory.comp_whiskerRight]
  simp only [Adj.comp_l, Adj.hom_inv_id_τl, id_whiskerRight, Adj.comp_r, Iso.inv_hom_id_assoc,
    Category.id_comp]
  rw [← Bicategory.whiskerLeft_comp]
  simp only [Adj.inv_hom_id_τr, Bicategory.whiskerLeft_id, Category.comp_id]
  have :
      (F.mapComp' u₃₂ p₂₃ p₃ rfl).inv.τl ▷ (F.map p₁₂).r ▷ (F.map u₁₂).r ≫
        (α_ (F.map p₃).l (F.map p₁₂).r (F.map u₁₂).r).hom ≫
        (F.map p₃).l ◁ (F.mapComp' u₁₂ p₁₂ p₁ rfl).hom.τr =
        (α_ _ _ _).hom ≫
        (F.map u₃₂ ≫ F.map p₂₃).l ◁ (F.mapComp' u₁₂ p₁₂ p₁ rfl).hom.τr ≫
        (F.mapComp' u₃₂ p₂₃ p₃ rfl).inv.τl ▷ (F.map p₁).r := by
    rw [whisker_exchange]
    simp
  simp [this]

end Triple

end Pseudofunctor

end CategoryTheory
