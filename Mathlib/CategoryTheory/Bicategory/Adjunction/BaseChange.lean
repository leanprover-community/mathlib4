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
lemma Adjuction.whiskerRight_unit_whiskerLeft_counit (adj₁ : Adjunction l₁ r₁) :
    adj₁.unit ▷ l₁ ⊗≫ l₁ ◁ adj₁.counit = (λ_ l₁).hom ≫ (ρ_ l₁).inv :=
  adj₁.left_triangle

@[reassoc (attr := simp)]
lemma Adjuction.whiskerRight_unit_associator_whiskerLeft_counit (adj₁ : Adjunction l₁ r₁) :
    adj₁.unit ▷ l₁ ≫ (α_ _ _ _).hom ≫ l₁ ◁ adj₁.counit = (λ_ l₁).hom ≫ (ρ_ l₁).inv := by
  rw [← adj₁.left_triangle]
  bicategory

lemma mateEquiv_id (adj₁ : Adjunction l₁ r₁) (adj₂ : Adjunction l₂ r₂) :
    mateEquiv adj₁ adj₂ (𝟙 _) = adj₁.counit ≫ adj₂.unit := by
  apply (mateEquiv adj₁ adj₂).symm.injective
  simp only [Equiv.symm_apply_apply, mateEquiv_symm_apply, comp_whiskerRight, whiskerLeft_comp]
  calc
    _ = 𝟙 (l₁ ≫ l₂) ⊗≫ (adj₁.unit ▷ l₁ ⊗≫ l₁ ◁ adj₁.counit) ▷ l₂ ⊗≫
          l₁ ◁ (adj₂.unit ▷ l₂ ⊗≫ l₂ ◁ adj₂.counit) ⊗≫
          𝟙 (l₁ ≫ l₂) := by simp; bicategory
    _ = 𝟙 (l₁ ≫ l₂) ⊗≫ adj₁.unit ▷ l₁ ▷ l₂ ⊗≫ (l₁ ◁ adj₁.counit ▷ l₂ ≫ l₁ ◁ adj₂.unit ▷ l₂) ⊗≫
          l₁ ◁ l₂ ◁ adj₂.counit ⊗≫ 𝟙 (l₁ ≫ l₂) := by bicategory

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
  (F.map l).g ≫ (F.map t).f ⟶ (F.map b).f ≫ (F.map r).g :=
Bicategory.mateEquiv (F.map l).adj (F.map r).adj (F.isoMapOfCommSq sq).hom.τf

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
def whiskerBaseChange : (F.map l).g ≫ (F.map t).f ≫ (F.map r).f ⟶ (F.map b).f :=
  (α_ _ _ _).inv ≫ F.baseChange sq ▷ (F.map r).f ≫
    (α_ _ _ _).hom ≫ (F.map b).f ◁ (F.map r).adj.counit ≫ (ρ_ _).hom

-- is this true?
instance [IsIso (F.baseChange sq)] : Mono (F.whiskerBaseChange sq) := by
  dsimp [whiskerBaseChange]
  sorry

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
    (F.map l).g ◁ ((F.comp Adj.forget₁).mapComp' t t' t'' ht).hom ≫
    (α_ _ _ _).inv ≫
    baseChange F sq ▷ (F.map t').f ≫
    (α_ _ _ _).hom ≫
    (F.map b).f ◁ baseChange F sq' ≫
    (α_ _ _ _).inv ≫
    ((F.comp Adj.forget₁).mapComp' b b' b'' hb).inv ▷ (F.map r).g :=
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
    Adj.forget₂.map₂ (F.mapComp' l l' l'').inv.op ▷ (F.map t).f ≫
    (α_ _ _ _).hom ≫
    (F.map l').g ◁ baseChange F sq ≫
    (α_ _ _ _).inv ≫
    baseChange F sq' ▷ (F.map r).g ≫
    (α_ _ _ _).hom ≫
    _ ◁ Adj.forget₂.map₂ (F.mapComp' r r' r'').hom.op := by
  sorry

end Vertical

section

-- Never unfold the definition of `mateEquiv`, instead try to add general `mateEquiv` lemmas first.
attribute [-simp] Bicategory.mateEquiv_apply Bicategory.mateEquiv_symm_apply

lemma baseChange_self_self {S X Y : B} (f : S ⟶ X) (g : X ⟶ Y) :
    F.baseChange (l := f) (t := f) (b := g) (r := g) (by simp) =
      (F.map f).adj.counit ≫ (F.map g).adj.unit := by
  simp [baseChange, mateEquiv_id]

lemma whiskerBaseChange_self_self {S X Y : B} (f : S ⟶ X) (g : X ⟶ Y) :
    F.whiskerBaseChange (t := f) (l := f) (r := g) (b := g) ⟨by simp⟩ =
      (α_ _ _ _).inv ≫ (F.map f).adj.counit ▷ _ ≫ (λ_ _).hom := by
  simp [whiskerBaseChange, baseChange_self_self]

variable {Z : B} (b' : X₂ ⟶ Z) (r' : Y₁ ⟶ Z) (d : Y₂ ⟶ Z)
  (hbd : b ≫ d = b') (hrd : r ≫ d = r')

lemma baseChange_id_comp :
    F.baseChange (t := 𝟙 Y₁) (l := r) (r := r ≫ d) (b := d) (by simp) =
      (F.map r).g ◁ ((F.comp Adj.forget₁).mapId _).hom ≫
      (ρ_ _).hom ≫ (λ_ _).inv ≫
      (F.map d).adj.unit ▷ _ ≫
      (α_ _ _ _).hom ≫
      (F.map d).f ◁ (Adj.forget₂.map₂ (F.mapComp r d).hom.op) :=
  sorry

lemma baseChange_of_comp_eq :
    F.baseChange (l := l) (t := t) (b := b') (r := r') ⟨by rw [← hrd, ← hbd, sq.w_assoc]⟩ =
      F.baseChange sq ≫ (F.map b).f ◁ ((λ_ _).inv ≫ (F.map d).adj.unit ▷ _) ≫
      ((F.map b).f ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫
      _ ◁ (Adj.forget₂.map₂ (F.mapComp' _ _ _ hrd).hom.op) ≫
        ((F.comp Adj.forget₁).mapComp' _ _ _ hbd).inv ▷ (F.map r').g := by
  subst hbd hrd
  let sq'' : CommSq t l (r ≫ d) (b ≫ d) := ⟨by rw [sq.w_assoc]⟩
  let sq' : CommSq (𝟙 _) r (r ≫ d) d := ⟨by simp⟩
  have : sq'' = sq.horiz_comp' sq' (by simp) rfl := rfl
  show F.baseChange (sq.horiz_comp' sq' (by simp) rfl) = _
  rw [F.baseChange_horiz_comp' sq sq' (by simp) rfl]
  simp only [Adj.forget₁_obj, Adj.forget₁_map, Adj.comp_f, comp_toPrelaxFunctor,
    PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
    Prefunctor.comp_obj, Prefunctor.comp_map, Bicategory.whiskerLeft_comp, Adj.forget₂_map,
    Quiver.Hom.unop_op', comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  rw [F.baseChange_id_comp]
  simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Adj.forget₂_map, Quiver.Hom.unop_op', comp_mapId,
    Adj.id_f, Iso.trans_hom, Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map,
    Bicategory.whiskerLeft_comp, Category.assoc, whiskerLeft_rightUnitor]
  simp_rw [← Category.assoc]
  rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp]
  congr 6
  simp only [Category.assoc]
  have : (Adj.forget₁.mapId (F.obj Y₁)).hom = 𝟙 _ := rfl
  rw [this]
  --have : (F.mapId Y₁).hom.f = 𝟙 _ := sorry
  simp only [Adj.forget₁_obj, Adj.forget₁_map, Adj.id_f, Bicategory.whiskerLeft_id,
    Category.id_comp]
  rw [mapComp'_comp_id]
  have : (Adj.forget₁.mapId (F.obj Y₁)).inv = 𝟙 _ := rfl
  simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, comp_mapId, Adj.id_f, Iso.trans_symm, Iso.trans_hom,
    Iso.symm_hom, whiskerLeftIso_hom, this, Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map,
    Category.id_comp, Bicategory.whiskerLeft_comp, whiskerLeft_rightUnitor_inv, Category.assoc]
  rw [← comp_whiskerLeft_assoc, whisker_exchange_assoc, comp_whiskerLeft]
  simp only [Bicategory.whiskerRight_id, Category.assoc, Iso.inv_hom_id_assoc]
  simp [← Bicategory.whiskerLeft_comp_assoc, ← Bicategory.whiskerLeft_comp]

lemma whiskerRight_whiskerBaseChange :
    F.whiskerBaseChange sq ▷ (F.map d).f =
      (α_ _ _ _).hom ≫
      (F.map l).g ◁ ((α_ _ _ _).hom ≫ (F.map t).f ◁ ((F.comp Adj.forget₁).mapComp' _ _ _ hrd).inv) ≫
      F.whiskerBaseChange (l := l) (t := t) (b := b') (r := r') ⟨by rw [← hrd, ← hbd, sq.w_assoc]⟩ ≫
      ((F.comp Adj.forget₁).mapComp' _ _ _ hbd).hom := by
  dsimp
  simp only [Bicategory.whiskerLeft_comp, Category.assoc]
  simp only [whiskerBaseChange, comp_whiskerRight, whisker_assoc, Category.assoc,
    triangle_assoc_comp_right]
  rw [F.baseChange_of_comp_eq sq b' r' d hbd hrd]
  simp
  sorry

end

section Codiag

variable {S X Y : B} (f : S ⟶ X) (r b : X ⟶ Y) (sq : CommSq f f r b) (d : Y ⟶ X)
    (hrd : r ≫ d = 𝟙 _) (hbd : b ≫ d = 𝟙 _)

lemma whiskerRight_whiskerBaseChange_self_self :
    F.whiskerBaseChange sq ▷ (F.map d).f  =
    ((α_ _ _ _).inv ≫ (F.map f).adj.counit ▷ (F.map r).f ≫ (λ_ _).hom) ▷ (F.map d).f ≫
    ((F.comp Adj.forget₁).mapComp' r d (𝟙 X) hrd).inv ≫
    ((F.comp Adj.forget₁).mapComp' b d (𝟙 X) hbd).hom := by
  rw [F.whiskerRight_whiskerBaseChange sq _ _ _ hbd hrd, whiskerBaseChange_self_self]
  simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Bicategory.whiskerLeft_comp, Category.assoc,
    comp_whiskerRight, leftUnitor_whiskerRight]
  simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
  let a := ((F.map f).g ≫ (F.map f).f) ◁ ((F.comp Adj.forget₁).mapComp' r d (𝟙 X) hrd).inv ≫
    (F.map f).adj.counit ▷ _
  dsimp at a
  trans 𝟙 _ ⊗≫ a ⊗≫ 𝟙 _
  · dsimp [a]
    simp
    simp [bicategoricalComp] -- why does not `bicategory` work?!
  · dsimp [a]
    rw [whisker_exchange]
    simp [bicategoricalComp]

end Codiag

section Triple

variable {S X₁ X₂ X₃ : B} {f₁ : S ⟶ X₁} {f₂ : S ⟶ X₂} {f₃ : S ⟶ X₃}
  {P₁₂ P₂₃ P₁₃ P₁₂₃ : B} {p₁ : X₁ ⟶ P₁₂₃} {p₂ : X₂ ⟶ P₁₂₃} {p₃ : X₃ ⟶ P₁₂₃}
  {u₁₂ : X₁ ⟶ P₁₂} {u₂₁ : X₂ ⟶ P₁₂} {u₂₃ : X₂ ⟶ P₂₃} {u₃₂ : X₃ ⟶ P₂₃}
  {u₁₃ : X₁ ⟶ P₁₃} {u₃₁ : X₃ ⟶ P₁₃}
  {p₁₂ : P₁₂ ⟶ P₁₂₃} {p₂₃ : P₂₃ ⟶ P₁₂₃} {p₁₃ : P₁₃ ⟶ P₁₂₃}
  (sq₁₂ : CommSq f₁ f₂ u₁₂ u₂₁)
  (sq₂₃ : CommSq f₂ f₃ u₂₃ u₃₂)
  (sq₁₃ : CommSq f₁ f₃ u₁₃ u₃₁)
  (h₁₃₁₂ : CommSq u₁₃ u₁₂ p₁₃ p₁₂)
  (h₂₁₂₃ : CommSq u₂₁ u₂₃ p₁₂ p₂₃)
  (h₃₂₃₁ : CommSq u₃₂ u₃₁ p₂₃ p₁₃)

lemma whiskerRight_whiskerBaseChange_triple :
    F.whiskerBaseChange sq₁₃ ▷ (F.map p₁₃).f =
      (α_ _ _ _).inv ▷ (F.map p₁₃).f ≫
      ((F.map f₃).g ◁ (λ_ _).inv) ▷ (F.map u₁₃).f ▷ (F.map p₁₃).f ≫
      ((F.map f₃).g ◁ ((F.map f₂).adj.unit ▷ (F.map f₁).f)) ▷ (F.map u₁₃).f ▷ (F.map p₁₃).f ≫
      (α_ _ _ _).hom ≫
      (α_ _ _ _).hom ≫
      (F.map f₃).g ◁ (α_ _ _ _).inv ≫
      (F.map f₃).g ◁ ((α_ _ _ _).hom ▷ (F.map p₁₃).f) ≫
      (F.map f₃).g ◁ ((α_ _ _ _).hom ▷ (F.map p₁₃).f) ≫
      (F.map f₃).g ◁ (α_ _ _ _).hom ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ (α_ _ _ _).hom ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ (F.map f₂).g ◁ (α_ _ _ _).hom ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ (F.map f₂).g ◁ (F.map f₁).f ◁
        ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ (F.map f₂).g ◁ (α_ _ _ _).inv ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ (α_ _ _ _).inv ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ (F.whiskerBaseChange sq₁₂ ▷ (F.map p₁₂).f) ≫
      (F.map f₃).g ◁ (F.map f₂).f ◁ ((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom ≫
      (F.map f₃).g ◁ (α_ _ _ _).inv ≫
      (α_ _ _ _).inv ≫
      (F.whiskerBaseChange sq₂₃) ▷ (F.map p₂₃).f ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₃₂₃₁).hom := by
  sorry

end Triple

section

variable {B C : Type*} [Bicategory B] [Strict B] [Bicategory C] (F : Pseudofunctor B (Adj Cat))

variable {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂}
  {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b)

/--
Given a commutative square,
```
  t
 X₁ ⟶ Y₁
l|    |r
 v     v
 X₂ ⟶ Y₂
    b
```
any morphism `M ⟶ t^* l_* N` induces a morphism `r^* M ⟶ b^* N`. This is the morphism
constructed from a `DescentDataAsCoalgebra` to form a `DescentData'`.
-/
def coalgHom {M : (F.obj Y₁).obj} {N : (F.obj X₂).obj}
    (a : M ⟶ (F.map t).f.obj ((F.map l).g.obj N)) :
    (F.map r).f.obj M ⟶ (F.map b).f.obj N :=
  (F.map r).f.map a ≫ (F.whiskerBaseChange sq).app _

/-- If the base change morphism is an isomorphism, `coalgHom sq` is an equivalence. -/
noncomputable
def coalgEquiv [IsIso (F.baseChange sq)]
    (M : (F.obj Y₁).obj) (N : (F.obj X₂).obj) :
    (M ⟶ (F.map t).f.obj ((F.map l).g.obj N)) ≃ ((F.map r).f.obj M ⟶ (F.map b).f.obj N) where
  toFun a := (F.map r).f.map a ≫ (F.whiskerBaseChange sq).app N
  invFun a := (F.map r).adj.unit.app _ ≫ (F.map r).g.map a ≫ inv ((F.baseChange sq).app _)
  left_inv a := by
    dsimp [whiskerBaseChange]
    simp only [Functor.map_comp, Category.assoc]
    simp only [Cat.associator_inv_app, Cat.comp_obj, eqToHom_refl, Functor.map_id,
      Cat.associator_hom_app, Cat.rightUnitor_hom_app, Cat.id_obj, Category.id_comp]
    rw [← Cat.comp_map, ← (F.map r).adj.unit.naturality_assoc]
    simp only [Cat.id_obj, Cat.id_map, Cat.comp_obj]
    rw [← Cat.comp_map, ← (F.map r).adj.unit.naturality_assoc]
    have := congr($((F.map r).adj.right_triangle).app ((F.map b).f.obj N))
    dsimp only [Cat.comp_obj, Cat.id_obj, rightZigzag, bicategoricalComp,
      BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.whiskerRight_iso,
      BicategoricalCoherence.refl_iso, Iso.trans_hom, whiskerRightIso_hom, Iso.refl_hom,
      Iso.symm_hom, Cat.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.id_app,
      Cat.comp_map, Cat.associator_inv_app, eqToHom_refl, Cat.rightUnitor_hom_app] at this
    simp only [Functor.map_id, Category.comp_id, Category.id_comp, Cat.leftUnitor_inv_app,
      Cat.comp_obj, Cat.id_obj, eqToHom_refl] at this
    rw [reassoc_of% this]
    simp
  right_inv a := by
    dsimp [whiskerBaseChange]
    simp only [Cat.associator_inv_app, Cat.comp_obj, eqToHom_refl, Functor.map_id,
      Cat.associator_hom_app, Cat.rightUnitor_hom_app, Cat.id_obj, Category.id_comp]
    simp only [Functor.map_comp, Functor.map_inv, Category.comp_id, Category.assoc,
      IsIso.inv_hom_id_assoc]
    rw [← Cat.comp_map, (F.map r).adj.counit.naturality]
    simp only [Cat.comp_obj, Cat.id_obj, Cat.id_map]
    -- TODO: specialize the `left_triangle` and `right_triangle` conditions
    -- for `Adj Cat` in `app`lied for
    have := congr($((F.map r).adj.left_triangle).app M)
    dsimp only [Cat.comp_obj, Cat.id_obj, leftZigzag, bicategoricalComp,
      BicategoricalCoherence.assoc_iso, BicategoricalCoherence.whiskerRight_iso,
      BicategoricalCoherence.refl_iso, Iso.trans_hom, whiskerRightIso_hom, Iso.refl_hom,
      Cat.comp_app, Cat.whiskerRight_app, Cat.id_app, Cat.comp_map, Cat.whiskerLeft_app] at this
    simp only [Cat.associator_hom_app, Cat.comp_obj, eqToHom_refl, Functor.map_id, Category.comp_id,
      Category.id_comp, Cat.leftUnitor_hom_app, Cat.id_obj, Cat.rightUnitor_inv_app] at this
    rw [reassoc_of% this]

@[simp]
lemma coalgHom_coalgEquiv_symm [IsIso (F.baseChange sq)] {M} {N}
    (a : (F.map r).f.obj M ⟶ (F.map b).f.obj N) :
    F.coalgHom sq ((F.coalgEquiv sq _ _).symm a) = a :=
  (F.coalgEquiv sq _ _).apply_symm_apply _

@[simp]
lemma coalgEquiv_symm_coalgHom_apply [IsIso (F.baseChange sq)] {M} {N}
    (a : M ⟶ (F.map t).f.obj ((F.map l).g.obj N)) :
    (F.coalgEquiv sq M N).symm (F.coalgHom sq a) = a :=
  (F.coalgEquiv sq M N).symm_apply_apply _

section

variable {S X Y : B} (f : S ⟶ X) (r b : X ⟶ Y) (sq : CommSq f f r b) (d : Y ⟶ X)
    (hrd : r ≫ d = 𝟙 _) (hbd : b ≫ d = 𝟙 _)

lemma map_coalgHom_of_comp_eq_id {M : (F.obj X).obj}
    (a : M ⟶ (F.map f).f.obj ((F.map f).g.obj M)) :
    (F.map d).f.map (F.coalgHom sq a) =
      (F.map d).f.map ((F.map r).f.map (a ≫ (F.map f).adj.counit.app M)) ≫
      ((F.comp Adj.forget₁).mapComp' r d (𝟙 _) hrd).inv.app _ ≫
      ((F.comp Adj.forget₁).mapComp' b d (𝟙 _) hbd).hom.app _ := by
  have := congr($(F.whiskerRight_whiskerBaseChange_self_self _ _ _ sq d hrd hbd).app M)
  dsimp only [Cat.comp_obj, Cat.whiskerRight_app, comp_toPrelaxFunctor,
    PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
    Prefunctor.comp_obj, Adj.forget₁_obj, Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_app,
    Cat.id_obj] at this
  simp only [coalgHom, Functor.map_comp, comp_toPrelaxFunctor,
    PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
    Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj]
  rw [this, Cat.associator_inv_app, Cat.leftUnitor_hom_app]
  simp only [Cat.comp_obj, eqToHom_refl, Cat.id_obj, Category.comp_id, Category.id_comp]
  simp_rw [← (F.map d).f.map_comp_assoc, ← (F.map r).f.map_comp]
  simp

lemma comp_counit_eq_id_iff {M : (F.obj X).obj} (a : M ⟶ (F.map f).f.obj ((F.map f).g.obj M)) :
    a ≫ (F.map f).adj.counit.app M = 𝟙 M ↔
      (F.map d).f.map (F.coalgHom sq a) =
        ((F.comp Adj.forget₁).mapComp' r d (𝟙 _) hrd).inv.app _ ≫
        ((F.comp Adj.forget₁).mapComp' b d (𝟙 _) hbd).hom.app _ := by
  rw [F.map_coalgHom_of_comp_eq_id _ _ _ sq _ hrd hbd]
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · simp [H]
  · have : Functor.Faithful ((F.map r).f ≫ (F.map d).f) := by
      have : Functor.Faithful (𝟙 ((F.comp Adj.forget₁).obj X)) :=
        inferInstanceAs <| (Functor.id _).Faithful
      exact Functor.Faithful.of_iso
        (((F.comp Adj.forget₁).mapId _).symm ≪≫ (F.comp Adj.forget₁).mapComp' r d (𝟙 _) hrd)
    apply ((F.map r).f ≫ (F.map d).f).map_injective
    simp only [Cat.comp_obj, Cat.id_obj, Cat.comp_map, Functor.map_comp, Functor.map_id]
    rw [← cancel_mono
      (((F.comp Adj.forget₁).mapComp' r d (𝟙 X) hrd).inv.app _ ≫
      ((F.comp Adj.forget₁).mapComp' b d (𝟙 X) hbd).hom.app _)]
    simp only [Cat.id_obj, comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
      PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
      Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj, Functor.map_comp, Category.assoc] at H
    simp [H]

end

section

variable {S X₁ X₂ X₃ : B} {f₁ : S ⟶ X₁} {f₂ : S ⟶ X₂} {f₃ : S ⟶ X₃}
  {P₁₂ P₂₃ P₁₃ P₁₂₃ : B} {p₁ : X₁ ⟶ P₁₂₃} {p₂ : X₂ ⟶ P₁₂₃} {p₃ : X₃ ⟶ P₁₂₃}
  {u₁₂ : X₁ ⟶ P₁₂} {u₂₁ : X₂ ⟶ P₁₂} {u₂₃ : X₂ ⟶ P₂₃} {u₃₂ : X₃ ⟶ P₂₃}
  {u₁₃ : X₁ ⟶ P₁₃} {u₃₁ : X₃ ⟶ P₁₃}
  {p₁₂ : P₁₂ ⟶ P₁₂₃} {p₂₃ : P₂₃ ⟶ P₁₂₃} {p₁₃ : P₁₃ ⟶ P₁₂₃}
  (sq₁₂ : CommSq f₁ f₂ u₁₂ u₂₁)
  (sq₂₃ : CommSq f₂ f₃ u₂₃ u₃₂)
  (sq₁₃ : CommSq f₁ f₃ u₁₃ u₃₁)
  (h₁₃₁₂ : CommSq u₁₃ u₁₂ p₁₃ p₁₂)
  (h₂₁₂₃ : CommSq u₂₁ u₂₃ p₁₂ p₂₃)
  (h₃₂₃₁ : CommSq u₃₂ u₃₁ p₂₃ p₁₃)

@[reassoc]
lemma map_coalgHom_comp_map_coalgHom {A₁ : (F.obj X₁).obj} {A₂ : (F.obj X₂).obj}
    {A₃ : (F.obj X₃).obj}
    (a₁₂ : A₁ ⟶ (F.map f₁).f.obj ((F.map f₂).g.obj A₂))
    (a₂₃ : A₂ ⟶ (F.map f₂).f.obj ((F.map f₃).g.obj A₃)) :
    (F.map p₁₂).f.map (F.coalgHom sq₁₂ a₁₂) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom.app _ ≫
      (F.map p₂₃).f.map (F.coalgHom sq₂₃ a₂₃) =
        (F.map p₁₂).f.map ((F.map u₁₂).f.map a₁₂) ≫
          (F.map p₁₂).f.map ((F.map u₁₂).f.map ((F.map f₁).f.map ((F.map f₂).g.map a₂₃))) ≫
          (F.map p₁₂).f.map ((F.whiskerBaseChange sq₁₂).app _) ≫
          ((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom.app _ ≫
          (F.map p₂₃).f.map ((F.whiskerBaseChange sq₂₃).app _) := by
  dsimp [coalgHom]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← (F.map p₁₂).f.map_comp_assoc, ← Cat.comp_map _ (F.map u₁₂).f]
  rw [← Cat.comp_map (F.map f₂).g, (F.whiskerBaseChange sq₁₂).naturality]
  simp only [Cat.comp_obj, Functor.map_comp, Category.assoc]
  congr 1
  rw [← Cat.comp_map _ (F.map p₁₂).f]
  -- defeq abuse of `(F.map p₁₂).f` and `(F.comp Adj.forget₁).map p₁₂`
  erw [((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom.naturality_assoc]
  simp

include sq₁₂ sq₂₃ h₁₃₁₂ h₂₁₂₃ h₃₂₃₁ in
lemma coalgHom_eq_coalgHom_coalgHom' {A₁ : (F.obj X₁).obj} {A₃ : (F.obj X₃).obj}
    (a₁₃ : A₁ ⟶ (F.map f₁).f.obj ((F.map f₃).g.obj A₃)) :
    (F.map p₁₃).f.map (F.coalgHom sq₁₃ a₁₃) =
      (F.map p₁₃).f.map ((F.map u₁₃).f.map a₁₃) ≫
      (F.map p₁₃).f.map ((F.map u₁₃).f.map ((F.map f₁).f.map ((F.map f₂).adj.unit.app _))) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.app _ ≫
      (F.map p₁₂).f.map ((F.whiskerBaseChange sq₁₂).app _) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom.app _ ≫
      (F.map p₂₃).f.map ((F.whiskerBaseChange sq₂₃).app A₃) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₃₂₃₁).hom.app A₃ := by
  dsimp [coalgHom]
  simp only [Functor.map_comp]
  have := congr($(F.whiskerRight_whiskerBaseChange_triple sq₁₂ sq₂₃ sq₁₃ h₁₃₁₂ h₂₁₂₃ h₃₂₃₁).app A₃)
  dsimp at this
  simp only [Cat.associator_inv_app, Cat.comp_obj, eqToHom_refl, Functor.map_id,
    Cat.leftUnitor_inv_app, Cat.id_obj, Cat.associator_hom_app, Category.id_comp] at this
  rw [this]

variable {A₁ : (F.obj X₁).obj} {A₂ : (F.obj X₂).obj}
  {A₃ : (F.obj X₃).obj}
  (a₁₃ : A₁ ⟶ (F.map f₁).f.obj ((F.map f₃).g.obj A₃))
  (a₁₂ : A₁ ⟶ (F.map f₁).f.obj ((F.map f₂).g.obj A₂))
  (a₂₃ : A₂ ⟶ (F.map f₂).f.obj ((F.map f₃).g.obj A₃))

lemma coalgHom_eq_coalgHom_coalgHom
    (H : a₁₂ ≫ (F.map f₁).f.map ((F.map f₂).g.map a₂₃) =
        a₁₃ ≫ (F.map f₁).f.map ((F.map f₂).adj.unit.app _)) :
    (F.map p₁₃).f.map (F.coalgHom sq₁₃ a₁₃) =
      ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.app _ ≫
      (F.map p₁₂).f.map (F.coalgHom sq₁₂ a₁₂) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom.app _ ≫
      (F.map p₂₃).f.map (F.coalgHom sq₂₃ a₂₃) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq h₃₂₃₁).hom.app _ := by
  rw [F.coalgHom_eq_coalgHom_coalgHom' sq₁₂ sq₂₃ sq₁₃ h₁₃₁₂ h₂₁₂₃ h₃₂₃₁]
  rw [map_coalgHom_comp_map_coalgHom_assoc]
  rw [← (F.map p₁₃).f.map_comp_assoc, ← (F.map u₁₃).f.map_comp, ← H]
  simp only [Cat.comp_obj, comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Functor.map_comp, Category.assoc]
  rw [← Cat.comp_map _ (F.map p₁₂).f]
  erw [← ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.naturality_assoc]
  erw [← ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.naturality_assoc]
  simp

lemma coalgHom_eq_coalgHom_coalgHom_iff :
    a₁₂ ≫ (F.map f₁).f.map ((F.map f₂).g.map a₂₃) =
      a₁₃ ≫ (F.map f₁).f.map ((F.map f₂).adj.unit.app _) ↔
        (F.map p₁₃).f.map (F.coalgHom sq₁₃ a₁₃) =
          ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.app _ ≫
          (F.map p₁₂).f.map (F.coalgHom sq₁₂ a₁₂) ≫
          ((F.comp Adj.forget₁).isoMapOfCommSq h₂₁₂₃).hom.app _ ≫
          (F.map p₂₃).f.map (F.coalgHom sq₂₃ a₂₃) ≫
          ((F.comp Adj.forget₁).isoMapOfCommSq h₃₂₃₁).hom.app _ := by
  refine ⟨fun H ↦ F.coalgHom_eq_coalgHom_coalgHom _ _ _ _ _ _ _ _ _ H, fun H ↦ ?_⟩
  rw [F.coalgHom_eq_coalgHom_coalgHom' sq₁₂ sq₂₃ sq₁₃ h₁₃₁₂ h₂₁₂₃ h₃₂₃₁] at H
  rw [map_coalgHom_comp_map_coalgHom_assoc] at H
  simp_rw [← Category.assoc] at H
  rw [cancel_mono] at H
  simp_rw [Category.assoc] at H
  dsimp at H
  rw [← Cat.comp_map _ (F.map p₁₂).f] at H
  erw [← ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.naturality_assoc] at H
  erw [← ((F.comp Adj.forget₁).isoMapOfCommSq h₁₃₁₂).hom.naturality_assoc] at H
  dsimp at H
  -- seems to need `(F.map u₁₃).f ≫ (F.map p₁₃).f` faithful and
  -- `(F.whiskerBaseChange sq).app _` mono?
  sorry

end

section Hom

variable {M M' : (F.obj Y₁).obj} {N N' : (F.obj X₂).obj}
    (a : M ⟶ (F.map t).f.obj ((F.map l).g.obj N))
    (a' : M' ⟶ (F.map t).f.obj ((F.map l).g.obj N'))
    (u : M ⟶ M') (v : N ⟶ N')

lemma map_comp_coalgHom_eq_coalgHom_map
    (H : a ≫ (F.map t).f.map ((F.map l).g.map v) = u ≫ a') :
    (((F.map r).f.map u ≫ F.coalgHom sq a' = F.coalgHom sq a ≫ (F.map b).f.map v)) := by
  rw [coalgHom, ← (F.map r).f.map_comp_assoc, ← H, coalgHom]
  simp [← (F.whiskerBaseChange sq).naturality]

lemma iff_map_comp_coalgHom_eq_coalgHom_map [IsIso (F.baseChange sq)] :
    a ≫ (F.map t).f.map ((F.map l).g.map v) = u ≫ a' ↔
    (((F.map r).f.map u ≫ F.coalgHom sq a' = F.coalgHom sq a ≫ (F.map b).f.map v)) := by
  refine ⟨fun H ↦ F.map_comp_coalgHom_eq_coalgHom_map sq _ _ _ _ H, fun H ↦ ?_⟩
  rw [coalgHom, coalgHom, Category.assoc] at H
  rw [← (F.whiskerBaseChange sq).naturality] at H
  simp only [Cat.comp_obj, Cat.comp_map] at H
  -- seems to need `(F.map r).f` faithful and `(F.whiskerBaseChange sq).app _` mono?
  sorry

end Hom

end

end Pseudofunctor

end CategoryTheory
