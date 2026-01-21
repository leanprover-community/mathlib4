/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Order.Interval.Set.SuccOrder
public import Mathlib.Order.Shrink
/-!
# Classes of morphisms that are stable under transfinite composition

Given a well-ordered type `J`, `W : MorphismProperty C` and
a morphism `f : X ⟶ Y`, we define a structure `W.TransfiniteCompositionOfShape J f`
which expresses that `f` is a transfinite composition of shape `J` of morphisms in `W`.
This structures extends `CategoryTheory.TransfiniteCompositionOfShape` which was
defined in the file `CategoryTheory.Limits.Shape.Preorder.TransfiniteCompositionOfShape`.
We use this structure in order to define the class of morphisms
`W.transfiniteCompositionsOfShape J : MorphismProperty C`, and the type class
`W.IsStableUnderTransfiniteCompositionOfShape J`.
In particular, if `J := ℕ`, we define `W.IsStableUnderInfiniteComposition`,

Finally, we introduce the class `W.IsStableUnderTransfiniteComposition`
which says that `W.IsStableUnderTransfiniteCompositionOfShape J`
holds for any well-ordered type `J` in a certain universe `w`.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace MorphismProperty

variable (W : MorphismProperty C)

section

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {J' : Type w'} [LinearOrder J'] [SuccOrder J'] [OrderBot J'] [WellFoundedLT J']

/-- Structure expressing that a morphism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape `J` of morphisms in `W : MorphismProperty C`. -/
structure TransfiniteCompositionOfShape {X Y : C} (f : X ⟶ Y) extends
    CategoryTheory.TransfiniteCompositionOfShape J f where
  map_mem (j : J) (hj : ¬IsMax j) : W (F.map (homOfLE (Order.le_succ j)))

namespace TransfiniteCompositionOfShape

section

variable {W J} {X Y : C} {f : X ⟶ Y} (h : W.TransfiniteCompositionOfShape J f)

/-- If `f` and `f'` are two isomorphic morphisms and `f` is a transfinite composition
of morphisms in `W : MorphismProperty C`, then so is `f'`. -/
@[simps toTransfiniteCompositionOfShape]
def ofArrowIso {X' Y' : C}
    {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    W.TransfiniteCompositionOfShape J f' where
  __ := h.toTransfiniteCompositionOfShape.ofArrowIso e
  map_mem := h.map_mem

/-- If `W ≤ W'`, then transfinite compositions of shape `J` of morphisms in `W`
are also transfinite composition of shape `J` of morphisms in `W'`. -/
@[simps toTransfiniteCompositionOfShape]
def ofLE {W' : MorphismProperty C} (hW : W ≤ W') :
    W'.TransfiniteCompositionOfShape J f where
  __ := h.toTransfiniteCompositionOfShape
  map_mem j hj := hW _ (h.map_mem j hj)

/-- If `f` is a transfinite composition of shape `J` of morphisms in `W`,
then it is also a transfinite composition of shape `J'` of morphisms in `W` if `J' ≃o J`. -/
def ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J']
    [SuccOrder J'] [WellFoundedLT J'] (e : J' ≃o J) :
    W.TransfiniteCompositionOfShape J' f where
  __ := h.toTransfiniteCompositionOfShape.ofOrderIso e
  map_mem j hj := by
    have := h.map_mem (e j) (by simpa only [e.isMax_apply])
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk (homOfLE (e.monotone (Order.le_succ j))) =
      Arrow.mk (homOfLE (Order.le_succ (e j))) :=
        Arrow.ext rfl (e.map_succ j) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert this using 1

/-- If `f` is a transfinite composition of shape `J` of morphisms
in `W.inverseImage F`, then `F` is a transfinite composition of shape `J`
of morphisms in `W` provided `F` preserves suitable colimits. -/
@[simps toTransfiniteCompositionOfShape]
noncomputable def map {W : MorphismProperty D} {F : C ⥤ D}
    [PreservesWellOrderContinuousOfShape J F]
    [PreservesColimitsOfShape J F]
    (h : (W.inverseImage F).TransfiniteCompositionOfShape J f) :
    W.TransfiniteCompositionOfShape J (F.map f) where
  __ := h.toTransfiniteCompositionOfShape.map F
  map_mem j hj := h.map_mem j hj

/-- A transfinite composition of shape `J` of morphisms in `W` induces a transfinite
composition of shape `Set.Iic j` (for any `j : J`). -/
noncomputable def iic (j : J) :
    W.TransfiniteCompositionOfShape (Set.Iic j) (h.F.map (homOfLE bot_le : ⊥ ⟶ j)) where
  __ := h.toTransfiniteCompositionOfShape.iic j
  map_mem i hi := by
    have := h.map_mem i.1 (by
      rw [not_isMax_iff] at hi ⊢
      obtain ⟨i', hi'⟩ := hi
      exact ⟨j, lt_of_lt_of_le hi' i'.2⟩)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (homOfLE (Order.le_succ i))) =
      Arrow.mk (homOfLE (Order.le_succ i.1)) :=
        Arrow.ext rfl (Set.Iic.coe_succ_of_not_isMax hi) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert this using 1

/-- A transfinite composition of shape `J` of morphisms in `W` induces a transfinite
composition of shape `Set.Ici j` (for any `j : J`). -/
noncomputable def ici (j : J) :
    W.TransfiniteCompositionOfShape (Set.Ici j) (h.incl.app j) where
  __ := h.toTransfiniteCompositionOfShape.ici j
  map_mem i hi := by
    have := h.map_mem i.1 (Set.not_isMax_coe _ hi)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (homOfLE (Order.le_succ i))) =
      Arrow.mk (homOfLE (Order.le_succ i.1)) :=
        Arrow.ext rfl (coe_succ_of_mem (i.2.trans (Order.le_succ _))) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert this using 1

end

/-- If `F : ComposableArrows C n` and all maps `F.obj i.castSucc ⟶ F.obj i.succ`
are in `W`, then `F.hom : F.left ⟶ F.right` is a transfinite composition of
shape `Fin (n + 1)` of morphisms in `W`. -/
@[simps!]
def ofComposableArrows {n : ℕ} (F : ComposableArrows C n)
    (hF : ∀ (i : Fin n), W (F.map (homOfLE i.castSucc_le_succ))) :
    W.TransfiniteCompositionOfShape (Fin (n + 1)) F.hom where
  toTransfiniteCompositionOfShape := .ofComposableArrows F
  map_mem j hj := by
    obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · replace hF := hF j
      rw [← W.arrow_mk_mem_toSet_iff] at hF ⊢
      have eq : Arrow.mk (homOfLE (Order.le_succ j.castSucc)) =
        Arrow.mk (homOfLE j.castSucc_le_succ) :=
          Arrow.ext rfl j.orderSucc_castSucc rfl
      replace eq := congr_arg F.mapArrow.obj eq
      convert hF using 1
    · rw [isMax_iff_eq_top] at hj
      exact (hj rfl).elim

/-- The identity of any object is a transfinite composition of shape `Fin 1`. -/
def id (X : C) : W.TransfiniteCompositionOfShape (Fin 1) (𝟙 X) :=
  ofComposableArrows W (.mk₀ X) (by simp)

variable {W}

/-- If `f : X ⟶ Y` satisfies `W f`, then `f` is a transfinite composition of shape `Fin 2`
of morphisms in `W`. -/
def ofMem {X Y : C} (f : X ⟶ Y) (hf : W f) :
    W.TransfiniteCompositionOfShape (Fin 2) f :=
  ofComposableArrows W (.mk₁ f) (fun i ↦ by fin_cases i; assumption)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy `W f` and `W g`, then `f ≫ g` is a
transfinite composition of shape `Fin 3` of morphisms in `W`. -/
def ofComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) :
    W.TransfiniteCompositionOfShape (Fin 3) (f ≫ g) :=
  ofComposableArrows W (.mk₂ f g) (fun i ↦ by fin_cases i <;> assumption)

end TransfiniteCompositionOfShape

/-- Given `W : MorphismProperty C` and a well-ordered type `J`, this is
the class of morphisms that are transfinite composition of shape `J`
of morphisms in `W`. -/
def transfiniteCompositionsOfShape : MorphismProperty C :=
  fun _ _ f ↦ Nonempty (W.TransfiniteCompositionOfShape J f)

lemma transfiniteCompositionsOfShape_monotone :
    Monotone (transfiniteCompositionsOfShape (C := C) (J := J)) := by
  rintro _ _ h _ _ _ ⟨t⟩
  exact ⟨t.ofLE h⟩

variable {J} in
lemma transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') :
    W.transfiniteCompositionsOfShape J =
      W.transfiniteCompositionsOfShape J' := by
  ext _ _ f
  exact ⟨fun ⟨h⟩ ↦ ⟨h.ofOrderIso e.symm⟩, fun ⟨h⟩ ↦ ⟨h.ofOrderIso e⟩⟩

instance : RespectsIso (W.transfiniteCompositionsOfShape J) :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e ⟨h⟩ ↦ ⟨h.ofArrowIso e⟩)

variable {W J} in
lemma TransfiniteCompositionOfShape.mem {X Y : C} (f : X ⟶ Y)
    (h : W.TransfiniteCompositionOfShape J f) :
    W.transfiniteCompositionsOfShape J f := ⟨h⟩

lemma transfiniteCompositionsOfShape_map_of_preserves (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    {X Y : C} (f : X ⟶ Y) {P : MorphismProperty D}
    [PreservesColimitsOfShape J G]
    (h : (P.inverseImage G).transfiniteCompositionsOfShape J f) :
    P.transfiniteCompositionsOfShape J (G.map f) :=
  h.some.map.mem

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite compositions
of shape `J` if for any well-order-continuous functor `F : J ⥤ C` such that
`F.obj j ⟶ F.obj (Order.succ j)` is in `W`, then `F.obj ⊥ ⟶ c.pt` is in `W`
for any colimit cocone `c : Cocone F`. -/
@[mk_iff]
class IsStableUnderTransfiniteCompositionOfShape : Prop where
  le : W.transfiniteCompositionsOfShape J ≤ W

lemma transfiniteCompositionsOfShape_le
    [W.IsStableUnderTransfiniteCompositionOfShape J] :
    W.transfiniteCompositionsOfShape J ≤ W :=
  IsStableUnderTransfiniteCompositionOfShape.le

variable {J} in
lemma isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (e : J ≃o J') :
    W.IsStableUnderTransfiniteCompositionOfShape J ↔
      W.IsStableUnderTransfiniteCompositionOfShape J' := by
  simp only [isStableUnderTransfiniteCompositionOfShape_iff,
    W.transfiniteCompositionsOfShape_eq_of_orderIso e]

end

section

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

namespace IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape

variable {W J} {X Y : C} {f : X ⟶ Y} (hf : W.TransfiniteCompositionOfShape J f)
  [W.IsMultiplicative]
  (hJ : ∀ (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J],
    W.IsStableUnderColimitsOfShape J)

attribute [local instance] IsCofiltered.isConnected

include hJ in
lemma mem_map_bot_le {j : J} (g : ⊥ ⟶ j) : W (hf.F.map g) := by
  obtain rfl : g = homOfLE bot_le := rfl
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using W.id_mem _
  | succ j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j), hf.F.map_comp]
    exact W.comp_mem _ _ hj' (hf.map_mem j hj)
  | isSuccLimit j hj hj' =>
    letI : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj⟩
        bot_le j := bot_le }
    exact MorphismProperty.colimitsOfShape_le _
      (.of_isColimit (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun k ↦ hj' _ k.2))

include hf hJ in
lemma mem [W.RespectsIso] : W f :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk hf.isoBot.symm (Iso.refl _))).2
    (MorphismProperty.colimitsOfShape_le _
      (.of_isColimit hf.isColimit (fun j ↦ mem_map_bot_le _ hJ _)))

end IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape

variable {W J} in
open IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape in
lemma IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
    [W.IsMultiplicative] [W.RespectsIso]
    (hJ : ∀ (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J],
      W.IsStableUnderColimitsOfShape J) :
    W.IsStableUnderTransfiniteCompositionOfShape J where
  le _ _ _ | ⟨hf⟩ => mem hf hJ

instance [W.IsMultiplicative] [W.RespectsIso]
    [MorphismProperty.IsStableUnderFilteredColimits.{w, w} W] :
    W.IsStableUnderTransfiniteCompositionOfShape J :=
  .of_isStableUnderColimitsOfShape (fun _ _ _ _ _ ↦ by infer_instance)

end

/-- A class of morphisms `W : MorphismProperty C` is stable under infinite composition
if for any functor `F : ℕ ⥤ C` such that `F.obj n ⟶ F.obj (n + 1)` is in `W` for any `n : ℕ`,
the map `F.obj 0 ⟶ c.pt` is in `W` for any colimit cocone `c : Cocone F`. -/
abbrev IsStableUnderInfiniteComposition : Prop :=
  W.IsStableUnderTransfiniteCompositionOfShape ℕ

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite composition
if it is multiplicative and stable under transfinite composition of any shape
(in a certain universe). -/
class IsStableUnderTransfiniteComposition : Prop where
  isStableUnderTransfiniteCompositionOfShape
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.IsStableUnderTransfiniteCompositionOfShape J := by infer_instance

namespace IsStableUnderTransfiniteComposition

attribute [instance] isStableUnderTransfiniteCompositionOfShape

instance [W.IsMultiplicative] [W.RespectsIso]
    [MorphismProperty.IsStableUnderFilteredColimits.{w, w} W] :
    IsStableUnderTransfiniteComposition.{w} W where

example : (isomorphisms C).IsStableUnderTransfiniteComposition := inferInstance

variable [IsStableUnderTransfiniteComposition.{w'} W]

lemma shrink [UnivLE.{w, w'}] :
    IsStableUnderTransfiniteComposition.{w} W where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso W
      (orderIsoShrink.{w'} J)]
    infer_instance

lemma shrink₀ : IsStableUnderTransfiniteComposition.{0} W := shrink.{0, w'} W

attribute [local instance] shrink₀

instance : W.IsMultiplicative where
  id_mem X :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.id W X).mem
  comp_mem f g hf hg :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.ofComp f g hf hg).mem

end IsStableUnderTransfiniteComposition

/-- The class of transfinite compositions (for arbitrary well-ordered types `J : Type w`)
of a class of morphisms `W`. -/
@[pp_with_univ]
def transfiniteCompositions : MorphismProperty C :=
  ⨆ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
    (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J

lemma transfiniteCompositions_iff {X Y : C} (f : X ⟶ Y) :
    transfiniteCompositions.{w} W f ↔
      ∃ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
        (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J f := by
  simp only [transfiniteCompositions, iSup_iff]

lemma transfiniteCompositionsOfShape_le_transfiniteCompositions
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.transfiniteCompositionsOfShape J ≤ transfiniteCompositions.{w} W := by
  intro A B f hf
  rw [transfiniteCompositions_iff]
  exact ⟨_, _, _, _, _, hf⟩

lemma transfiniteCompositions_monotone :
    Monotone (transfiniteCompositions.{w} (C := C)) := by
  intro W₁ W₂ h X Y f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    (transfiniteCompositionsOfShape_monotone J h _ hf)

lemma le_transfiniteCompositions :
    W ≤ transfiniteCompositions.{w} W :=
  le_trans (fun _ _ _ hf ↦
    (MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso (.ofMem _ hf)
      (orderIsoShrink.{w} (Fin 2)).symm).mem)
    (transfiniteCompositionsOfShape_le_transfiniteCompositions _ _)

lemma transfiniteCompositions_le [IsStableUnderTransfiniteComposition.{w} W] :
    transfiniteCompositions.{w} W ≤ W := by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le J _ hf

@[simp]
lemma transfiniteCompositions_le_iff {P Q : MorphismProperty C}
    [IsStableUnderTransfiniteComposition.{w} Q] :
    transfiniteCompositions.{w} P ≤ Q ↔ P ≤ Q := by
  constructor
  · exact (le_transfiniteCompositions P).trans
  · intro h
    exact (transfiniteCompositions_monotone.{w} h).trans Q.transfiniteCompositions_le

namespace TransfiniteCompositionOfShape

variable {W} {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

section

variable [IsStableUnderTransfiniteComposition.{w} W]
  {X Y : C} {f : X ⟶ Y} (h : W.TransfiniteCompositionOfShape J f)

lemma mem_map {i j : J} (φ : i ⟶ j) :
    W (h.F.map φ) :=
  W.transfiniteCompositionsOfShape_le _ _ ((h.iic j).ici ⟨i, leOfHom φ⟩).mem

lemma mem_incl_app (j : J) :
    W (h.incl.app j) :=
  W.transfiniteCompositionsOfShape_le _ _ (h.ici j).mem

end

section isomorphisms

example : (isomorphisms C).IsStableUnderTransfiniteCompositionOfShape J := inferInstance

variable {X Y : C} {f : X ⟶ Y} (h : (isomorphisms C).TransfiniteCompositionOfShape J f)

include h in
lemma isIso : IsIso f :=
  (isomorphisms C).transfiniteCompositionsOfShape_le _ _ h.mem

instance {i j : J} (f : i ⟶ j) : IsIso (h.F.map f) := h.mem_map f

instance (j : J) : IsIso (h.incl.app j) := h.mem_incl_app j

end isomorphisms

end TransfiniteCompositionOfShape

section

variable {J : Type w} [LinearOrder J]

variable {X Y : J → C} (f : ∀ j, X j ⟶ Y j)

namespace transfiniteCompositionOfShapeSigmaMap

open Classical in
def obj (_ : ∀ j, X j ⟶ Y j) (i j : J) : C :=
  if i ≤ j then X j else Y j

def objIso₁ (i j : J) (hij : i ≤ j) : obj f i j ≅ X j :=
  eqToIso (dif_pos hij)

def objIso₂ (i j : J) (hij : j < i) : obj f i j ≅ Y j :=
  eqToIso (dif_neg (by simpa using hij))

def map (i₁ i₂ : J) (h : i₁ ≤ i₂) (j : J) :
    obj f i₁ j ⟶ obj f i₂ j :=
  if hi₂ : i₂ ≤ j then
    (objIso₁ f i₁ j (by lia)).hom ≫ (objIso₁ f i₂ j hi₂).inv
  else
    if hi₁ : i₁ ≤ j then
      (objIso₁ f i₁ j hi₁).hom ≫ f j ≫ (objIso₂ f i₂ j (by lia)).inv
    else
      (objIso₂ f i₁ j (by lia)).hom ≫ (objIso₂ f i₂ j (by lia)).inv

lemma map_eq_of_le₂ (i₁ i₂ : J) (h : i₁ ≤ i₂) (j : J) (hi₂ : i₂ ≤ j) :
    map f i₁ i₂ h j = (objIso₁ f i₁ j (by lia)).hom ≫ (objIso₁ f i₂ j hi₂).inv := by
  grind [map]

@[simp]
lemma map_refl (i j : J) :
    map f i i (by rfl) j = 𝟙 _ := by
  grind [map]

@[reassoc (attr := simp)]
lemma map_trans (i₁ i₂ i₃ : J) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (j : J) :
    map f i₁ i₂ hi₁₂ j ≫ map f i₂ i₃ hi₂₃ j = map f i₁ i₃ (hi₁₂.trans hi₂₃) j := by
  grind [map]

open Classical in
def objι (i j : J) :
    obj f i j ⟶ Y j :=
  if hi : i ≤ j then
    (objIso₁ f i j hi).hom ≫ f j
  else
    (objIso₂ f i j (by lia)).hom

@[reassoc (attr := simp)]
lemma objIso₁_inv_objι (i j : J) (hi : i ≤ j) :
    (objIso₁ f i j hi).inv ≫ objι f i j = f j:= by
  grind [objι]

@[reassoc (attr := simp)]
lemma map_objι (i₁ i₂ : J) (hi : i₁ ≤ i₂) (j : J) :
    map f i₁ i₂ hi j ≫ objι f i₂ j = objι f i₁ j := by
  grind [map, objι]

@[reassoc (attr := simp)]
lemma objIso₂_inv_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (j : J) (hi₁ : j < i₁) :
    (objIso₂ f i₁ j hi₁).inv ≫ map f i₁ i₂ hi j = (objIso₂ f i₂ j (by lia)).inv := by
  grind [map]

@[simps]
def diagramFunctor :
    J ⥤ Discrete J ⥤ C where
  obj i := Discrete.functor (obj f i)
  map {i₁ i₂} g := Discrete.natTrans (fun ⟨j⟩ ↦ map f i₁ i₂ (leOfHom g) j)

abbrev columnFunctor (j : J) : J ⥤ C := (diagramFunctor f).flip.obj (.mk j)

instance (j : J) [OrderBot J] [SuccOrder J] :
    (columnFunctor f j).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    by_cases h : m ≤ j
    · exact ⟨{
        desc s := (objIso₁ f m j h).hom ≫ (objIso₁ f ⊥ j bot_le).inv ≫
          s.ι.app ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩
        fac s k := by
          rw [← s.w (show ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩ ⟶ k from homOfLE bot_le)]
          dsimp
          grind [map]
        uniq s l hl := by
          simp [← hl ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩, map_eq_of_le₂ f _ _ bot_le j h]
      }⟩
    · simp only [not_le] at h
      exact ⟨{
        desc s := (objIso₂ f m j h).hom ≫
            (objIso₂ f _ _ (Order.lt_succ_of_not_isMax (not_isMax_iff.2 ⟨_, h⟩))).inv ≫
            s.ι.app ⟨Order.succ j, hm.succ_lt_iff.2 h⟩
        fac s k := by
          dsimp
          by_cases hk : Order.succ j ≤ k
          · rw [← s.w (show ⟨Order.succ j, hm.succ_lt_iff.2 h⟩ ⟶ k from homOfLE hk)]
            dsimp
            grind [map]
          · simp only [not_le] at hk
            rw [← s.w (show k ⟶ ⟨Order.succ j, hm.succ_lt_iff.2 h⟩ from homOfLE hk.le)]
            dsimp
            grind [map]
        uniq s l hl := by simp [← hl ⟨Order.succ j, hm.succ_lt_iff.2 h⟩]
      }⟩

variable [HasCoproductsOfShape J C]

noncomputable abbrev ι (i : J) : ∐ (obj f i) ⟶ ∐ Y :=
  Limits.Sigma.map (objι f i)

@[reassoc (attr := simp)]
lemma map_ι (i₁ i₂ : J) (hi : i₁ ≤ i₂) :
    Limits.Sigma.map (map f i₁ i₂ hi) ≫ ι f i₂ = ι f i₁ := by
  simp [Limits.Sigma.map_comp_map]

variable [OrderBot J]

noncomputable def isoBot : ∐ (obj f ⊥) ≅ ∐ X :=
  Sigma.mapIso (fun j ↦ objIso₁ f ⊥ j bot_le)

@[reassoc (attr := simp)]
lemma isoBot_inv_ι :
    (isoBot f).inv ≫ ι f ⊥ = Limits.Sigma.map f := by
  dsimp [isoBot, ι]
  cat_disch

variable [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]

/-instance : (diagramFunctor f ⋙ colim).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    sorry⟩-/

end transfiniteCompositionOfShapeSigmaMap

variable [HasCoproductsOfShape J C] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]

/-open transfiniteCompositionOfShapeSigmaMap in
noncomputable def transfiniteCompositionOfShapeSigmaMap :
    TransfiniteCompositionOfShape (MorphismProperty.ofHoms f).pushouts J
      (Limits.Sigma.map f) where
  F := diagramFunctor f ⋙ colim
  isoBot := isoBot f
  incl := { app i := ι f i }
  isColimit := sorry
  map_mem := sorry

variable (hf : ∀ (j : J), W (f j))

variable [W.IsStableUnderTransfiniteCompositionOfShape J]
variable [W.IsStableUnderCobaseChange]

instance : W.IsStableUnderCoproductsOfShape J :=
  IsStableUnderCoproductsOfShape.mk _ _ (fun X Y _ _ f hf ↦ by
    sorry)-/

end


end MorphismProperty

end CategoryTheory
