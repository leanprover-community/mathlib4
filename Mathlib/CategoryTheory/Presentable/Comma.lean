/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Comma
public import Mathlib.CategoryTheory.Presentable.IsDiscrete
public import Mathlib.CategoryTheory.Presentable.Uniformization

/-!
# Comma categories are accessible

Let `F₁ : C₁ ⥤ D` and `F₂ : C₂ ⥤ D` be accessible functors between
accessible categories, then `Comma F₁ F₂` is also an accessible
category (`Comma.isAccessibleCategory`); similar results hold for `Arrow`,
`CostructuredArrow`, `StructuredArrow`, `Under`, `Over` categories.
This is obtained as a consequence of the uniformization theorem for accessible
categories (see the file `Mathlib/CategoryTheory/Presentable/Uniformization.lean`)
and the more precise result `Comma.isCardinalAccessibleCategory` which says that
`Comma F₁ F₂` is a `κ`-accessible category when `F₁` and `F₂` are `κ`-accessible
functors between `κ`-accessible categories and that `F₁` preserves
`κ`-presentable objects.

The key point in the technical proof of `Comma.isCardinalAccessibleCategory`
is that if `f : Comma F₁ F₂`, then `f` is the `κ`-filtered colimit
(indexed by a category denoted `J κ f` here) of the
`g : Comma F₁ F₂` equipped with a morphism `g ⟶ f` such that both `g.left`
and `g.right` are `κ`-presentable. In order to do this, we basically need
to show that the first and second functors `π₁ : J κ f ⥤ J₁ κ f` and
`π₂ : J κ f ⥤ J₂ κ f` are final (where `J₁ κ f` is the category of morphisms
`X ⟶ f.left` where `X` is `κ`-presentable, and similarly `J₂ κ f` is the
category of morphisms `Y ⟶ f.right` where `Y` is `κ`-presentable).
Then, the colimit of those `g.left` for `g ⟶ f` in `J κ f` identify to the
colimit of such `X` indexed by `J₁ κ f` which is `f.left` because
`κ`-presentable objects in `C₁` form a dense full subcategory
(see the file `Mathlib/CategoryTheory/Presentable/Dense.lean`),
and similarly the colimit of those `g.right` for `g ⟶ f` in `J κ f`
identify to `f.right`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w

@[expose] public section

namespace CategoryTheory

open Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace Comma

variable (F₁ : C₁ ⥤ D) (F₂ : C₂ ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular]

section

variable [F₁.IsCardinalAccessible κ]
  [HasCardinalFilteredColimits C₁ κ] [HasCardinalFilteredColimits C₂ κ]

instance : HasCardinalFilteredColimits (Comma F₁ F₂) κ where
  hasColimitsOfShape J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₁ κ J
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₂ κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    infer_instance

instance : (Comma.fst F₁ F₂).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₁ κ J
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₂ κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    infer_instance

instance : (Comma.snd F₁ F₂).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₁ κ J
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₂ κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    infer_instance

end

open IsFiltered in
variable {F₁ F₂ κ} in
lemma isCardinalPresentable_mk {X₁ : C₁} {X₂ : C₂}
    [HasCardinalFilteredColimits C₁ κ] [HasCardinalFilteredColimits C₂ κ]
    [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
    [IsCardinalPresentable X₁ κ] [IsCardinalPresentable X₂ κ]
    [F₁.PreservesCardinalPresentable κ] (f : F₁.obj X₁ ⟶ F₂.obj X₂) :
    IsCardinalPresentable (Comma.mk _ _ f) κ :=
  .mk (fun J _ _ G c hc ↦ by
    have := isFiltered_of_isCardinalFiltered J κ
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₁ κ J
    have := HasCardinalFilteredColimits.hasColimitsOfShape C₂ κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₂ κ J
    refine ⟨fun g ↦ ?_, fun j f₁ f₂ hf ↦ ?_⟩
    · /- We need to show that any morphism `g : Comma.mk _ _ f ⟶ c.pt`
      lifts as a morphism `Comma.mk _ _ f ⟶ G.obj j` for a suitable `j`.
      By using that `X₁` and `X₂` are `κ`-presentable, we start by lifting
      the maps `g.left` and `g.right` as `f₁ : X₁ ⟶ (G.obj j).left` and
      `f₂ : X₂ ⟶ (G.obj j).right`. -/
      obtain ⟨j, f₁, f₂, hf₁, hf₂⟩ :
          ∃ (j : J) (f₁ : X₁ ⟶ (G.obj j).left) (f₂ : X₂ ⟶ (G.obj j).right),
            f₁ ≫ (c.ι.app j).left = g.left ∧ f₂ ≫ (c.ι.app j).right = g.right := by
        obtain ⟨j₁, f₁, hf₁⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
          (isColimitOfPreserves (fst _ _) hc) g.left
        obtain ⟨j₂, f₂, hf₂⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
          (isColimitOfPreserves (snd _ _) hc) g.right
        dsimp at f₁ f₂ hf₁ hf₂
        refine ⟨max j₁ j₂, f₁ ≫ (G.map (leftToMax j₁ j₂)).left,
          f₂ ≫ (G.map (rightToMax j₁ j₂)).right, ?_, ?_⟩
        · rw [Category.assoc, ← hf₁, ← Comma.comp_left, Cocone.w]
        · rw [Category.assoc, ← hf₂, ← Comma.comp_right, Cocone.w]
      /- Replacing `j` by a "larger" `j'` (i.e. using a morphism `j ⟶ j'`),
      we may obtain a commutative square. This uses that `F₁.obj X₁`
      is `κ`-presentable. -/
      obtain ⟨j', a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
        κ (isColimitOfPreserves (snd _ _ ⋙ F₂) hc)
        (F₁.map f₁ ≫ (G.obj j).hom) (f ≫ F₂.map f₂) (by
          dsimp
          simp only [Category.assoc, ← Functor.map_comp, hf₂,
            ← (c.ι.app j).w, Functor.const_obj_obj,
            ← Functor.map_comp_assoc, hf₁, g.w])
      refine ⟨j', { left := f₁ ≫ (G.map a).left, right := f₂ ≫ (G.map a).right }, ?_⟩
      ext
      · dsimp
        simp [← hf₁, ← Comma.comp_left]
      · dsimp
        simp [← hf₂, ← Comma.comp_right]
    · /- We need to show that two morphisms `f₁` and `f₂` in `Comma.mk _ _ f ⟶ G.obj j`
      which become equal after postcomposing with `G.obj j ⟶ c.pt` also become equal
      after postcomposing with `G.obj j ⟶ G.obj j'` for a suitable map `j ⟶ j'`.
      The proof proceeds by considering separately the left and the right parts
      of these morphisms in the comma category. -/
      obtain ⟨j₁, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
        (isColimitOfPreserves (fst _ _) hc) f₁.left f₂.left ((fst _ _).congr_map hf)
      obtain ⟨j₂, b, hb⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
        (isColimitOfPreserves (snd _ _) hc) f₁.right f₂.right ((snd _ _).congr_map hf)
      dsimp at ha hb
      obtain ⟨j', a', b', h⟩ := IsFiltered.span a b
      refine ⟨j', a ≫ a', ?_⟩
      ext
      · simp [reassoc_of% ha]
      · simp [h, reassoc_of% hb])

/-- The property of objects in `Comma F₁ F₂` which consists of
morphisms `F₁.obj X₁ ⟶ F₂.obj X₂` where both `X₁` abd `X₂` are `κ`-presentable.
When both `F₁` and `F₂` are `κ`-accessible functors (between `κ`-accessible categories)
and `F₁` preserves `κ`-presentable objects, we show that this property of objects
coincides with the `κ`-presentable objects of `Comma F₁ F₂`,
see the lemma `Comma.isCardinalPresentable_eq`. -/
protected def isCardinalPresentable : ObjectProperty (Comma F₁ F₂) :=
  ObjectProperty.comma _ _ (isCardinalPresentable C₁ κ) (isCardinalPresentable C₂ κ)
deriving ObjectProperty.IsStableUnderRetracts

lemma isCardinalPresentable_le
    [HasCardinalFilteredColimits C₁ κ] [HasCardinalFilteredColimits C₂ κ]
    [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
    [F₁.PreservesCardinalPresentable κ] :
    Comma.isCardinalPresentable F₁ F₂ κ ≤ isCardinalPresentable (Comma F₁ F₂) κ := by
  intro f ⟨h₁, h₂⟩
  simp only [ObjectProperty.prop_inverseImage_iff, fst_obj, snd_obj] at h₁ h₂
  exact isCardinalPresentable_mk f.hom

instance [ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C₁ κ)]
    [ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C₂ κ)]
    [LocallySmall.{w} D] :
    ObjectProperty.EssentiallySmall.{w} (Comma.isCardinalPresentable F₁ F₂ κ) := by
  dsimp only [Comma.isCardinalPresentable]
  infer_instance

namespace isCardinalAccessibleCategory

variable {F₁ F₂} (f : Comma F₁ F₂)

/-- Given `f : Comma F₁ F₂`, this is the category of morphisms `g ⟶ f`
where both the first and second objects of `g` are `κ`-presentable. -/
private abbrev J := CostructuredArrow (Comma.isCardinalPresentable F₁ F₂ κ).ι f

/-- Given `f : Comma F₁ F₂`, this is the category of morpshims `X ⟶ f.left`
where `X` is `κ`-presentable. -/
private abbrev J₁ := CostructuredArrow (isCardinalPresentable C₁ κ).ι f.left

/-- Given `f : Comma F₁ F₂`, this is the category of morpshims `Y ⟶ f.right`
where `Y` is `κ`-presentable. -/
private abbrev J₂ := CostructuredArrow (isCardinalPresentable C₂ κ).ι f.right

private instance [IsCardinalAccessibleCategory C₁ κ] : IsFiltered (J₁ κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

private instance [IsCardinalAccessibleCategory C₂ κ] : IsFiltered (J₂ κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

attribute [local instance] IsFiltered.nonempty

/-- The map `J κ f → J₁ κ f` which extracts the first part. -/
private abbrev J.fst (g : J κ f) : J₁ κ f :=
  CostructuredArrow.mk (Y := ⟨_, g.left.property.1⟩) (by exact g.hom.left)

/-- The map `J κ f → J₂ κ f` which extracts the second part. -/
private abbrev J.snd (g : J κ f) : J₂ κ f :=
  CostructuredArrow.mk (Y := ⟨_, g.left.property.2⟩) (by exact g.hom.right)

/-- The first projection `J κ f ⥤ J₁ κ f`. (Note: this functor could be
defined using `CostructuredArrow.map₂`, but it would not have the same
definitional properties.) -/
@[implicit_reducible, simps]
private def π₁ : J κ f ⥤ J₁ κ f where
  obj g := g.fst
  map φ := CostructuredArrow.homMk (ObjectProperty.homMk (by exact φ.left.hom.left))
    (by exact congr_arg CommaMorphism.left (CostructuredArrow.w φ))

/-- The second projection `J κ f ⥤ J₂ κ f`. (Note: this functor could be
defined using `CostructuredArrow.map₂`, but it would not have the same
definitional properties.) -/
@[implicit_reducible, simps]
private def π₂ : J κ f ⥤ J₂ κ f where
  obj g := g.snd
  map φ := CostructuredArrow.homMk (ObjectProperty.homMk (by exact φ.left.hom.right))
    (by exact congr_arg CommaMorphism.right (CostructuredArrow.w φ))

variable {κ f}

/-- Constructor for objects in `J κ f`. -/
private abbrev J.mk (j₁ : J₁ κ f) (j₂ : J₂ κ f) (g : F₁.obj j₁.left.obj ⟶ F₂.obj j₂.left.obj)
    (w : F₁.map j₁.hom ≫ f.hom = g ≫ F₂.map j₂.hom := by cat_disch) :
    J κ f :=
  CostructuredArrow.mk (Y := ⟨Comma.mk _ _ g, j₁.left.property, j₂.left.property⟩)
    { left := by exact j₁.hom
      right := by exact j₂.hom }

/-- Constructor for morphisms in `J κ f`. -/
private abbrev J.homMk {j j' : J κ f} (g₁ : j.fst ⟶ j'.fst) (g₂ : j.snd ⟶ j'.snd)
    (h : F₁.map g₁.left.hom ≫ j'.left.obj.hom =
      j.left.obj.hom ≫ F₂.map g₂.left.hom := by cat_disch) :
    j ⟶ j' :=
  CostructuredArrow.homMk (ObjectProperty.homMk
    { left := g₁.left.hom
      right := g₂.left.hom }) (by
        ext
        · simpa using! CostructuredArrow.w g₁
        · simpa using! CostructuredArrow.w g₂)

section

variable [IsCardinalAccessibleCategory C₂ κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ]

private lemma J.exists_hom'
    {j j' : J κ f} (g₁ : j.fst ⟶ j'.fst) (g₂ : j.snd ⟶ j'.snd) :
    ∃ (j₂ : J₂ κ f) (a : j'.snd ⟶ j₂),
        F₁.map g₁.left.hom ≫ j'.left.obj.hom ≫ F₂.map a.left.hom =
        j.left.obj.hom ≫ F₂.map g₂.left.hom ≫ F₂.map a.left.hom := by
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    F₂ κ (J₂ κ f)
  obtain ⟨j₂, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
    (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
    (i := j'.snd) (F₁.map g₁.left.hom ≫ j'.left.obj.hom)
    (j.left.obj.hom ≫ F₂.map g₂.left.hom) (by
      dsimp
      rw [Category.id_comp, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← dsimp% j'.hom.w, ← Functor.map_comp_assoc, dsimp% CostructuredArrow.w g₁,
        dsimp% j.hom.w, dsimp% CostructuredArrow.w g₂])
  exact ⟨j₂, a, by cat_disch⟩


private lemma J.exists_hom {j j' : J κ f} (g₁ : j.fst ⟶ j'.fst) (g₂ : j.snd ⟶ j'.snd) :
    ∃ (j'' : J κ f) (a : j ⟶ j'') (b : j' ⟶ j''),
      g₁.left.hom ≫ b.left.hom.left = a.left.hom.left ∧
      g₂.left.hom ≫ b.left.hom.right = a.left.hom.right := by
  obtain ⟨j₂, a, ha⟩ := J.exists_hom' g₁ g₂
  exact ⟨J.mk j'.fst j₂ (j'.left.obj.hom ≫ F₂.map a.left.hom)
    (by simp [← dsimp% (CostructuredArrow.w a)]), J.homMk g₁ (g₂ ≫ a) (by simpa),
    J.homMk (𝟙 _) a (by simp), by simp⟩

private lemma exists_of_j₁_of_j₂' (j₁ : J₁ κ f) (j₂ : J₂ κ f) :
    ∃ (j₂' : J₂ κ f) (_ : j₂ ⟶ j₂') (b : F₁.obj j₁.left.obj ⟶ F₂.obj j₂'.left.obj),
    F₁.map j₁.hom ≫ f.hom = b ≫ F₂.map j₂'.hom := by
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall F₂ κ
    (J₂ κ f)
  obtain ⟨k, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
    (F₁.map j₁.hom ≫ f.hom)
  dsimp at ha
  simp only [Category.id_comp] at ha
  obtain ⟨j₂', b, c, _⟩ := IsFilteredOrEmpty.cocone_objs j₂ k
  refine ⟨j₂', b, a ≫ F₂.map c.left.hom, ?_⟩
  simp [← ha, ← Functor.map_comp, dsimp% CostructuredArrow.w c]

private lemma exists_of_j₁_of_j₂ (j₁ : J₁ κ f) (j₂ : J₂ κ f) :
    ∃ (j : J κ f) (_ : j₁ ⟶ j.fst), Nonempty (j₂ ⟶ j.snd) := by
  obtain ⟨j₂', a, b, h⟩ := exists_of_j₁_of_j₂' j₁ j₂
  exact ⟨J.mk j₁ j₂' b h, 𝟙 _, ⟨a⟩⟩

private lemma exists_of_j₁ (j₁ : J₁ κ f) :
    ∃ (j : J κ f), Nonempty (j₁ ⟶ j.fst) := by
  obtain ⟨j, a, _⟩ := exists_of_j₁_of_j₂ j₁ (Classical.arbitrary _)
  exact ⟨j, ⟨a⟩⟩

private lemma exists_of_j₂ [IsCardinalAccessibleCategory C₁ κ] (j₂ : J₂ κ f) :
    ∃ (j : J κ f), Nonempty (j₂ ⟶ j.snd) := by
  obtain ⟨j, _, ⟨a⟩⟩ := exists_of_j₁_of_j₂ (Classical.arbitrary _) j₂
  exact ⟨j, ⟨a⟩⟩

end

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ] [LocallySmall.{w} D]

private instance : PreservesColimitsOfShape (J₁ κ f) F₁ :=
  F₁.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

private instance : PreservesColimitsOfShape (J₂ κ f) F₂ :=
  F₂.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

open IsCardinalFiltered in
private instance : IsCardinalFiltered (J κ f) κ := by
  rw [isCardinalFiltered_iff']
  refine ⟨fun ι j hι ↦ ?_, fun ι j k g hι hι' ↦ ?_⟩
  · /- Given a family of objects `j : ι → J κ f` with `ι` of cardinality `< κ`,
    we need to find an object `k : J κ f`, such that for any `i : ι`,
    there exists a morphism `j i ⟶ k`. We first use that `J₁ κ f` and `J₂ κ f`
    are `κ`-filtered in order to find `j₁` and `j₂`, and using `exists_of_j₁_of_j₂'`,
    we obtain a morphism `c : F₁.obj j₁.left.obj ⟶ F₂.obj j₂'.left.obj` which
    corresponds to an object `J.mk j₁ j₂' c : J κ f` -/
    obtain ⟨j₁, ⟨a₁⟩⟩ := IsCardinalFiltered.exists_max (fun i ↦ (j i).fst) hι
    obtain ⟨j₂, ⟨a₂⟩⟩ := IsCardinalFiltered.exists_max (fun i ↦ (j i).snd) hι
    obtain ⟨j₂', b, c, h₁⟩ := exists_of_j₁_of_j₂' j₁ j₂
    /- for each `i : ι`, we find a `j₂'' i : J₂ κ f` such that
    we have a morphism from `j i` to `J.mk j₁ (j₂'' i) (c ≫ F₂.map (d i).left.hom)`. -/
    choose j₂'' d h₂ using
      fun i ↦ IsCardinalPresentable.exists_eq_of_isColimit' κ
        (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
          (F₁.map (a₁ i).left.hom ≫ c)
            ((j i).left.obj.hom ≫ F₂.map (a₂ i).left.hom ≫ F₂.map b.left.hom) (by
              dsimp
              rw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc,
                ← dsimp% h₁, ← F₁.map_comp_assoc, dsimp% CostructuredArrow.w (a₁ i),
                ← F₂.map_comp, dsimp% CostructuredArrow.w b, ← F₂.map_comp,
                dsimp% CostructuredArrow.w (a₂ i), dsimp% (j i).hom.w])
    dsimp at h₁ h₂
    simp only [Category.assoc] at h₂
    /- Using that `J₂ κ f` is `κ`-filtered, we find `l : J₂ κ f` which is "larger"
    that `j₂'' i` for any `i : ι`. More precisely, we have morphisms `e i : j₂'' i ⟶ l`
    such that all the compositions `d i ≫ e i` are equal to the same morphism `g : j₂' ⟶ l`.
    The object `J.mk j₁ l (c ≫ F₂.map g.left.hom) : J κ f` is the expected object `k`. -/
    obtain ⟨l, e, g, fac⟩ := wideSpan d hι
    refine ⟨J.mk j₁ l (c ≫ F₂.map g.left.hom) ?_, fun i ↦ ⟨?_⟩⟩
    · dsimp
      rw [h₁, Category.assoc, ← Functor.map_comp, dsimp% CostructuredArrow.w g]
    · refine J.homMk (a₁ i) (a₂ i ≫ b ≫ g) (by simp [← fac i, reassoc_of% h₂])
  · /- Given a family of morphisms `g : ι → (j ⟶ k)` between two objects of `J κ f`,
    where `ι` is of cardinality `< κ`, we need to find an object `l'` and a morphism
    `c : k ⟶ l'` such that all the compositions `g i ≫ c` are equal. -/
    let g₁ (i : ι) := (π₁ κ f).map (g i)
    let g₂ (i : ι) := (π₂ κ f).map (g i)
    obtain ⟨l, a, ⟨b⟩⟩ := exists_of_j₁_of_j₂ (coeq g₁ hι) (coeq g₂ hι)
    obtain ⟨l', c, d, h₁, h₂⟩ := J.exists_hom (coeqHom g₁ hι ≫ a) (coeqHom g₂ hι ≫ b)
    refine ⟨l', c, J.homMk (toCoeq g₁ hι ≫ a ≫ (π₁ κ f).map d)
      (toCoeq g₂ hι ≫ b ≫ (π₂ κ f).map d) ?_, fun i ↦ ?_⟩
    · let i : ι := Classical.arbitrary _
      dsimp
      rw [← dsimp% coeq_condition g₁ hι i, ← dsimp% coeq_condition g₂ hι i]
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ h₂ ⊢
      rw [h₁, h₂]
      simp only [Functor.map_comp, Category.assoc, CommaMorphism.w]
      simp only [← Category.assoc]
      congr 1
      exact (g i).left.hom.w
    · ext
      · simp [← dsimp% [g₁] coeq_condition g₁ hι i, ← h₁, g₁]
      · simp [← dsimp% [g₂] coeq_condition g₂ hι i, ← h₂, g₂]

private instance : PreservesColimitsOfShape (J κ f) F₁ :=
  F₁.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

private instance : IsFiltered (J κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

private instance : (π₁ κ f).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨exists_of_j₁, fun {d e} g₁ g₂ ↦ ?_⟩
  obtain ⟨j₁, a, ha⟩ := IsFilteredOrEmpty.cocone_maps g₁ g₂
  obtain ⟨j, b, ⟨c⟩⟩ := exists_of_j₁_of_j₂ j₁ e.snd
  obtain ⟨j', g, h, h₁, h₂⟩ := J.exists_hom (a ≫ b) c
  refine ⟨j', g, ?_⟩
  ext
  simp [← h₁, reassoc_of% dsimp% (CostructuredArrow.proj _ _ ⋙
    ObjectProperty.ι _).congr_map ha]

private instance : (π₂ κ f).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨exists_of_j₂, fun {d e} g₁ g₂ ↦ ?_⟩
  obtain ⟨j₂, a, ha⟩ := IsFilteredOrEmpty.cocone_maps g₁ g₂
  obtain ⟨j, b, ⟨c⟩⟩ := exists_of_j₁_of_j₂ e.fst j₂
  obtain ⟨j', g, h, h₁, h₂⟩ := J.exists_hom b (a ≫ c)
  refine ⟨j', g, ?_⟩
  ext
  simp [← h₂, reassoc_of% dsimp% (CostructuredArrow.proj _ _ ⋙
    ObjectProperty.ι _).congr_map ha]

instance : (Comma.isCardinalPresentable F₁ F₂ κ).ι.IsDense where
  isDenseAt f :=
    ⟨Comma.fstSndJointlyReflectColimit
      ((Functor.Final.isColimitWhiskerEquiv (π₁ κ f) _).2
        ((isCardinalPresentable C₁ κ).ι.denseAt f.left))
      ((Functor.Final.isColimitWhiskerEquiv (π₂ κ f) _).2
        ((isCardinalPresentable C₂ κ).ι.denseAt f.right))⟩

end isCardinalAccessibleCategory

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ] [LocallySmall.{w} D]

protected lemma isCardinalFilteredGenerator_isCardinalPresentable :
    (Comma.isCardinalPresentable F₁ F₂ κ).IsCardinalFilteredGenerator κ :=
  .mk' (isCardinalPresentable_le _ _ _)
    (fun f ↦ ⟨(CostructuredArrow (Comma.isCardinalPresentable F₁ F₂ κ).ι f), inferInstance,
      inferInstance, inferInstance,
      ⟨_, _, (Comma.isCardinalPresentable F₁ F₂ κ).ι.denseAt f⟩,
    fun g ↦ g.left.property⟩)

instance isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Comma F₁ F₂) κ where
  exists_generator :=
    ⟨_, inferInstance, Comma.isCardinalFilteredGenerator_isCardinalPresentable.{w} F₁ F₂ κ⟩

protected lemma isCardinalPresentable_eq :
    Comma.isCardinalPresentable F₁ F₂ κ = isCardinalPresentable (Comma F₁ F₂) κ := by
  rw [(Comma.isCardinalFilteredGenerator_isCardinalPresentable
      F₁ F₂ κ).isPresentable_eq_retractClosure,
    ObjectProperty.retractClosure_eq_self]

variable {F₁ F₂} in
protected lemma isCardinalPresentable_iff (f : Comma F₁ F₂) :
    IsCardinalPresentable f κ ↔
      IsCardinalPresentable f.left κ ∧ IsCardinalPresentable f.right κ := by
  change _ ↔ Comma.isCardinalPresentable F₁ F₂ κ f
  rw [Comma.isCardinalPresentable_eq]

instance : (Comma.fst F₁ F₂).PreservesCardinalPresentable κ where
  le_inverseImage_isCardinalPresentable f hf := by
    simp only [Comma.isCardinalPresentable_iff] at hf
    tauto

instance : (Comma.snd F₁ F₂).PreservesCardinalPresentable κ where
  le_inverseImage_isCardinalPresentable f hf := by
    simp only [Comma.isCardinalPresentable_iff] at hf
    tauto

section

variable [IsAccessibleCategory.{w} C₁] [IsAccessibleCategory.{w} C₂]
  [Functor.IsAccessible.{w} F₁] [Functor.IsAccessible.{w} F₂]
  [IsAccessibleCategory.{w} D]

instance isAccessibleCategory : IsAccessibleCategory.{w} (Comma F₁ F₂) := by
  obtain ⟨κ, _, _, _, _, _, _, _, _, _⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F₁ F₂
  exact ⟨κ, inferInstance, inferInstance⟩

instance : Functor.IsAccessible.{w} (Comma.fst F₁ F₂) := by
  obtain ⟨κ, _, _, _, _, _, _, _, _, _⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F₁ F₂
  exact ⟨κ, inferInstance, inferInstance⟩

instance : Functor.IsAccessible.{w} (Comma.snd F₁ F₂) := by
  obtain ⟨κ, _, _, _, _, _, _, _, _, _⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F₁ F₂
  exact ⟨κ, inferInstance, inferInstance⟩

end

end Comma

namespace Arrow

variable [IsAccessibleCategory.{w} D]

instance : IsAccessibleCategory.{w} (Arrow D) :=
  inferInstanceAs (IsAccessibleCategory.{w} (Comma _ _))

instance : Functor.IsAccessible.{w} (Arrow.leftFunc : Arrow D ⥤ D) :=
  inferInstanceAs (Functor.IsAccessible.{w} (Comma.fst _ _))

instance : Functor.IsAccessible.{w} (Arrow.rightFunc : Arrow D ⥤ D) :=
  inferInstanceAs (Functor.IsAccessible.{w} (Comma.snd _ _))

end Arrow

namespace CostructuredArrow

variable [IsAccessibleCategory.{w} C₁] [IsAccessibleCategory.{w} C₂]
  (F : C₁ ⥤ C₂) [Functor.IsAccessible.{w} F] (Y : C₂)

instance : IsAccessibleCategory.{w} (CostructuredArrow F Y) :=
  inferInstanceAs (IsAccessibleCategory.{w} (Comma _ _))

instance : Functor.IsAccessible.{w} (CostructuredArrow.proj F Y) :=
  inferInstanceAs (Functor.IsAccessible.{w} (Comma.fst _ _))

end CostructuredArrow

namespace StructuredArrow

variable [IsAccessibleCategory.{w} C₁] [IsAccessibleCategory.{w} C₂]
  (F : C₁ ⥤ C₂) [Functor.IsAccessible.{w} F] (X : C₂)

instance : IsAccessibleCategory.{w} (StructuredArrow X F) :=
  inferInstanceAs (IsAccessibleCategory.{w} (Comma _ _))

instance : Functor.IsAccessible.{w} (StructuredArrow.proj X F) :=
  inferInstanceAs (Functor.IsAccessible.{w} (Comma.snd _ _))

end StructuredArrow

namespace Over

variable [IsAccessibleCategory.{w} D] (Y : D)

instance : IsAccessibleCategory.{w} (Over Y) :=
  inferInstanceAs (IsAccessibleCategory.{w} (CostructuredArrow _ _))

instance : Functor.IsAccessible.{w} (Over.forget Y) :=
  inferInstanceAs (Functor.IsAccessible.{w} (CostructuredArrow.proj _ _))

end Over

namespace Under

variable [IsAccessibleCategory.{w} D] (X : D)

instance : IsAccessibleCategory.{w} (Under X) :=
  inferInstanceAs (IsAccessibleCategory.{w} (StructuredArrow _ _))

instance : Functor.IsAccessible.{w} (Under.forget X) :=
  inferInstanceAs (Functor.IsAccessible.{w} (StructuredArrow.proj _ _))

end Under

end CategoryTheory
