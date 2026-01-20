/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Lemma 1.8 (T. Beke)

-/

@[expose] public section

universe w v u

open HomotopicalAlgebra CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

instance [LocallySmall.{w} C] : LocallySmall.{w} (Arrow C) where
  hom_small X Y :=
    small_of_injective (f := (fun f ↦ (f.left, f.right))) (by cat_disch)

namespace SmallObject

section

variable {J I W : MorphismProperty C}

namespace lemma_1_8

variable {X Y : C} (f : X ⟶ Y) (g : Over Y)

variable (I W) in
structure Index where
  {A B : C}
  l : A ⟶ B
  hl : I l
  γ : Arrow.mk l ⟶ Arrow.mk g.hom
  prop : W g.hom

namespace Index

variable {g} (i : Index I W g)

structure Factorization (J : MorphismProperty C) where
  {A' B' : C}
  m : A' ⟶ B'
  hm : J m
  α : Arrow.mk i.l ⟶ Arrow.mk m
  β : Arrow.mk m ⟶ Arrow.mk g.hom
  fac : α ≫ β = i.γ

namespace Factorization

variable {i} {Φ : i.Factorization J}

attribute [reassoc (attr := simp)] fac

@[reassoc (attr := simp)]
lemma fac_left : Φ.α.left ≫ Φ.β.left = i.γ.left := by
  simp [← Arrow.comp_left]

@[reassoc (attr := simp)]
lemma fac_right : Φ.α.right ≫ Φ.β.right = i.γ.right := by
  simp [← Arrow.comp_right]

end Factorization

variable (hJ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
  ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)

include hJ in
lemma nonempty_factorization :
    Nonempty (i.Factorization J) := by
  obtain ⟨j, hj, a, b, fac⟩ := hJ i.γ i.hl i.prop
  exact ⟨
    { m := j.hom
      hm := hj
      α := a
      β := b
      fac := fac }⟩

noncomputable def factorization : i.Factorization J :=
  Nonempty.some (i.nonempty_factorization hJ)

end Index

variable (I) in
lemma isEmpty_index (hg : ¬ W g.hom) : IsEmpty (Index I W g) where
  false i := hg i.prop

variable [MorphismProperty.IsSmall.{w} I] [LocallySmall.{w} C]

variable (I W) in
lemma small_index : Small.{w} (Index I W g) := by
  by_cases hg : W g.hom
  · let φ (x : Σ (l : I.toSet), Arrow.mk l.1.hom ⟶ Arrow.mk g.hom) : Index I W g :=
      { l := x.1.1.hom
        hl := x.1.prop
        γ := x.2
        prop := hg }
    exact small_of_surjective (f := φ) (fun i ↦ ⟨⟨⟨Arrow.mk i.l, i.hl⟩, i.γ⟩, rfl⟩)
  · have := isEmpty_index I g hg
    infer_instance

variable (hJ₁ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
  ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)
  [HasCoproducts.{w} C]

open MorphismProperty in
variable (I W) in
lemma hasCoproductsOfShape_index : HasCoproductsOfShape (Index I W g) C :=
  have := small_index.{w} I W g
  hasCoproductsOfShape_of_small.{w} C (Index I W g)

noncomputable abbrev sigmaSrc : C :=
  haveI := hasCoproductsOfShape_index I W g
  ∐ fun (i : Index I W g) ↦ (i.factorization hJ₁).A'

noncomputable abbrev sigmaTgt : C :=
  haveI := hasCoproductsOfShape_index I W g
  ∐ fun (i : Index I W g) ↦ (i.factorization hJ₁).B'

noncomputable abbrev sigmaMap : sigmaSrc g hJ₁ ⟶ sigmaTgt g hJ₁ :=
  haveI := hasCoproductsOfShape_index I W g
  Limits.Sigma.map (fun i ↦ (i.factorization hJ₁).m)

noncomputable abbrev sigmaDesc : sigmaSrc g hJ₁ ⟶ g.left :=
  haveI := hasCoproductsOfShape_index I W g
  Sigma.desc (fun i ↦ (i.factorization hJ₁).β.left)

variable [HasPushouts C]

noncomputable abbrev succObj : C :=
  pushout (sigmaDesc g hJ₁) (sigmaMap g hJ₁)

noncomputable abbrev inr : sigmaTgt g hJ₁ ⟶ succObj g hJ₁ :=
  pushout.inr _ _

noncomputable abbrev ιSuccObj : g.left ⟶ succObj g hJ₁ :=
  pushout.inl _ _

noncomputable abbrev πSuccObj : succObj g hJ₁ ⟶ Y :=
  haveI := hasCoproductsOfShape_index I W g
  pushout.desc g.hom (Sigma.desc (fun i ↦ (i.factorization hJ₁).β.right))

@[reassoc (attr := simp)]
lemma factorizationM_ι_inr (i : Index I W g) :
    haveI := hasCoproductsOfShape_index I W g
    (i.factorization hJ₁).m ≫
      Sigma.ι (fun i ↦ (i.factorization hJ₁).B') i ≫ inr g hJ₁ =
        (i.factorization hJ₁).β.left ≫ ιSuccObj g hJ₁ := by
  haveI := hasCoproductsOfShape_index I W g
  simpa using (Sigma.ι (fun i ↦ (i.factorization hJ₁).A') i ≫=
    pushout.condition (f := sigmaDesc g hJ₁) (g := sigmaMap g hJ₁)).symm

noncomputable def attachCells' : AttachCells J.homFamily (ιSuccObj g hJ₁) := by
  have := hasCoproductsOfShape_index I W g
  exact {
      ι := Index I W g
      π i := ⟨Arrow.mk (i.factorization hJ₁).m, (i.factorization hJ₁).hm⟩
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := coproductIsCoproduct _
      isColimit₂ := coproductIsCoproduct _
      m := sigmaMap g hJ₁
      g₁ := sigmaDesc g hJ₁
      g₂ := inr g hJ₁
      isPushout := IsPushout.of_hasPushout (sigmaDesc g hJ₁) (sigmaMap g hJ₁) }

noncomputable def attachCells : AttachCells.{w} J.homFamily (ιSuccObj g hJ₁) :=
  haveI : Small.{w} (attachCells' g hJ₁).ι := small_index I W g
  (attachCells' g hJ₁).reindex (equivShrink.{w} _).symm

lemma pushouts_coproducts_ιSuccObj :
    (MorphismProperty.coproducts.{w} J).pushouts (ιSuccObj g hJ₁) := by
  simpa using (attachCells g hJ₁).pushouts_coproducts

variable (hJ₂ : J ≤ I.rlp.llp ⊓ W)

variable [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)] in
include hJ₂ in
lemma ιSuccObj_mem :
    (I.rlp.llp ⊓ W) (ιSuccObj g hJ₁) :=
  have := small_index I W g
  have := hasCoproductsOfShape_index I W g
  have : (I.rlp.llp ⊓ W).IsStableUnderCoproductsOfShape (Index I W g) :=
    .of_equivalence (Discrete.equivalence (equivShrink.{w} (Index I W g)).symm)
  ((I.rlp.llp ⊓ W).of_isPushout
    (IsPushout.of_hasPushout _ _) (MorphismProperty.colimMap _
      (fun ⟨i⟩ ↦ hJ₂ _ ((i.factorization hJ₁).hm))))

noncomputable abbrev succ : Over Y := Over.mk (πSuccObj g hJ₁)

noncomputable def toSucc : g ⟶ succ g hJ₁ := Over.homMk (ιSuccObj g hJ₁)

variable [W.HasTwoOutOfThreeProperty]
  [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)] in
include hJ₂ in
lemma prop_succ_hom (hg : W g.hom) :
    W (succ g hJ₁).hom :=
  W.of_precomp _ _ ((ιSuccObj_mem g hJ₁ hJ₂).2) (by simpa)

@[simps]
noncomputable def succStruct : SuccStruct (Over Y) where
  X₀ := Over.mk f
  succ g := succ g hJ₁
  toSucc g := toSucc g hJ₁

noncomputable def attachCellsOfProp {Z₀ Z₁ : Over Y} (φ : Z₀ ⟶ Z₁)
    (hφ : (succStruct f hJ₁).prop φ) :
    AttachCells.{w} J.homFamily φ.left :=
  (attachCells Z₀ hJ₁).ofArrowIso
    ((Over.forget Y).mapArrow.mapIso hφ.arrowIso.symm)

include hJ₂ in
variable [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)] in
lemma succStruct_prop_le_inverseImage_rlp_llp_inter :
    (succStruct f hJ₁).prop ≤ (I.rlp.llp ⊓ W).inverseImage
      (Over.forget Y) := by
  intro Z₀ Z₁ φ hφ
  simp only [MorphismProperty.inverseImage_iff, Over.forget_obj, Over.forget_map]
  have : (MorphismProperty.coproducts.{w} (I.rlp.llp ⊓ W)).pushouts φ.left :=
    MorphismProperty.pushouts_monotone
      (MorphismProperty.coproducts_monotone (by simpa using hJ₂)) _
      ((attachCellsOfProp f hJ₁ φ hφ).pushouts_coproducts)
  exact MorphismProperty.pushouts_le _ (by simpa)

lemma exists_lift {Z₀ Z₁ : Over Y} (φ : Z₀ ⟶ Z₁) (hφ : (succStruct f hJ₁).prop φ)
    (h₀ : W Z₀.hom)
    {A B : C} (i : A ⟶ B) (hi : I i) (t : A ⟶ Z₀.left) (b : B ⟶ Y)
    (fac : t ≫ Z₀.hom = i ≫ b) :
    ∃ (l : B ⟶ Z₁.left), i ≫ l = t ≫ φ.left ∧ l ≫ Z₁.hom = b := by
  obtain rfl := hφ.succ_eq
  obtain rfl : φ = (succStruct f hJ₁).toSucc Z₀ := by simpa using hφ.fac
  have := small_index.{w} I W Z₀
  have := hasCoproductsOfShape_index I W Z₀
  let y : Index I W Z₀ :=
    { A := _
      B := _
      l := i
      hl := hi
      γ := Arrow.homMk t b
      prop := h₀ }
  refine ⟨(by exact (y.factorization hJ₁).α.right) ≫ Sigma.ι _ y ≫ inr Z₀ hJ₁,
    ?_, by cat_disch⟩
  have h₁ : _ = i ≫ _:= Arrow.w (y.factorization hJ₁).α
  dsimp at h₁ ⊢
  rw [← reassoc_of% h₁]
  cat_disch

end lemma_1_8

section

open lemma_1_8

variable
  [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [W.HasTwoOutOfThreeProperty]
  [MorphismProperty.IsStableUnderTransfiniteComposition.{w} (I.rlp.llp ⊓ W)]
  [MorphismProperty.IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)]
  (hJ₁ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
    ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)
  (hJ₂ : J ≤ I.rlp.llp ⊓ W)
  [HasColimitsOfSize.{w, w} C]
  [MorphismProperty.IsSmall.{w} I]
  [LocallySmall.{w} C]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hκ : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ)

include hJ₁ hJ₂ hκ in
lemma lemma_1_8 {X Y : C} (f : X ⟶ Y) (hf : W f) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y)
      (_ : RelativeCellComplex.{w} (basicCell := fun (_ : κ.ord.ToType) ↦ J.homFamily) a)
      (_ : I.rlp b), a ≫ b = f := by
  have : NoMaxOrder κ.ord.ToType :=
    Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  let σ := lemma_1_8.succStruct f hJ₁
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      ((I.rlp.llp ⊓ W).inverseImage (Over.forget Y)) :=
    ⟨fun J _ _ _ _ ↦ ⟨by
      rintro Z₀ Z₁ f ⟨hf⟩
      simp only [MorphismProperty.inverseImage_iff, Over.forget_obj, Over.forget_map]
      exact MorphismProperty.transfiniteCompositionsOfShape_le _ _ _ hf.map.mem⟩⟩
  refine ⟨(σ.iteration κ.ord.ToType).left, (σ.ιIteration κ.ord.ToType).left,
    (σ.iteration κ.ord.ToType).hom,
      { toTransfiniteCompositionOfShape :=
          (σ.transfiniteCompositionOfShapeιIteration
            κ.ord.ToType).toTransfiniteCompositionOfShape.map (Over.forget Y)
        attachCells j hj :=
          attachCellsOfProp f hJ₁ _ ((σ.transfiniteCompositionOfShapeιIteration
            κ.ord.ToType).map_mem j hj) }, ?_, by simp [σ]⟩
  have hι (j : κ.ord.ToType) :
      (I.rlp.llp ⊓ W) ((σ.ιIterationFunctor κ.ord.ToType).app j).left := by
    have := (((σ.transfiniteCompositionOfShapeιIteration κ.ord.ToType).iic
      j).ofLE (succStruct_prop_le_inverseImage_rlp_llp_inter f hJ₁ hJ₂)).mem_map
      (j := ⟨j, by simp⟩) (homOfLE bot_le)
    refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2 this
    exact Arrow.isoMk ((Over.forget _).mapIso
      (σ.transfiniteCompositionOfShapeιIteration κ.ord.ToType).isoBot.symm)
      (Iso.refl _) (by cat_disch)
  intro A B i hi
  have := hκ i hi
  constructor
  intro t b sq
  obtain ⟨x, t, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (isColimitOfPreserves (Over.forget _)
      (σ.isColimitIterationCocone κ.ord.ToType)) t
  have := (σ.transfiniteCompositionOfShapeιIteration κ.ord.ToType).map_mem
    x (not_isMax x)
  obtain ⟨l, fac₁, fac₂⟩ := exists_lift f hJ₁ _
    ((σ.transfiniteCompositionOfShapeιIteration κ.ord.ToType).map_mem x (not_isMax x))
      (W.of_precomp _ _ (hι x).2 (by simpa)) i hi t b (by simpa using sq.w)
  exact ⟨⟨{
    l := l ≫ ((σ.iterationCocone κ.ord.ToType).ι.app (Order.succ x)).left
    fac_left := by
      have := t ≫= (Over.forget _).congr_map ((σ.iterationCocone κ.ord.ToType).w
        (homOfLE (Order.le_succ x)))
      dsimp at this
      simpa [reassoc_of% fac₁] using this
    fac_right := by cat_disch
  }⟩⟩

end

end

end SmallObject

end CategoryTheory
