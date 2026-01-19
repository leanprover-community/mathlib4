module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# A theorem by Smith

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

noncomputable def attachCells : AttachCells J.homFamily (ιSuccObj g hJ₁) := by
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

noncomputable def attachCells' : AttachCells.{w} J.homFamily (ιSuccObj g hJ₁) :=
  haveI : Small.{w} (attachCells g hJ₁).ι := small_index I W g
  (attachCells g hJ₁).reindex (equivShrink.{w} _).symm

lemma pushouts_coproducts_ιSuccObj :
    (MorphismProperty.coproducts.{w} J).pushouts (ιSuccObj g hJ₁) := by
  simpa using (attachCells' g hJ₁).pushouts_coproducts

variable (hJ₂ : J ≤ I.rlp.llp ⊓ W)
  [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)]

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

variable [W.HasTwoOutOfThreeProperty]

noncomputable abbrev succ : Over Y := Over.mk (πSuccObj g hJ₁)

noncomputable def toSucc : g ⟶ succ g hJ₁ := Over.homMk (ιSuccObj g hJ₁)

include hJ₂ in
lemma prop_succ_hom (hg : W g.hom) :
    W (succ g hJ₁).hom :=
  W.of_precomp _ _ ((ιSuccObj_mem g hJ₁ hJ₂).2) (by simpa)

noncomputable def succStruct : SuccStruct (Over Y) where
  X₀ := Over.mk f
  succ g := succ g hJ₁
  toSucc g := toSucc g hJ₁

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

variable [HasIterationOfShape κ.ord.ToType C]

--#check (succStruct f hJ₁).iteration κ.ord.ToType

variable [MorphismProperty.IsStableUnderTransfiniteComposition.{w} (I.rlp.llp ⊓ W)]

end lemma_1_8

section

open lemma_1_8

variable
  [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)]
  (hJ₁ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
    ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)
  (hJ₂ : J ≤ I.rlp.llp ⊓ W)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

/-lemma lemma_1_8 {X Y : C} (w : X ⟶ Y) (hw : W w) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y)
      (ha : RelativeCellComplex (basicCell := fun (x : κ.ord.ToType) ↦ J.homFamily) a)
      (hb : I.rlp b), a ≫ b = w := by
  sorry-/

end

end

end SmallObject

end CategoryTheory
