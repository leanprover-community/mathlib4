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

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

instance [LocallySmall.{w} C] : LocallySmall.{w} (Arrow C) where
  hom_small X Y :=
    small_of_injective (f := (fun f ↦ (f.left, f.right))) (by cat_disch)

namespace SmallObject

section

variable {J I W : MorphismProperty C}
  /-(h : J ≤ I.rlp.llp ⊓ W)
  (hJ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
    ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]-/

namespace lemma_1_8

variable {Y : C}

section

variable (g : W.Over ⊤ Y)

variable (I) in
structure Index where
  {A B : C}
  l : A ⟶ B
  hl : I l
  γ : Arrow.mk l ⟶ Arrow.mk g.hom

namespace Index

variable {g} (i : Index I g)

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
  obtain ⟨j, hj, a, b, fac⟩ := hJ i.γ i.hl g.prop
  exact ⟨
    { m := j.hom
      hm := hj
      α := a
      β := b
      fac := fac }⟩

noncomputable def factorization : i.Factorization J :=
  Nonempty.some (i.nonempty_factorization hJ)

end Index

variable (hJ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
  ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

open MorphismProperty in
variable (I) in
include κ in
lemma hasCoproductsOfShape_index : HasCoproductsOfShape (Index I g) C := by
  have := IsCardinalForSmallObjectArgument.locallySmall I κ
  have : Small.{w} I.toSet := by
    have := IsCardinalForSmallObjectArgument.isSmall (I := I) κ
    infer_instance
  have : Small.{w} (Index I g) := by
    let φ (x : Σ (l : I.toSet), Arrow.mk l.1.hom ⟶ Arrow.mk g.hom) : Index I g :=
      { l := x.1.1.hom
        hl := x.1.prop
        γ := x.2 }
    exact small_of_surjective (f := φ) (fun i ↦ ⟨⟨⟨Arrow.mk i.l, i.hl⟩, i.γ⟩, rfl⟩)
  have := IsCardinalForSmallObjectArgument.hasCoproducts I κ
  exact hasCoproductsOfShape_of_small.{w} C (Index I g)

noncomputable abbrev sigmaSrc : C :=
  haveI := hasCoproductsOfShape_index I g κ
  ∐ fun (i : Index I g) ↦ (i.factorization hJ).A'

noncomputable abbrev sigmaTgt : C :=
  haveI := hasCoproductsOfShape_index I g κ
  ∐ fun (i : Index I g) ↦ (i.factorization hJ).B'

noncomputable abbrev sigmaMap : sigmaSrc g hJ κ ⟶ sigmaTgt g hJ κ :=
  haveI := hasCoproductsOfShape_index I g κ
  Limits.Sigma.map (fun i ↦ (i.factorization hJ).m)

noncomputable abbrev sigmaDesc : sigmaSrc g hJ κ ⟶ g.left :=
  haveI := hasCoproductsOfShape_index I g κ
  Sigma.desc (fun i ↦ (i.factorization hJ).β.left)

noncomputable abbrev succObj : C :=
  haveI := MorphismProperty.IsCardinalForSmallObjectArgument.hasPushouts I κ
  pushout (sigmaDesc g hJ κ) (sigmaMap g hJ κ)

noncomputable abbrev ιSuccObj : g.left ⟶ succObj g hJ κ :=
  haveI := MorphismProperty.IsCardinalForSmallObjectArgument.hasPushouts I κ
  pushout.inl _ _

noncomputable abbrev πSuccObj : succObj g hJ κ ⟶ Y :=
  haveI := hasCoproductsOfShape_index I g κ
  haveI := MorphismProperty.IsCardinalForSmallObjectArgument.hasPushouts I κ
  pushout.desc g.hom (Sigma.desc (fun i ↦ (i.factorization hJ).β.right))

/-noncomputable abbrev succ : W.Over ⊤ Y :=
  MorphismProperty.Over.mk _ (πSuccObj g hJ κ) (by
    sorry)

noncomputable def toSucc : g ⟶ succ g hJ κ :=
  MorphismProperty.Over.homMk (ιSuccObj g hJ κ) (by simp) (by simp)-/

end

/-variable {X Y : C} {f : X ⟶ Y} (hf : W f)
  (hJ : ∀ {i w : Arrow C} (sq : i ⟶ w) (_ : I i.hom) (_ : W w.hom),
  ∃ (j : Arrow C) (_ : J j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

noncomputable def succStruct : SuccStruct (W.Over ⊤ Y) where
  X₀ := MorphismProperty.Over.mk _ f hf
  succ g := succ g hJ κ
  toSucc g := toSucc g hJ κ-/

end lemma_1_8

end

end SmallObject

end CategoryTheory
