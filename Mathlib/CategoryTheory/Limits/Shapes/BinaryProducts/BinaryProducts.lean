/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Binary (co)products

We define `prod X Y` and `coprod X Y` as limits and colimits of walking-pair diagrams.

Typeclasses `HasBinaryProducts` and `HasBinaryCoproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

@[expose] public noncomputable section

universe v v₁ u u₁ u₂

namespace CategoryTheory.Limits

open WalkingPair

variable {C : Type u} [Category.{v} C] {X Y : C}

to_dual_name_hint Prod Coprod, Mono Epi

/-- An abbreviation for `HasLimit (pair X Y)`. -/
@[to_dual /-- An abbreviation for `HasColimit (pair X Y)`. -/]
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or `X ⨯ Y`. -/
@[to_dual
/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y` or `X ⨿ Y`. -/]
abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

/-- Notation for the product -/
notation:20 X " ⨯ " Y:20 => prod X Y

/-- Notation for the coproduct -/
notation:20 X " ⨿ " Y:20 => coprod X Y

/-- The projection map to the first component of the product. -/
@[to_dual inl /-- The inclusion map from the first component of the coproduct. -/]
abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩

/-- The projection map to the second component of the product. -/
@[to_dual inr /-- The inclusion map from the second component of the coproduct. -/]
abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩

/-- The binary fan constructed from the projection maps is a limit. -/
@[to_dual /-- The binary cofan constructed from the coprojection maps is a colimit. -/]
def prodIsProd (X Y : C) [HasBinaryProduct X Y] :
    IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit (Cone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  ))

@[to_dual (attr := ext 1100)]
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
    (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
@[to_dual desc
/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/]
abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y]
    (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
@[to_dual /-- codiagonal arrow of the binary coproduct -/]
abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)

@[to_dual (attr := reassoc) inl_desc]
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.fst = f :=
  limit.lift_π _ _

@[to_dual (attr := reassoc) inr_desc]
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.snd = g :=
  limit.lift_π _ _

@[to_dual epi_desc_of_epi_left]
instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

@[to_dual epi_desc_of_epi_right]
instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ Prod.fst = f` and `l ≫ Prod.snd = g`. -/
@[to_dual desc'
/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
`coprod.inr ≫ l = g`. -/]
def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
`g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
@[to_dual
/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
`g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/]
def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)

section ProdLemmas

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[to_dual (attr := reassoc, simp) desc_comp]
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[to_dual codiag_comp]
theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y) :
    f ≫ diag Y = prod.lift f f := by simp

@[deprecated (since := "2026-09-26")] alias coprod.diag_comp := coprod.codiag_comp

@[to_dual (attr := reassoc (attr := simp)) inl_map]
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  limMap_π _ _

@[to_dual (attr := reassoc (attr := simp)) inr_map]
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g :=
  limMap_π _ _

@[to_dual (attr := simp)]
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[to_dual (attr := simp) desc_inl_inr]
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] :
    prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by ext <;> simp

@[to_dual (attr := simp, reassoc) map_desc]
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
    (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by ext <;> simp

-- `simp` can prove `coprod.map_desc_assoc` but not `prod.lift_map_assoc`.
attribute [simp] prod.lift_map_assoc

@[to_dual (attr := simp) desc_comp_inl_comp_inr]
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
    (g : W ⟶ X) (g' : Y ⟶ Z) : prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `map_fst` and `map_snd` can still work just
-- as well.
@[to_dual (attr := reassoc (attr := simp))]
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
    [HasBinaryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) := by ext <;> simp

-- I don't think it's a good idea to make any of the following three simp lemmas.
-- TODO: is it necessary to weaken the assumption here?
@[to_dual (attr := reassoc)]
theorem prod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f := by simp

@[to_dual (attr := reassoc)]
theorem prod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
    [HasBinaryProduct Z W] [HasBinaryProduct Y W] :
    prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) := by simp

@[to_dual (attr := reassoc)]
theorem prod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
    [HasBinaryProduct W Y] [HasBinaryProduct W Z] :
    prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g := by simp

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : X ≅ Z` induces an isomorphism `prod.mapIso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[to_dual (attr := simps)
/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : W ≅ Z` induces an isomorphism `coprod.mapIso f g : W ⨿ X ≅ Y ⨿ Z`. -/]
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z where
  hom := prod.map f.hom g.hom
  inv := prod.map f.inv g.inv

@[to_dual]
instance isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g) :=
  (prod.mapIso (asIso f) (asIso g)).isIso_hom

@[to_dual]
instance prod.map_mono {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr($h ≫ prod.fst)
    · rw [← cancel_mono g]
      simpa using congr($h ≫ prod.snd)⟩

@[to_dual (attr := reassoc) map_codiag]
theorem prod.diag_map {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ≫ prod.map f f = f ≫ diag Y := by simp

@[to_dual (attr := reassoc) map_inl_inr_codiag]
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)] :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd = 𝟙 (X ⨯ Y) := by simp

@[to_dual (attr := reassoc) map_comp_inl_inr_codiag]
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    diag (X ⨯ X') ≫ prod.map (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by simp

@[to_dual]
instance {X : C} [HasBinaryProduct X X] : IsSplitMono (diag X) :=
  IsSplitMono.mk' { retraction := prod.fst }

end ProdLemmas

variable (C)

/-- A category `HasBinaryProducts` if it has all limits of shape `Discrete WalkingPair`,
i.e. if it has a product for every pair of objects. -/
@[stacks 001T]
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

/-- A category `HasBinaryCoproducts` if it has all colimit of shape `Discrete WalkingPair`,
i.e. if it has a coproduct for every pair of objects. -/
@[stacks 04AP, to_dual existing]
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
@[to_dual /-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/]
theorem hasBinaryProducts_of_hasLimit_pair [∀ {X Y : C}, HasLimit (pair X Y)] :
    HasBinaryProducts C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoPair F).symm }

section

variable {C}

/-- The braiding isomorphism which swaps a binary product. -/
@[to_dual (attr := simps) /-- The braiding isomorphism which swaps a binary coproduct. -/]
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f := by simp

@[to_dual (attr := reassoc)]
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
@[to_dual (attr := reassoc) /-- The braiding isomorphism is symmetric. -/]
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id

/-- The associator isomorphism for binary products. -/
@[to_dual (attr := simps) /-- The associator isomorphism for binary coproducts. -/]
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

@[reassoc]
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).hom (𝟙 Z) ≫
        (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) (prod.associator X Y Z).hom =
      (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom := by
  simp

@[reassoc]
theorem prod.associator_naturality [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
      (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) := by
  simp

variable [HasTerminal C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[to_dual (attr := simps)
/-- The left unitor isomorphism for binary coproducts with the initial object. -/]
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[to_dual (attr := simps)
/-- The right unitor isomorphism for binary coproducts with the initial object. -/]
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[to_dual (attr := reassoc) leftUnitor_inv_naturality]
theorem prod.leftUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).hom = (prod.leftUnitor X).hom ≫ f :=
  prod.map_snd _ _

@[to_dual (attr := reassoc) leftUnitor_hom_naturality]
theorem prod.leftUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.leftUnitor_hom_naturality]

@[deprecated (since := "2026-09-26")]
alias coprod.leftUnitor_naturality := coprod.leftUnitor_hom_naturality

@[to_dual (attr := reassoc) rightUnitor_inv_naturality]
theorem prod.rightUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).hom = (prod.rightUnitor X).hom ≫ f :=
  prod.map_fst _ _

@[to_dual (attr := reassoc) rightUnitor_hom_naturality]
theorem prod.rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.rightUnitor_hom_naturality]

@[deprecated (since := "2026-09-26")]
alias coprod.rightUnitor_naturality := coprod.rightUnitor_hom_naturality

@[deprecated (since := "2026-09-26")]
alias prod_rightUnitor_inv_naturality := prod.rightUnitor_inv_naturality

theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).hom =
      prod.map (prod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

section

variable {C}
variable [HasBinaryCoproducts C]

theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).hom (𝟙 Z) ≫
        (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) (coprod.associator X Y Z).hom =
      (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom := by
  simp

theorem coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
      (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) := by
  simp

variable [HasInitial C]

theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).hom =
      coprod.map (coprod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

section ProdFunctor

variable {C} [HasBinaryProducts C]

/-- The binary product functor. -/
@[to_dual (attr := simps, implicit_reducible) /-- The binary coproduct functor. -/]
def prod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

/-- The product functor can be decomposed. -/
@[to_dual /-- The coproduct functor can be decomposed. -/]
def prod.functorLeftComp (X Y : C) :
    prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)

end ProdFunctor

section swap

variable {C} {s : BinaryFan X Y} {t : BinaryFan Y X}

/-- Construct `HasBinaryProduct Y X` from `HasBinaryProduct X Y`.
This can't be an instance, as it would cause a loop in typeclass search. -/
lemma HasBinaryProduct.swap (X Y : C) [HasBinaryProduct X Y] : HasBinaryProduct Y X :=
  .mk ⟨BinaryFan.swap (limit.cone (pair X Y)), (limit.isLimit (pair X Y)).binaryFanSwap⟩

end swap

end Limits

open Limits

variable {C : Type u} [Category.{v} C]

/-- Auxiliary definition for `Over.coprod`. -/
@[simps, implicit_reducible]
def Over.coprodObj [HasBinaryCoproducts C] {A : C} :
    Over A → Over A ⥤ Over A :=
  fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps, implicit_reducible]
def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj f := Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        simp }
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

end CategoryTheory
