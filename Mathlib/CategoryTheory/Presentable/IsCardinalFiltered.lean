/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # κ-filtered category

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category `J`: it means that any functor `A ⥤ J` from a small category such
that `Arrow A` is of cardinality `< κ` admits a cocone.
This generalizes the notion of filtered category.
Indeed, we obtain the equivalence `IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.
The API is mostly parallel to that of filtered categories.

A preordered type `J` is a `κ`-filtered category (i.e. `κ`-directed set)
if any subset of `J` of cardinality `< κ` has an upper bound.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) if
any functor `F : A ⥤ J` from a category `A` such that `HasCardinalLT (Arrow A) κ`
admits a cocone. -/
class IsCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)

lemma hasCardinalLT_arrow_walkingParallelFamily {T : Type u}
    {κ : Cardinal.{w}} (hT : HasCardinalLT T κ) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Arrow (WalkingParallelFamily T)) κ := by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

namespace IsCardinalFiltered

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/-- A choice of cocone for a functor `F : A ⥤ J` such that `HasCardinalLT (Arrow A) κ`
when `J` is a `κ`-filtered category, and `Arrow A` has cardinality `< κ`. -/
noncomputable def cocone {A : Type v'} [Category.{u'} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocones.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

variable (J) in
lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

variable (κ) in
lemma of_equivalence {J' : Type u'} [Category.{v'} J'] (e : J ≌ J') :
    IsCardinalFiltered J' κ where
  nonempty_cocone F hA := ⟨e.inverse.mapCoconeInv (cocone (F ⋙ e.inverse) hA)⟩

section max

variable {K : Type u'} (S : K → J) (hS : HasCardinalLT K κ)

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a  choice of objects in `J` which is the target of a map from any of
the objects `S k`. -/
noncomputable def max : J :=
  (cocone (Discrete.functor S) (by simpa using hS)).pt

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a choice of map `S k ⟶ max S hS` for any `k : K`. -/
noncomputable def toMax (k : K) :
    S k ⟶ max S hS :=
  (cocone (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

end max

section coeq

variable {K : Type v'} {j j' : J} (f : K → (j ⟶ j')) (hK : HasCardinalLT K κ)

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is an object of `J` where these morphisms
shall be equalized. -/
noncomputable def coeq : J :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, and `k : K`, this is a choice of morphism `j' ⟶ coeq f hK`. -/
noncomputable def coeqHom : j' ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is a morphism `j ⟶ coeq f hK` which is equal
to all compositions `f k ≫ coeqHom f hK` for `k : K`. -/
noncomputable def toCoeq : j ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]
lemma coeq_condition (k : K) : f k ≫ coeqHom f hK = toCoeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).w
    (.line k)

end coeq

end IsCardinalFiltered

open IsCardinalFiltered in
lemma isFiltered_of_isCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩

@[deprecated (since := "2025-10-07")] alias isFiltered_of_isCardinalDirected :=
  isFiltered_of_isCardinalFiltered

attribute [local instance] Cardinal.fact_isRegular_aleph0

lemma isCardinalFiltered_aleph0_iff (J : Type u) [Category.{v} J] :
    IsCardinalFiltered J Cardinal.aleph0.{w} ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0_iff] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

lemma isCardinalFiltered_preorder (J : Type w) [Preorder J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ ⦃K : Type w⦄ (s : K → J) (_ : Cardinal.mk K < κ),
      ∃ (j : J), ∀ (k : K), s k ≤ j) :
    IsCardinalFiltered J κ where
  nonempty_cocone {A _ F hA} := by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
        naturality _ _ _ := rfl }⟩

instance (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    IsCardinalFiltered κ.ord.toType κ :=
  isCardinalFiltered_preorder _ _ (fun ι f hs ↦ by
    have h : Function.Surjective (fun i ↦ (⟨f i, i, rfl⟩ : Set.range f)) := fun _ ↦ by aesop
    obtain ⟨j, hj⟩ := Ordinal.lt_cof_type
      (α := κ.ord.toType) (r := (· < ·)) (S := Set.range f)
      (lt_of_le_of_lt (Cardinal.mk_le_of_surjective h)
        (lt_of_lt_of_le hs (by simp [hκ.out.cof_eq])))
    exact ⟨j, fun i ↦ (hj (f i) (by simp)).le⟩)

open IsCardinalFiltered

instance isCardinalFiltered_under
    (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (j₀ : J) : IsCardinalFiltered (Under j₀) κ where
  nonempty_cocone {A _} F hA := ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    let c := cocone (F ⋙ Under.forget j₀) hA
    let x (a : A) : j₀ ⟶ IsFiltered.max j₀ c.pt := (F.obj a).hom ≫ c.ι.app a ≫
      IsFiltered.rightToMax j₀ c.pt
    have hκ' : HasCardinalLT A κ := hasCardinalLT_of_hasCardinalLT_arrow hA
    exact
      { pt := Under.mk (toCoeq x hκ')
        ι :=
          { app a := Under.homMk (c.ι.app a ≫ IsFiltered.rightToMax j₀ c.pt ≫ coeqHom x hκ')
              (by simpa [x] using coeq_condition x hκ' a)
            naturality a b f := by
              ext
              have := c.w f
              dsimp at this ⊢
              simp only [reassoc_of% this, Category.comp_id] } }⟩

instance isCardinalFiltered_prod (J₁ : Type u) (J₂ : Type u')
    [Category.{v} J₁] [Category.{v'} J₂] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] [IsCardinalFiltered J₂ κ] :
    IsCardinalFiltered (J₁ × J₂) κ where
  nonempty_cocone F hC := ⟨by
    let c₁ := cocone (F ⋙ Prod.fst _ _) hC
    let c₂ := cocone (F ⋙ Prod.snd _ _) hC
    exact
      { pt := (c₁.pt, c₂.pt)
        ι.app i := (c₁.ι.app i, c₂.ι.app i)
        ι.naturality i j f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f }⟩

instance isCardinalFiltered_pi {ι : Type u'} (J : ι → Type u) [∀ i, Category.{v} (J i)]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [∀ i, IsCardinalFiltered (J i) κ] :
    IsCardinalFiltered (∀ i, J i) κ where
  nonempty_cocone F hC := ⟨by
    let c (i : ι) := cocone (F ⋙ Pi.eval J i) hC
    exact
      { pt i := (c i).pt
        ι.app X i := (c i).ι.app X
        ι.naturality {X Y} f := by
          ext i
          simpa using (c i).ι.naturality f }⟩

end CategoryTheory
