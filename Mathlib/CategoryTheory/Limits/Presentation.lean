/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# (Co)limit presentations

Let `J` and `C` be categories and `X : C`. We define type `ColimitPresentation J X` that contains
the data of objects `Dⱼ` and natural maps `sⱼ : Dⱼ ⟶ X` that make `X` the colimit of the `Dⱼ`.

## Main definitions:

- `CategoryTheory.Limits.ColimitPresentation`: A colimit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`.
- `CategoryTheory.Limits.ColimitPresentation.bind`: Given a colimit presentation of `X` and
  colimit presentations of the components, this is the colimit presentation over the sigma type.

## TODOs:

- Dualise to obtain `LimitPresentation`.
- Refactor `TransfiniteCompositionOfShape` so that it extends `ColimitPresentation`.
-/

universe s t w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- A colimit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`. -/
structure ColimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : Dᵢ ⟶ X`. -/
  ι : diag ⟶ (Functor.const J).obj X
  /-- `X` is the colimit of the `Dᵢ` via `sᵢ`. -/
  isColimit : IsColimit (Cocone.mk _ ι)

variable {J : Type w} [Category.{t} J] {X : C}

namespace ColimitPresentation

initialize_simps_projections ColimitPresentation (-isColimit)

/-- The cocone associated to a colimit presentation. -/
abbrev cocone (pres : ColimitPresentation J X) : Cocone pres.diag :=
  Cocone.mk _ pres.ι

/-- The canonical colimit presentation of any object over a point. -/
@[simps]
noncomputable
def self (X : C) : ColimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  ι := 𝟙 _
  isColimit := isColimitConstCocone _ _

/-- If `F` preserves colimits of shape `J`, it maps colimit presentations of `X` to
colimit presentations of `F(X)`. -/
@[simps]
noncomputable
def map (P : ColimitPresentation J X) {D : Type*} [Category D] (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : ColimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  ι := Functor.whiskerRight P.ι F ≫ (F.constComp _ _).hom
  isColimit := (isColimitOfPreserves F P.isColimit).ofIsoColimit (Cocones.ext (.refl _) (by simp))

/-- Map a colimit presentation under an isomorphism. -/
@[simps]
def ofIso (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y) : ColimitPresentation J Y where
  diag := P.diag
  ι := P.ι ≫ (Functor.const J).map e.hom
  isColimit := P.isColimit.ofIsoColimit (Cocones.ext e fun _ ↦ rfl)

section

variable {J : Type*} {I : J → Type*} [Category J] [∀ j, Category (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

set_option linter.unusedVariables false in
/-- The type underlying the category used in the construction of the composition
of colimit presentations. This is simply `Σ j, I j` but with a different category structure. -/
@[nolint unusedArguments]
def Total (P : ∀ j, ColimitPresentation (I j) (D.obj j)) : Type _ :=
  Σ j, I j

variable (P) in
/-- Constructor for `Total` to guide type checking. -/
abbrev Total.mk (i : J) (k : I i) : Total P := ⟨i, k⟩

/-- Morphisms in the `Total` category. -/
@[ext]
structure Total.Hom (k l : Total P) where
  /-- The underlying morphism in the first component. -/
  base : k.1 ⟶ l.1
  /-- A morphism in `C`. -/
  hom : (P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2
  w : (P k.1).ι.app k.2 ≫ D.map base = hom ≫ (P l.1).ι.app l.2 := by cat_disch

attribute [reassoc] Total.Hom.w

/-- Composition of morphisms in the `Total` category. -/
@[simps]
def Total.Hom.comp {k l m : Total P} (f : k.Hom l) (g : l.Hom m) : k.Hom m where
  base := f.base ≫ g.base
  hom := f.hom ≫ g.hom
  w := by
    simp only [Functor.const_obj_obj, Functor.map_comp, Category.assoc]
    rw [f.w_assoc, g.w]

@[simps! id_base id_hom comp_base comp_hom]
instance : Category (Total P) where
  Hom := Total.Hom
  id _ := { base := 𝟙 _, hom := 𝟙 _ }
  comp := Total.Hom.comp

section Small

variable {J : Type w} {I : J → Type w} [SmallCategory J] [∀ j, SmallCategory (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

lemma Total.exists_hom_of_hom {j j' : J} (i : I j) (u : j ⟶ j')
    [IsFiltered (I j')] [IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    ∃ (i' : I j') (f : Total.mk P j i ⟶ Total.mk P j' i'), f.base = u := by
  obtain ⟨i', q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (P j').isColimit
    ((P j).ι.app i ≫ D.map u)
  use i', { base := u, hom := q, w := by simp [← hq] }

instance [IsFiltered J] [∀ j, IsFiltered (I j)] : Nonempty (Total P) := by
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨i⟩ : Nonempty (I j) := IsFiltered.nonempty
  exact ⟨⟨j, i⟩⟩

instance [IsFiltered J] [∀ j, IsFiltered (I j)]
    [∀ j i, IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    IsFiltered (Total P) where
  cocone_objs k l := by
    let a := IsFiltered.max k.1 l.1
    obtain ⟨a', f, hf⟩ := Total.exists_hom_of_hom (P := P) k.2 (IsFiltered.leftToMax k.1 l.1)
    obtain ⟨b', g, hg⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.rightToMax k.1 l.1)
    refine ⟨⟨a, IsFiltered.max a' b'⟩, ?_, ?_, trivial⟩
    · exact f ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.leftToMax _ _) }
    · exact g ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.rightToMax _ _) }
  cocone_maps {k l} f g := by
    let a := IsFiltered.coeq f.base g.base
    obtain ⟨a', u, hu⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.coeqHom f.base g.base)
    have : (f.hom ≫ u.hom) ≫ (P _).ι.app _ = (g.hom ≫ u.hom) ≫ (P _).ι.app _ := by
      simp only [Category.assoc, Functor.const_obj_obj, ← u.w, ← f.w_assoc, ← g.w_assoc]
      rw [← Functor.map_comp, hu, IsFiltered.coeq_condition f.base g.base]
      simp
    obtain ⟨j, p, q, hpq⟩ := IsFinitelyPresentable.exists_eq_of_isColimit (P _).isColimit _ _ this
    dsimp at p q
    refine ⟨⟨a, IsFiltered.coeq p q⟩,
      u ≫ { base := 𝟙 _, hom := (P _).diag.map (p ≫ IsFiltered.coeqHom p q) }, ?_⟩
    apply Total.Hom.ext
    · simp [hu, IsFiltered.coeq_condition f.base g.base]
    · rw [Category.assoc] at hpq
      simp only [Functor.map_comp, comp_hom, reassoc_of% hpq]
      simp [← Functor.map_comp, ← IsFiltered.coeq_condition]

/-- If `P` is a colimit presentation over `J` of `X` and for every `j` we are given a colimit
presentation `Qⱼ` over `I j` of the `P.diag.obj j`, this is the refined colimit presentation of `X`
over `Total Q`. -/
@[simps]
def bind {X : C} (P : ColimitPresentation J X) (Q : ∀ j, ColimitPresentation (I j) (P.diag.obj j))
    [∀ j, IsFiltered (I j)] [∀ j i, IsFinitelyPresentable.{w} ((Q j).diag.obj i)] :
    ColimitPresentation (Total Q) X where
  diag.obj k := (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  ι.app k := (Q k.1).ι.app k.2 ≫ P.ι.app k.1
  ι.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
          ι.naturality {i i'} u := by
            let v : Total.mk Q j i ⟶ .mk _ j i' := { base := 𝟙 _, hom := (Q _).diag.map u }
            simpa using c.ι.naturality v }
      ι.naturality {j j'} u := by
        refine (Q j).isColimit.hom_ext fun i ↦ ?_
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          (Q j).isColimit.fac]
        obtain ⟨i', hom, rfl⟩ := Total.exists_hom_of_hom (P := Q) i u
        rw [reassoc_of% hom.w, (Q j').isColimit.fac]
        simpa using c.ι.naturality hom }
  isColimit.fac := fun c ⟨j, i⟩ ↦ by simp [P.isColimit.fac, (Q j).isColimit.fac]
  isColimit.uniq c m hm := by
    refine P.isColimit.hom_ext fun j ↦ ?_
    simp only [Functor.const_obj_obj, P.isColimit.fac]
    refine (Q j).isColimit.hom_ext fun i ↦ ?_
    simpa [(Q j).isColimit.fac] using hm (.mk _ j i)

end Small

end

end CategoryTheory.Limits.ColimitPresentation
