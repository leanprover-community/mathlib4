/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.SetTheory.Cardinal.Arithmetic

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

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) if
any functor `F : A ⥤ J` from a category `A` such that `HasCardinalLT (Arrow A) κ`
admits a cocone. See `isCardinalFiltered_iff` for a more
concrete characterization of `κ`-filtered categories. -/
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
  exact (Cocone.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
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
this is a choice of objects in `J` which is the target of a map from any of
the objects `S k`. -/
noncomputable def max : J :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).pt

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a choice of map `S k ⟶ max S hS` for any `k : K`. -/
noncomputable def toMax (k : K) :
    S k ⟶ max S hS :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

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

/-- Variant of `IsFiltered.span` for `κ`-filtered categories. -/
lemma wideSpan {ι : Type v'} {j : J} {k : ι → J}
    (f : ∀ i, j ⟶ k i) (hι : HasCardinalLT ι κ) :
    ∃ (m : J) (a : ∀ i, k i ⟶ m) (b : j ⟶ m), ∀ i, f i ≫ a i = b := by
  let φ (i : ι) := f i ≫ toMax k hι i
  exact ⟨coeq φ hι, fun i ↦ toMax k hι i ≫ coeqHom φ hι,
    toCoeq φ hι, by simpa [φ] using coeq_condition φ hι⟩

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

lemma IsCardinalFiltered.nonempty (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] : Nonempty J :=
  have := isFiltered_of_isCardinalFiltered J κ
  IsFiltered.nonempty

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

-- TODO: make a version specialized to linear orders.
-- In a linear order, `h` is equivalent to `κ ≤ Order.cof J`
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

set_option backward.isDefEq.respectTransparency.types false in
instance (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    IsCardinalFiltered κ.ord.ToType κ :=
  isCardinalFiltered_preorder _ _ (fun ι f hs ↦ by
    have h : Function.Surjective (fun i ↦ (⟨f i, i, rfl⟩ : Set.range f)) := fun _ ↦ by aesop
    contrapose! hs
    rw [← hκ.out.cof_ord, ← Ordinal.cof_toType]
    refine (Order.cof_le fun j ↦ ?_).trans (Cardinal.mk_le_of_surjective h)
    obtain ⟨k, hk⟩ := hs j
    exact ⟨_, Set.mem_range_self k, hk.le⟩)

open IsCardinalFiltered

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
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

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
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
        ι.naturality {i j} f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f }⟩

set_option backward.isDefEq.respectTransparency.types false in
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
          simpa using! (c i).ι.naturality f }⟩

section

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  (h₁ : (∀ ⦃ι : Type w⦄ (j : ι → J) (_ : HasCardinalLT ι κ),
          ∃ (k : J), ∀ (i : ι), Nonempty (j i ⟶ k)))
  (h₂ : ∀ ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι → (j ⟶ k)) (_ : HasCardinalLT ι κ),
      ∃ (l : J) (a : k ⟶ l) (b : j ⟶ l), ∀ (i : ι), f i ≫ a = b)

include h₁ h₂ in
omit [Fact κ.IsRegular] in
lemma isCardinalFiltered_iff_aux₁ {ι : Type w} {j : J} {k : ι → J}
    (f : ∀ i, j ⟶ k i) (hι : HasCardinalLT ι κ) :
    ∃ (m : J) (a : ∀ i, k i ⟶ m) (b : j ⟶ m), ∀ i, f i ≫ a i = b := by
  obtain ⟨l, hl⟩ := h₁ k hι
  let a (i : ι) := (hl i).some
  obtain ⟨m, b, c, hm⟩ := h₂ (fun i ↦ f i ≫ a i) hι
  exact ⟨m, fun i ↦ a i ≫ b, c, by grind⟩

include h₁ h₂ in
lemma isCardinalFiltered_iff_aux₂ {ι : Type w} {j : ι → J} {k : J}
    (f₁ f₂ : ∀ i, j i ⟶ k) (hι : HasCardinalLT ι κ) :
    ∃ (l : J) (a : k ⟶ l), ∀ i, f₁ i ≫ a = f₂ i ≫ a := by
  have (i : ι) : ∃ (l : J) (p : k ⟶ l), f₁ i ≫ p = f₂ i ≫ p := by
    obtain ⟨l, a, b, hl⟩ := h₂ (Sum.elim (fun (_ : PUnit.{w + 1}) ↦ f₁ i)
      (fun (_ : PUnit.{w + 1}) ↦ f₂ i))
        (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
    exact ⟨l, a, (hl (Sum.inl .unit)).trans (hl (Sum.inr .unit)).symm⟩
  choose l p hp using this
  obtain ⟨l, a, b, h⟩ := isCardinalFiltered_iff_aux₁ h₁ h₂ p hι
  exact ⟨l, b, fun i ↦ by grind⟩

set_option backward.defeqAttrib.useBackward true in
variable (J κ) in
/-- A category is `κ`-filtered iff
1. any family of objects of cardinality `< κ` admits a map towards a common object, and
2. any family of morphisms `j ⟶ k` of cardinality `< κ` (between *fixed* objects
   `j` and `k`) can be coequalized by a suitable morphism `k ⟶ l`.
-/
lemma isCardinalFiltered_iff :
    IsCardinalFiltered J κ ↔
      (∀ ⦃ι : Type w⦄ (j : ι → J) (_ : HasCardinalLT ι κ),
        ∃ (k : J), ∀ (i : ι), Nonempty (j i ⟶ k)) ∧
      ∀ ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι → (j ⟶ k)) (_ : HasCardinalLT ι κ),
        ∃ (l : J) (a : k ⟶ l) (b : j ⟶ l), ∀ (i : ι), f i ≫ a = b := by
  refine ⟨fun _ ↦ ⟨fun ι j hι ↦ ⟨_, fun i ↦ ⟨toMax j hι i⟩⟩,
    fun ι j k f hι ↦ ⟨_, _, _, coeq_condition f hι⟩⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨fun {A _} F hA ↦ ?_⟩⟩
  obtain ⟨j, hj⟩ := h₁ F.obj (hasCardinalLT_of_hasCardinalLT_arrow hA)
  let a (i : A) : F.obj i ⟶ j := (hj i).some
  obtain ⟨l, b, hb⟩ := isCardinalFiltered_iff_aux₂ h₁ h₂
    (fun (f : Arrow A) ↦ F.map f.hom ≫ a f.right)
    (fun (f : Arrow A) ↦ a f.left) hA
  exact ⟨{
    pt := l
    ι.app i := a i ≫ b
    ι.naturality _ _ f := by simpa using hb (Arrow.mk f) }⟩

end

lemma IsCardinalFiltered.multicoequalizer
    {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {ι : Type v'} {j : ι → J} {k : J}
    (f₁ f₂ : ∀ i, j i ⟶ k) (hι : HasCardinalLT ι κ) :
    ∃ (l : J) (a : k ⟶ l), ∀ i, f₁ i ≫ a = f₂ i ≫ a := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨l, a, b, h⟩ := IsCardinalFiltered.wideSpan
    (fun i ↦ IsFiltered.coeqHom (f₁ i) (f₂ i)) hι
  exact ⟨l, b, fun i ↦ by rw [← h i, IsFiltered.coeq_condition_assoc]⟩

/-- If `F : J₁ ⥤ J₂` is final and `J₁` is `κ`-filtered, then
`J₂` is also `κ`-filtered. See also `IsFiltered.of_final`
(in `CategoryTheory.Limits.Final`) for the particular case of
filtered categories (`κ = ℵ₀`). -/
lemma IsCardinalFiltered.of_final
    {J₁ : Type u} [Category.{v} J₁] {J₂ : Type u'} [Category.{v'} J₂]
    (F : J₁ ⥤ J₂) [F.Final] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] :
    IsCardinalFiltered J₂ κ := by
  have := isFiltered_of_isCardinalFiltered J₁ κ
  obtain ⟨h₁, h₂⟩ := (Functor.final_iff_of_isFiltered F).1 inferInstance
  rw [isCardinalFiltered_iff]
  refine ⟨fun ι j hι ↦ ?_, fun ι j k f hι ↦ ?_⟩
  · choose a ha using fun i ↦ h₁ (j i)
    exact ⟨F.obj (IsCardinalFiltered.max a hι),
      fun i ↦ ⟨(ha i).some ≫ F.map (toMax a hι i)⟩⟩
  · by_cases h : Nonempty ι
    · obtain ⟨l, ⟨a⟩⟩ := h₁ k
      choose m b hb using fun (i : ι × ι) ↦ h₂ (f i.1 ≫ a) (f i.2 ≫ a)
      simp only [Category.assoc, Prod.forall] at hb
      obtain ⟨n, c, d, hn⟩ := wideSpan b
        (hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι)
      let i₀ : ι := Classical.arbitrary _
      exact ⟨F.obj n, a ≫ F.map d, f i₀ ≫ a ≫ F.map d,
        fun i ↦ by rw [← hn (i₀, i), Functor.map_comp, reassoc_of% (hb i₀ i)]⟩
    · simp only [not_nonempty_iff] at h
      obtain ⟨j', ⟨a⟩⟩ := h₁ j
      obtain ⟨k', ⟨b⟩⟩ := h₁ k
      exact ⟨F.obj (IsFiltered.max j' k'), b ≫ F.map (IsFiltered.rightToMax _ _),
        a ≫ F.map (IsFiltered.leftToMax _ _), by simp⟩

set_option backward.defeqAttrib.useBackward true in
lemma Limits.IsTerminal.isCardinalFiltered {J : Type u} [Category.{v} J]
    {X : J} (hX : IsTerminal X) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered J κ where
  nonempty_cocone _ _ := ⟨{ pt := X, ι.app _ := hX.from _ }⟩

lemma isCardinalFiltered_of_hasTerminal (J : Type u) [Category.{v} J]
    [HasTerminal J] (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered J κ :=
  terminalIsTerminal.isCardinalFiltered _

end CategoryTheory
