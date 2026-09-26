/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nima Rasekh, Aras Ergus
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Order.SuccPred.Basic

/-!
# Reedy categories

In this file, we introduce the definition of a Reedy structure
on a category `C` equipped with two classes of morphisms
`W₁` and `W₂` (these are sometimes denoted `C₋` and `C₊` in
the literature).

## TODO
* Construct the Reedy model category structure on the category of
functors `C ⥤ D` when `C` is a Reedy category and `D` a model category
https://github.com/leanprover-community/project-intentions/issues/5

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]

-/

@[expose] public section

open CategoryTheory

namespace HomotopicalAlgebra

open MorphismProperty in
/-- A Reedy structure on a category `C` equipped with two multiplicative
classes of morphisms `W₁` and `W₂` consists of the data of a degree
map for objects `deg : C → α`, where `α` is a well ordered type. The first
two axioms `lt₁` and `lt₂` express the behaviour of the degree with
respect to morphisms in `W₁` (resp. `W₂`) that are not identities, and
the last axiom says that any morphism can be factored in a unique way
as a morphism in `W₁` followed by a morphism in `W₂`. -/
structure ReedyStructure {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.IsMultiplicative] [W₂.IsMultiplicative]
    (α : Type*) [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α] where
  /-- the degree of an object -/
  deg : C → α
  lt₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f) : deg Y < deg X
  lt₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f) : deg X < deg Y
  nonempty_unique {X Y : C} (f : X ⟶ Y) :
    Nonempty (Unique (W₁.MapFactorizationData W₂ f))

namespace ReedyStructure

variable {C : Type*} [Category* C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure W₁ W₂ α)

/-- The opposite of a Reedy structure. -/
@[simps]
protected def op : ReedyStructure W₂.op W₁.op α where
  deg := r.deg ∘ Opposite.unop
  lt₁ f hf hf' := r.lt₂ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  lt₂ f hf hf' := r.lt₁ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  nonempty_unique f :=
    MorphismProperty.MapFactorizationData.opEquiv.uniqueCongr.nonempty_congr.1
      (r.nonempty_unique f.unop)

lemma le₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) : r.deg Y ≤ r.deg X := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₁ f hf hf').le

lemma le₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) : r.deg X ≤ r.deg Y := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₂ f hf hf').le

lemma identities_of_prop₁_of_eq {X Y : C} {f : X ⟶ Y} (hf : W₁ f) (h : r.deg X = r.deg Y) :
    MorphismProperty.identities _ f := by
  by_contra
  exact h.not_gt (r.lt₁ _ hf this)

lemma identities_of_prop₂_of_eq {X Y : C} {f : X ⟶ Y} (hf : W₂ f) (h : r.deg X = r.deg Y) :
    MorphismProperty.identities _ f := by
  by_contra
  exact h.not_lt (r.lt₂ _ hf this)

include r in
lemma subsingleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) :
    Subsingleton (W₁.MapFactorizationData W₂ f) := by
  have := (r.nonempty_unique f).some
  infer_instance

/-- The Reedy factorization of a morphism `f : X ⟶ Y` as a morphism in `W₁`
followed by a morphism in `W₂`. -/
@[no_expose]
noncomputable def mapFactorizationData {X Y : C} (f : X ⟶ Y) :
    W₁.MapFactorizationData W₂ f := by
  letI := (r.nonempty_unique f).some
  exact default

include r in
lemma unique_obj {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) :
    fac.Z = fac'.Z := by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  rfl

include r in
lemma unique {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) :
    ∃ (h : fac.Z = fac'.Z), fac.i = fac'.i ≫ eqToHom h.symm ∧ fac.p = eqToHom h ≫ fac'.p := by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  simp

/-- The degree of a morphism for a Reedy structure. It is defined as the degree of
the intermediate object in the Reedy factorization, but it is also the smallest
degree of an intermediate object in a factorization, see the lemma `degHom_le`. -/
@[no_expose]
noncomputable def degHom {X Y : C} (f : X ⟶ Y) : α := r.deg (r.mapFactorizationData f).Z

lemma degHom_eq {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f) :
    r.degHom f = r.deg h.Z := by
  have := r.subsingleton_mapFactorizationData
  rw [← Subsingleton.elim (r.mapFactorizationData f) h]
  rfl

lemma exists_fac {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.degHom f = r.deg Z :=
  ⟨_, _, _, (r.mapFactorizationData f).hi, (r.mapFactorizationData f).hp,
    (r.mapFactorizationData f).fac, rfl⟩

lemma degHom_le {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) :
    r.degHom (f ≫ g) ≤ r.deg Z := by
  obtain ⟨Zf, f₁, f₂, hf₁, hf₂, fac_f, eq_f⟩ := r.exists_fac f
  obtain ⟨Zg, g₁, g₂, hg₁, hg₂, fac_g, eq_g⟩ := r.exists_fac g
  obtain ⟨Zh, h₁, h₂, hh₁, hh₂, fac_h, eq_h⟩ := r.exists_fac (f₂ ≫ g₁)
  let factfg := MorphismProperty.MapFactorizationData.mk (f := f ≫ g) Zh (f₁ ≫ h₁) (h₂ ≫ g₂)
    (by simp [reassoc_of% fac_h, reassoc_of% fac_f, fac_g])
    (W₁.comp_mem _ _ hf₁ hh₁) (W₂.comp_mem _ _ hh₂ hg₂)
  rw [r.degHom_eq factfg]
  exact (r.le₁ _ hh₁).trans (r.le₂ _ hf₂)

lemma degHom_le_deg_left {X Y : C} (f : X ⟶ Y) :
    r.degHom f ≤ r.deg X := by
  simpa using r.degHom_le (𝟙 X) f

lemma degHom_le_deg_right {X Y : C} (f : X ⟶ Y) :
    r.degHom f ≤ r.deg Y := by
  simpa using r.degHom_le f (𝟙 Y)

lemma degHom_comp_le_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.degHom (f ≫ g) ≤ r.degHom f := by
  have ⟨_, f₁, f₂, _, _, h_fac, h_deg⟩ := r.exists_fac f
  rw [h_deg, ← h_fac, Category.assoc]
  exact r.degHom_le f₁ (f₂ ≫ g)

lemma degHom_comp_le_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.degHom (f ≫ g) ≤ r.degHom g := by
  have ⟨_, g₁, g₂, _, _, h_fac, h_deg⟩ := r.exists_fac g
  rw [h_deg, ← h_fac, ← Category.assoc]
  exact r.degHom_le (f ≫ g₁) g₂

lemma prop₂_of_degHom_eq_deg_left {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg X) :
    W₂ f := by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₁_of_eq hp (by aesop)
  obtain rfl : i = f := by simpa using fac
  exact hi

lemma prop₁_of_degHom_eq_deg_right {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg Y) :
    W₁ f := by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₂_of_eq hi (by aesop)
  obtain rfl : p = f := by simpa using fac
  exact hp

lemma degHom_lt_or_of_degHom_comp_lt
    {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) (hfg : r.degHom (f ≫ g) < r.deg Z) :
    r.degHom f < r.deg Z ∨ r.degHom g < r.deg Z := by
  contrapose! hfg
  let φ := MorphismProperty.MapFactorizationData.mk Z f g rfl
    (r.prop₁_of_degHom_eq_deg_right (le_antisymm (r.degHom_le_deg_right f) hfg.left))
    (r.prop₂_of_degHom_eq_deg_left (le_antisymm (r.degHom_le_deg_left g) hfg.right))
  rw [r.degHom_eq φ]

@[simp]
lemma degHom_id (X : C) : r.degHom (𝟙 X) = r.deg X :=
  r.degHom_eq (MorphismProperty.MapFactorizationData.mk X (𝟙 X) (𝟙 X) (by simp) (W₁.id_mem _)
  (W₂.id_mem _))

lemma deg_eq_of_iso {X Y : C} (e : X ≅ Y) : r.deg X = r.deg Y := by
  have {X Y : C} (e : X ≅ Y) : r.deg X ≤ r.deg Y := by
    rw [← r.degHom_id X, ← e.hom_inv_id]
    apply r.degHom_le
  exact le_antisymm (this e) (this e.symm)

include r in
lemma prop₁_of_iso {X Y : C} (e : X ≅ Y) : W₁ e.hom :=
  r.prop₁_of_degHom_eq_deg_right (by
    refine le_antisymm ?_ ?_
    · simpa using r.degHom_comp_le_right e.hom (𝟙 Y)
    · simpa using r.degHom_comp_le_right e.inv e.hom)

include r in
lemma prop₂_of_iso {X Y : C} (e : X ≅ Y) : W₂ e.hom :=
  (r.op.prop₁_of_iso e.op)

include r in
lemma skeletal : Skeletal C := by
  intro X Y ⟨e⟩
  exact (r.unique (f := e.hom)
    (.mk X (𝟙 X) e.hom (by simp) (W₁.id_mem X) (r.prop₂_of_iso e))
    (.mk Y e.hom (𝟙 Y) (by simp) (r.prop₁_of_iso e) (W₂.id_mem Y))).choose

end ReedyStructure

end HomotopicalAlgebra
