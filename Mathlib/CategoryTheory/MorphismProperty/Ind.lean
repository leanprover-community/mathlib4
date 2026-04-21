/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## Main definitions

- `CategoryTheory.MorphismProperty.ind`: `f` satisfies `ind P` if `f` is a filtered colimit of
  morphisms in `P`.

## Main results:

- `CategoryTheory.MorphismProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `pro P`.
- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w v u

namespace CategoryTheory.MorphismProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

/--
Let `P` be a property of morphisms. `P.ind` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : X ⟶ Yᵢ` and `sᵢ : Yᵢ ⟶ Y` indexed by `J`
such that
- `J` is filtered
- `Y ≅ colim Yᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = tᵢ ≫ sᵢ` for all `i`.

See `CategoryTheory.MorphismProperty.ind_iff_ind_under_mk` for an equivalent characterization
in terms of `Y` as an object of `Under X`.
-/
def ind (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ C) (t : (Functor.const J).obj X ⟶ D) (s : D ⟶ (Functor.const J).obj Y)
    (_ : IsColimit (Cocone.mk _ s)), ∀ j, P (t.app j) ∧ t.app j ≫ s.app j = f

lemma exists_hom_of_isFinitelyPresentable {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    {c : Cocone D} (hc : IsColimit c) {X A : C} {p : X ⟶ A} (hp : isFinitelyPresentable.{w} C p)
    (s : (Functor.const J).obj X ⟶ D) (f : A ⟶ c.pt) (h : ∀ (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    ∃ (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f :=
  hp.exists_hom_of_isColimit_under hc _ s _ h

lemma le_ind : P ≤ ind.{w} P := by
  intro X Y f hf
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const PUnit).obj Y, ?_, 𝟙 _, ?_, ?_⟩
  · exact { app _ := f }
  · exact isColimitConstCocone _ _
  · simpa

variable {P}

set_option backward.isDefEq.respectTransparency false in
lemma ind_iff_ind_underMk {X Y : C} (f : X ⟶ Y) :
    ind.{w} P f ↔ ObjectProperty.ind.{w} P.underObj (CategoryTheory.Under.mk f) := by
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, pres, hpres⟩ ↦ ?_⟩
  · refine ⟨J, ‹_›, ‹_›, ⟨Under.lift D t, ?_, ?_⟩, ?_⟩
    · exact { app j := CategoryTheory.Under.homMk (s.app j) (by simp [hst]) }
    · have : Nonempty J := IsFiltered.nonempty
      exact Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs
    · simp [underObj, hst]
  · refine ⟨J, ‹_›, ‹_›, pres.diag ⋙ CategoryTheory.Under.forget _, ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
    · exact { app j := (pres.diag.obj j).hom }
    · exact Functor.whiskerRight pres.ι (CategoryTheory.Under.forget X)
    · exact isColimitOfPreserves (CategoryTheory.Under.forget _) pres.isColimit
    · exact hpres j
    · simp

lemma underObj_ind_eq_ind_underObj (X : C) :
    underObj (ind.{w} P) (X := X) = ObjectProperty.ind.{w} P.underObj := by
  ext f
  simp [underObj, show f = CategoryTheory.Under.mk f.hom from rfl, ind_iff_ind_underMk]

variable (Q : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in
instance [P.RespectsLeft Q] : P.ind.RespectsLeft Q where
  precomp {X Y Z} i hi f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j ↦ ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

set_option backward.isDefEq.respectTransparency false in
instance [P.RespectsIso] : P.ind.RespectsIso where
  postcomp {X Y Z} i (hi : IsIso i) f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j ↦ ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocone.ext (asIso i))) hs
    · simp [reassoc_of% (hst j).2]

lemma ind_underObj_pushout {X Y : C} (g : X ⟶ Y) [HasPushouts C] [P.IsStableUnderCobaseChange]
    {f : Under X} (hf : ObjectProperty.ind.{w} P.underObj f) :
    ObjectProperty.ind.{w} P.underObj ((Under.pushout g).obj f) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  use J, inferInstance, inferInstance, pres.map (Under.pushout g)
  intro i
  exact P.pushout_inr _ _ (hpres i)

instance [P.IsStableUnderCobaseChange] [HasPushouts C] : P.ind.IsStableUnderCobaseChange := by
  refine .mk' fun A B A' f g _ hf ↦ ?_
  rw [ind_iff_ind_underMk] at hf ⊢
  exact ind_underObj_pushout g hf

instance [P.ContainsIdentities] : (ind.{w} P).ContainsIdentities where
  id_mem X := le_ind _ _ (P.id_mem X)

/-- `ind` is idempotent if `P` implies finitely presentable. -/
lemma ind_ind (hp : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X Y f hf ↦ ?_) P.ind.le_ind
  have : P.underObj ≤ ObjectProperty.isFinitelyPresentable.{w} (Under X) := fun f hf ↦ hp _ hf
  simpa [ind_iff_ind_underMk, underObj_ind_eq_ind_underObj,
    ObjectProperty.ind_ind.{w} this] using hf

set_option backward.isDefEq.respectTransparency false in
lemma ind_iff_exists (H : P ≤ isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y)
    [IsFinitelyAccessibleCategory.{w} (Under X)] :
    ind.{w} P f ↔ ∀ {Z : C} (p : X ⟶ Z) (g : Z ⟶ Y),
      isFinitelyPresentable.{w} _ p → p ≫ g = f →
      ∃ (W : C) (u : Z ⟶ W) (v : W ⟶ Y), u ≫ v = g ∧ P (p ≫ u) := by
  rw [ind_iff_ind_underMk, ObjectProperty.ind_iff_exists]
  · refine ⟨fun H Z p g hp hpg ↦ ?_, fun H Z g hZ ↦ ?_⟩
    · have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
      obtain ⟨W, u, v, huv, hW⟩ := H (CategoryTheory.Under.homMk (U := CategoryTheory.Under.mk p)
        (V := CategoryTheory.Under.mk f) g hpg)
      use W.right, u.right, v.right, congr($(huv).right)
      rwa [show p ≫ u.right = W.hom from CategoryTheory.Under.w u]
    · obtain ⟨W, u, v, huv, hW⟩ := H Z.hom g.right hZ (CategoryTheory.Under.w g)
      exact ⟨CategoryTheory.Under.mk (Z.hom ≫ u), CategoryTheory.Under.homMk u,
          CategoryTheory.Under.homMk v, by ext; simpa, hW⟩
  · intro Y hY
    exact H _ hY

/--
A property of morphisms `P` is said to pre-ind-spread if `P`-morphisms out of filtered colimits
descend to a finite level. More precisely, let `Dᵢ` be a filtered family of objects.
Then:

- If `f : colim Dᵢ ⟶ T` satisfies `P`, there exists an index `j` and a pushout square
  ```
    Dⱼ ----f'---> T'
    |             |
    |             |
    v             v
  colim Dᵢ --f--> T
  ```
  such that `f'` satisfies `P`.
-/
class PreIndSpreads (P : MorphismProperty C) : Prop where
  exists_isPushout {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    {c : Cocone D} (_ : IsColimit c) {T : C} (f : c.pt ⟶ T) :
    P f →
    ∃ (j : J) (T' : C) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ P f'

alias exists_isPushout_of_isFiltered := PreIndSpreads.exists_isPushout

set_option backward.isDefEq.respectTransparency false in
/-- If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is stable under composition if `P` is. -/
@[stacks 0BSI "The stacks project lemma is for the special case of ind-étale ring homomorphisms."]
lemma IsStableUnderComposition.ind_of_preIndSpreads
    [∀ X : C, (IsFinitelyAccessibleCategory.{w} (Under X))] [HasPushouts C]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] (H : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    rw [ind_iff_exists H]
    intro T p u hp hpu
    obtain ⟨J₁, _, _, D₁, s₁, t₁, ht₁, h₁⟩ := hf
    obtain ⟨J₂, _, _, D₂, s₂, t₂, ht₂, h₂⟩ := hg
    have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
    obtain ⟨j₂, q, hcomp, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
        ht₂ p ((Functor.const _).map f ≫ s₂) u <| by simp [h₂, hpu]
    obtain ⟨j₁, W, f', g', h, hf'⟩ :=
      P.exists_isPushout_of_isFiltered ht₁ (s₂.app j₂) (h₂ j₂).left
    let D' : Under j₁ ⥤ C :=
      (Under.post D₁ ⋙ Under.pushout f') ⋙ CategoryTheory.Under.forget _
    let c' : Cocone D' :=
      (Under.pushout f' ⋙ CategoryTheory.Under.forget _).mapCocone
        ((Cocone.mk _ t₁).underPost j₁) |>.extend h.isoPushout.inv
    let hc' : IsColimit c' :=
      IsColimit.extendIso _ <| isColimitOfPreserves _ (ht₁.underPost j₁)
    let s' : (Functor.const (Under j₁)).obj X ⟶ D' :=
      { app k := s₁.app k.right ≫ pushout.inl _ _
        naturality k l a := by
          have h2 := s₁.naturality a.right
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
          simp [h2, D'] }
    obtain ⟨j₃, v, hcomp', hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
        hc' p s' q <| fun k ↦ by
      simp [c', s', hcomp, reassoc_of% (h₁ k.right).right]
    refine ⟨D'.obj j₃, v, c'.ι.app j₃ ≫ t₂.app j₂, ?_, ?_⟩
    · rwa [reassoc_of% hq]
    · rw [hcomp']
      exact P.comp_mem _ _ (h₁ _).left (P.pushout_inl _ _ hf')

/-- If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is multiplicative if `P` is. -/
lemma IsMultiplicative.ind_of_preIndSpreads
    [∀ X : C, (IsFinitelyAccessibleCategory.{w} (Under X))] [HasPushouts C]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] (H : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsMultiplicative where
  __ := IsStableUnderComposition.ind_of_preIndSpreads H

end CategoryTheory.MorphismProperty
