/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ObjectProperty.Ind

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

instance [P.RespectsLeft Q] : P.ind.RespectsLeft Q where
  precomp {X Y Z} i hi f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j ↦ ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

instance [P.RespectsIso] : P.ind.RespectsIso where
  postcomp {X Y Z} i (hi : IsIso i) f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j ↦ ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocones.ext (asIso i))) hs
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

/-- `ind` is idempotent if `P` implies finitely presentable. -/
lemma ind_ind (hp : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X Y f hf ↦ ?_) P.ind.le_ind
  have : P.underObj ≤ ObjectProperty.isFinitelyPresentable.{w} (Under X) := fun f hf ↦ hp _ hf
  simpa [ind_iff_ind_underMk, underObj_ind_eq_ind_underObj,
    ObjectProperty.ind_ind.{w} this] using hf

end CategoryTheory.MorphismProperty
