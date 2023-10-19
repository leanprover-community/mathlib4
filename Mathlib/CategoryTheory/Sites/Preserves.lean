/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Tactic.ApplyFun

universe v u w

open CategoryTheory Limits Opposite

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type (max u v)) [HasInitial C]
    (hF : (Presieve.ofArrows (X := ⊥_ C) Empty.elim instIsEmptyEmpty.elim).IsSheafFor F)

instance : (Presieve.ofArrows (X := ⊥_ C) Empty.elim instIsEmptyEmpty.elim).hasPullbacks := by
  constructor
  intro _ _ _ hf
  cases' hf with i
  exact Empty.elim i

instance : IsEmpty (Σ(Y : C), {f : Y ⟶ ⊥_ C //
    (Presieve.ofArrows (X := ⊥_ C) Empty.elim instIsEmptyEmpty.elim) f}) := by
  constructor
  rintro ⟨_, _, ⟨i⟩⟩
  exact Empty.elim i

lemma isoTerminalComparisonOfIsSheafForEmpty : IsIso (terminalComparison F) := by
  rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF
  intro b
  let S := (Presieve.ofArrows (X := ⊥_ C) Empty.elim instIsEmptyEmpty.elim)
  let SO := (fg : (Σ(Y : C), {f : Y ⟶ ⊥_ C // S f}) × (Σ(Y : C), {f : Y ⟶ ⊥_ C // S f})) →
      F.obj ((op (@pullback _ _ _ _ _ fg.1.2.1 fg.2.2.1
      (Presieve.hasPullbacks.has_pullbacks fg.1.2.2 fg.2.2.2))))
  let i : Equalizer.Presieve.SecondObj F S ≅ SO :=
      (Types.productIso.{(max u v), v} _)
  specialize hF ((Types.productIso.{(max u v), v} _).inv (IsEmpty.elim inferInstance)) ?_
  · have hU : Subsingleton SO := (Pi.uniqueOfIsEmpty _).instSubsingleton
    apply_fun i.hom using injective_of_mono _
    exact hU.allEq _ _
  · obtain ⟨x, _, h⟩ := hF
    let i' : ⊤_ Cᵒᵖ ≅ op (⊥_ C) := (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial))
    refine ⟨(F.mapIso i').inv x, by simp, ?_⟩
    intro z _
    apply_fun (F.mapIso i').hom using injective_of_mono _
    simp only [inv_hom_id_apply]
    apply h
    ext Y g hg
    cases' hg with i
    cases i

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` takes the initial object to the terminal object.
-/
noncomputable
def preservesTerminalOfIsSheafForEmpty : PreservesLimit (Functor.empty Cᵒᵖ) F :=
  letI := isoTerminalComparisonOfIsSheafForEmpty F hF
  PreservesTerminal.ofIsoComparison F

instance {α : Type w} (X : α → C) (B : C) (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).hasPullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.hasPullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)
-- TODO: move

variable {α : Type w} (X : α → C) [HasCoproduct X]
    [(Presieve.ofArrows X (fun i ↦ Sigma.ι X i)).hasPullbacks]
    (hF' : (Presieve.ofArrows X (fun i ↦ Sigma.ι X i)).IsSheafFor F)
    (hd : ∀ i j, i ≠ j → IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)))
