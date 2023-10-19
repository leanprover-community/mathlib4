/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
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

instance {α : Type w} {X : α → C} {B : C} (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).hasPullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.hasPullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)
-- TODO: move

variable {α : Type} [UnivLE.{w, (max u v)}] {X : α → C} [HasCoproduct X]
    [(Presieve.ofArrows X (fun i ↦ Sigma.ι X i)).hasPullbacks]
    (hd : ∀ i j, i ≠ j → IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)))
    [∀ i, Mono (Sigma.ι X i)]
-- `α` should be `Type w`

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prod_map {B : C} (π : (a : α) → X a ⟶ B) (F : Cᵒᵖ ⥤ Type max u v) :
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ B // Presieve.ofArrows X π f })) => F.obj (op f.fst)) ⟶
    ∏ fun a => F.obj (op (X a)) :=
  Pi.lift (fun a => Pi.π (fun (f : (Σ(Y : C), { f : Y ⟶ B // Presieve.ofArrows X π f })) =>
    F.obj (op f.fst)) ⟨X a, π a, Presieve.ofArrows.mk a⟩)

lemma one : F.map (opCoproductIsoProduct X).inv ≫
    Equalizer.forkMap F (Presieve.ofArrows X (fun j ↦ Sigma.ι X j)) ≫ prod_map _ F =
    piComparison F (fun z ↦ op (X z)) := by
  have : (Equalizer.forkMap F (Presieve.ofArrows X (fun j ↦ Sigma.ι X j)) ≫
      prod_map (fun j ↦ Sigma.ι X j) F) = Pi.lift (fun j ↦ F.map ((fun j ↦ Sigma.ι X j) j).op) := by
    ext; simp [prod_map, Equalizer.forkMap]
  rw [this]
  have t : Pi.lift (fun j ↦ Pi.π (fun a ↦ (op (X a))) j) = 𝟙 _ := by ext; simp -- why not just simp?
  have hh : (fun j ↦ (opCoproductIsoProduct X).inv ≫ (Sigma.ι X j).op) =
      fun j ↦ Pi.π (fun a ↦ (op (X a))) j
  · ext j
    exact opCoproductIsoProduct_inv_comp_ι _ _
  have : F.map (Pi.lift (fun j ↦ (opCoproductIsoProduct X).inv ≫ (Sigma.ι X j).op)) ≫
      piComparison F (fun z ↦ op (X z)) =
      (F.map (opCoproductIsoProduct X).inv ≫ Pi.lift fun j ↦ F.map ((fun j ↦ Sigma.ι X j) j).op)
  · rw [hh, t]
    ext j x
    simp only [Functor.map_id, Category.id_comp, piComparison, types_comp_apply,
      Types.pi_lift_π_apply, ← FunctorToTypes.map_comp_apply, congr_fun hh j]
  rw [← this, hh]
  congr
  ext
  simp [t]

lemma two : Equalizer.Presieve.firstMap F (Presieve.ofArrows X (fun j ↦ Sigma.ι X j)) =
    Equalizer.Presieve.secondMap F (Presieve.ofArrows X (fun j ↦ Sigma.ι X j)) := by
  ext a
  simp only [Equalizer.Presieve.SecondObj, Equalizer.Presieve.firstMap,
    Equalizer.Presieve.secondMap]
  ext ⟨j⟩
  simp only [Discrete.functor_obj, Types.pi_lift_π_apply, types_comp_apply]
  obtain ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩ := j
  cases' hf with i
  cases' hg with j
  by_cases hi : i = j
  · subst hi
    suffices pullback.fst (f := Sigma.ι X i) (g := Sigma.ι X i) =
      pullback.snd (f := Sigma.ι X i) (g := Sigma.ι X i) by rw [this]
    apply Mono.right_cancellation (f := Sigma.ι X i)
    exact pullback.condition
  · haveI := preservesTerminalOfIsSheafForEmpty F hF
    let i₁ : op (pullback (Sigma.ι X i) (Sigma.ι X j)) ≅ op (⊥_ _) :=
      (initialIsoIsInitial (hd i j hi)).op
    let i₂ : op (⊥_ C) ≅ (⊤_ Cᵒᵖ) :=
      (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)).symm
    apply_fun (F.mapIso i₁ ≪≫ F.mapIso i₂ ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    simp

lemma sigma_surjective {B : C} (π : (a : α) → X a ⟶ B) :
    Function.Surjective (fun a ↦ ⟨X a, π a, Presieve.ofArrows.mk a⟩ :
    α → Σ(Y : C), { f : Y ⟶ B // Presieve.ofArrows X π f }) :=
  fun ⟨_, ⟨_, hf⟩⟩ ↦ by cases' hf with a _; exact ⟨a, rfl⟩

lemma prod_map_inj : Function.Injective (prod_map (fun j ↦ Sigma.ι X j) F) := by
  intro a b h
  ext ⟨f⟩
  obtain ⟨c, hc⟩ := sigma_surjective (fun j ↦ Sigma.ι X j) f
  subst hc
  apply_fun Pi.π (fun i ↦ F.obj (op (X i))) c at h
  simp only [prod_map, Types.pi_lift_π_apply] at h
  exact h

variable (hF' : (Presieve.ofArrows X (fun i ↦ Sigma.ι X i)).IsSheafFor F)

lemma map_eq {B : C} (π : (a : α) → X a ⟶ B)
    (f : Σ(Y : C), { f : Y ⟶ B // Presieve.ofArrows X π f }) :
    ∃ i, f.fst = X i := by
  obtain ⟨Y, g, h⟩ := f
  cases' h with i
  exact ⟨i, rfl⟩

variable (X) in
lemma sigma_injective : Function.Injective
  ((fun a ↦ ⟨X a.val, Sigma.ι X a.val, Presieve.ofArrows.mk a.val⟩) :
   {a : α // ∀ b, X a = X b → a = b} →
    Σ(Y : C), {f : Y ⟶ ∐ X // (Presieve.ofArrows X (fun i ↦ Sigma.ι X i)) f}) := by
  intro a b h
  simp only [Sigma.mk.inj_iff] at h
  ext
  exact a.prop b h.1

noncomputable
instance : PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [← one F]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
    exact fun b ↦ hF' b (congr_fun (two F hF hd) b)
  · rw [isIso_iff_bijective]
    refine ⟨prod_map_inj _, ?_⟩
    intro a
    dsimp at a
    let i : ∏ (fun x ↦ F.obj (op (X x))) ≅ (x : α) → F.obj (op (X x)) := Types.productIso _
    let b : (f : Σ(Y : C), {f : Y ⟶ ∐ X // (Presieve.ofArrows X (fun i ↦ Sigma.ι X i)) f}) →
        F.obj (op f.fst) := by
      intro f
      rw [(map_eq (fun j ↦ Sigma.ι X j) f).choose_spec]
      exact i.hom a (map_eq (fun j ↦ Sigma.ι X j) f).choose
    use (Types.productIso.{max u v, v} _).inv b
    simp only [prod_map, eq_mpr_eq_cast, Types.productIso_hom_comp_eval_apply]
    ext ⟨j⟩
    simp only [Discrete.functor_obj, Pi.lift, Types.pi_lift_π_apply, Pi.π]
    sorry
