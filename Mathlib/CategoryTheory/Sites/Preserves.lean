/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Tactic.ApplyFun

/-!
# Sheaves preserve products

We prove that a presheaf which satisfies the sheaf condition with respect to certain presieves
preserve "the corresponding products".

More precisely, given a presheaf `F : Cᵒᵖ ⥤ Type*`, we have:

## Main results

* If `F` satisfies the sheaf condition with respect to the empty sieve on the initial object of `C`,
  then `F` preserves terminal objects.
See `preservesTerminalOfIsSheafForEmpty`.

* If `F` furthermore satisfies the sheaf condition with respect to the presieve consisting of the
  inclusion arrows in a coproduct in `C`, then `F` preserves the corresponding product.
See `preservesProductOfIsSheafFor`.
-/

universe v u

namespace CategoryTheory.Presieve

open Limits Opposite

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type (max u v)) [HasInitial C]
    (hF : (ofArrows (X := ⊥_ C) Empty.elim instIsEmptyEmpty.elim).IsSheafFor F)

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` takes the initial object to the terminal object.
-/
noncomputable
def isTerminal_obj_initial_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op (⊥_ C))) := by
  refine @IsTerminal.ofUnique _ _ _ fun Y ↦ ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨fun _ ↦ t⟩, fun a ↦ by ext; exact h.2 _ (by tauto)⟩

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` preserves terminal objects.
-/
noncomputable
def preservesTerminalOfIsSheafForEmpty : PreservesLimit (Functor.empty Cᵒᵖ) F :=
  preservesTerminalOfIso F
    (F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (terminalIsoIsTerminal (isTerminal_obj_initial_of_isSheafFor_empty_presieve F hF)).symm)

variable {α : Type} {X : α → C} [HasCoproduct X]
    [(ofArrows X (fun i ↦ Sigma.ι X i)).hasPullbacks]
    (hd : ∀ i j, i ≠ j → IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)))
    [∀ i, Mono (Sigma.ι X i)]

variable (X)

namespace Preserves

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prodMap (F : Cᵒᵖ ⥤ Type (max u v)) :
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ ∐ X // ofArrows X (fun i ↦ Sigma.ι X i) f })) ↦
    F.obj (op f.fst)) ⟶ ∏ fun a ↦ F.obj (op (X a)) :=
  Pi.map' (fun a ↦ ⟨X a, (fun i ↦ Sigma.ι X i) a, ofArrows.mk a⟩) (fun _ ↦ 𝟙 _)

/--
Remove the factors coming from `a : α` where `X a` is an initial object.
-/
noncomputable
def removeInitial₁ : (∏ fun a ↦ F.obj (op (X a))) ⟶
    ∏ fun (a : {i : α // ¬ (Nonempty (IsInitial (X i))) }) ↦ F.obj (op (X a.val)) :=
  Pi.map' (fun a ↦ a.val) fun _ ↦ 𝟙 _

/--
Remove the factors coming from those `f` in the indexing set of `Equalizer.firstObj`
where `f.fst` is an initial object.
-/
noncomputable
def removeInitial₂ : (∏ fun (f : Σ(Y : C), { f : Y ⟶ ∐ X // ofArrows X (fun i ↦ Sigma.ι X i) f }) ↦
    F.obj (op f.fst)) ⟶ ∏ fun (f : {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) ↦
    F.obj (op f.val.fst) :=
  Pi.map' (fun a ↦ a.val) fun _ ↦ 𝟙 _

theorem sigma_surjective :
    Function.Surjective (fun a ↦ ⟨⟨X a.val, Sigma.ι X a.val, ofArrows.mk a.val⟩, a.prop⟩ :
    {i : α // ¬ (Nonempty (IsInitial (X i))) } → {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) :=
  fun ⟨⟨_, _, hg⟩, prop⟩ ↦ by cases' hg with i; exact ⟨⟨i, prop⟩, rfl⟩

theorem sigma_injective :
    Function.Injective (fun a ↦ ⟨⟨X a.val, Sigma.ι X a.val, ofArrows.mk a.val⟩, a.prop⟩ :
    {i : α // ¬ (Nonempty (IsInitial (X i))) } → {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) := by
  intro a b h
  simp only [Subtype.mk.injEq, Sigma.mk.inj_iff] at h
  ext
  by_contra hh
  specialize hd _ _ hh
  apply a.prop
  constructor
  refine IsInitial.ofIso hd ⟨pullback.fst, pullback.lift (𝟙 _) (eqToHom h.1) ?_, ?_, ?_⟩
  · refine eq_comp_of_heq h.1 ?_ ?_
    · rw [Subtype.heq_iff_coe_heq ?_ ?_] at h
      · exact h.2
      · rw [h.1]
      · rw [h.1]
    · simp
  · exact IsInitial.hom_ext hd _ _
  · simp

/--
After removing the factors that come from initial objects, the products are isomorphic.
-/
noncomputable
def prodIsoWithoutInitial : (∏ fun (f : {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) ↦
    F.obj (op f.val.fst)) ≅
    ∏ fun (a : {i : α // ¬ (Nonempty (IsInitial (X i))) }) ↦ F.obj (op (X a.val)) :=
  (Pi.whiskerEquiv (Equiv.ofBijective _ ⟨sigma_injective X hd, (sigma_surjective X)⟩)
    (fun _ ↦ Iso.refl _)).symm

theorem prodMap_comp : prodMap X F ≫ removeInitial₁ F X = removeInitial₂ F X ≫
    (prodIsoWithoutInitial F X hd).hom := by
  ext; simp [prodMap, removeInitial₁, removeInitial₂, prodIsoWithoutInitial, Pi.map']

theorem iso_prodMap_aux {β : Type v} {Z : β → Type (max u v)} (p : β → Prop)
    [∀ b, Decidable (p b)] (h : ∀ b, p b → Nonempty (Unique (Z b))) :
    IsIso (Pi.map' (fun a ↦ a.val) fun _ ↦ 𝟙 _ :
    (∏ Z) ⟶ ∏ fun (b : {a : β // ¬ (p a)}) ↦ Z b.val) := by
  rw [isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · intro a b hab
    ext ⟨j⟩
    simp only [Pi.map', Category.comp_id] at hab
    simp only [Discrete.functor_obj]
    by_cases hj : p j
    · obtain ⟨hj'⟩ := h j hj
      replace hj' := hj'.instSubsingleton
      exact hj'.allEq  _ _
    · apply_fun Pi.π (fun (b : {a : β // ¬ (p a)}) ↦ Z b.val) ⟨j, hj⟩ at hab
      simp only [Types.pi_lift_π_apply] at hab
      exact hab
  · intro a
    let i : ∀ (γ : Type v) (Y : γ → Type (max u v)), ∏ Y ≅ (x : γ) → Y x :=
      fun γ Y ↦ Types.productIso.{v, max u v} _
    have : ∀ b, p b → Inhabited (Z b) := fun b hb ↦ (h b hb).some.instInhabited
    let a' : (b : β) → Z b := fun b ↦ if hb : p b then @default _ (this b hb)
      else (i {a : β // ¬ (p a)} (fun c ↦ Z c.val)).hom a ⟨b, hb⟩
    refine ⟨(i _ Z).inv a', ?_⟩
    apply_fun (i {a : β // ¬ (p a)} (fun c ↦ Z c.val)).hom using injective_of_mono _
    ext j
    simp only [Types.productIso_hom_comp_eval_apply]
    rw [← types_comp_apply (g := Pi.π _ _)]
    simp only [Pi.map'_comp_π, Category.comp_id]
    rw [← types_comp_apply (g := Pi.π _ _)]
    simp only [Types.productIso_inv_comp_π]
    exact dif_neg j.prop

open Classical in
theorem iso_prodMap : IsIso (prodMap X F) :=
  let _ := preservesTerminalOfIsSheafForEmpty F hF
  have _ : IsIso (removeInitial₁ F X) :=
    iso_prodMap_aux (fun b ↦ Nonempty (IsInitial.{v, u} (X b))) fun b ⟨hb⟩ ↦
      ⟨(Types.isTerminalEquivUnique _).toFun <|
      IsTerminal.isTerminalObj F (op (X b)) (terminalOpOfInitial hb )⟩
  have _ : IsIso (removeInitial₂ F X) :=
    iso_prodMap_aux.{max u v, max u v} (fun (g : Σ(Y : C),
      { f : Y ⟶ ∐ X // ofArrows X (fun i ↦ Sigma.ι X i) f }) ↦ Nonempty (IsInitial g.fst))
      fun b ⟨hb⟩ ↦ ⟨(Types.isTerminalEquivUnique _) <|
      IsTerminal.isTerminalObj F (op b.fst) (terminalOpOfInitial hb )⟩
  have _ : IsIso (prodMap X F ≫ removeInitial₁ F X) := by
    rw [prodMap_comp F X hd]
    exact IsIso.comp_isIso
  IsIso.of_isIso_comp_right (prodMap X F) (removeInitial₁ F X)

theorem piComparison_fac : F.map (opCoproductIsoProduct X).inv ≫
    Equalizer.forkMap F (ofArrows X (fun j ↦ Sigma.ι X j)) ≫ prodMap X F =
    piComparison F (fun z ↦ op (X z)) := by
  have : (Equalizer.forkMap F (ofArrows X (fun j ↦ Sigma.ι X j)) ≫
      prodMap X F) = Pi.lift (fun j ↦ F.map ((fun j ↦ Sigma.ι X j) j).op) := by
    ext; simp [prodMap, Pi.map', Equalizer.forkMap]
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

theorem firstMap_eq_secondMap : Equalizer.Presieve.firstMap F (ofArrows X (fun j ↦ Sigma.ι X j)) =
    Equalizer.Presieve.secondMap F (ofArrows X (fun j ↦ Sigma.ι X j)) := by
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

end Preserves

open Preserves

/--
If `F` is a presheaf which `IsSheafFor` a presieve of arrows and the empty presieve, then it
preserves the product corresponding to the presieve of arrows.
-/
noncomputable
def preservesProductOfIsSheafFor (hF' : (ofArrows X (fun i ↦ Sigma.ι X i)).IsSheafFor F) :
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [← piComparison_fac F]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
    exact fun b ↦ hF' b (congr_fun (firstMap_eq_secondMap F hF X hd) b)
  · exact iso_prodMap F hF X hd

end CategoryTheory.Presieve
