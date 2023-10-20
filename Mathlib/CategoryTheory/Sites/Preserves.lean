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

variable [UnivLE.{w, (max u v)}] {α : Type} {X : α → C} [HasCoproduct X]
    [(Presieve.ofArrows X (fun i ↦ Sigma.ι X i)).hasPullbacks]
    (hd : ∀ i j, i ≠ j → IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)))
    [∀ i, Mono (Sigma.ι X i)]
-- `α` should be `Type w`

variable (X)

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prod_map (F : Cᵒᵖ ⥤ Type (max u v)) :
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ ∐ X // Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f })) ↦
    F.obj (op f.fst)) ⟶ ∏ fun a ↦ F.obj (op (X a)) :=
  Pi.map' (fun a ↦ ⟨X a, (fun i ↦ Sigma.ι X i) a, Presieve.ofArrows.mk a⟩) (fun _ ↦ 𝟙 _)

noncomputable
def prod_map₂ : (∏ fun a ↦ F.obj (op (X a))) ⟶
    ∏ fun (a : {i : α // ¬ (Nonempty (IsInitial (X i))) }) ↦ F.obj (op (X a.val)) :=
  Pi.map' (fun a ↦ a.val) fun _ ↦ 𝟙 _

noncomputable
def prod_map₃ : (∏ fun (f :
    (Σ(Y : C), { f : Y ⟶ ∐ X // Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f })) ↦
    F.obj (op f.fst)) ⟶ ∏ fun (f : {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) ↦
    F.obj (op f.val.fst) :=
  Pi.map' (fun a ↦ a.val) fun _ ↦ 𝟙 _

lemma sigma_surjective :
    Function.Surjective (fun a ↦ ⟨⟨X a.val, Sigma.ι X a.val, Presieve.ofArrows.mk a.val⟩, a.prop⟩ :
    {i : α // ¬ (Nonempty (IsInitial (X i))) } → {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) :=
  fun ⟨⟨_, _, hg⟩, prop⟩ ↦ by cases' hg with i; exact ⟨⟨i, prop⟩, rfl⟩

lemma eq_comp_of_heq {X Y Z W : C} (h : Y = Z) (f : Y ⟶ W) (g : Z ⟶ W) (i : X ⟶ Y) (j : X ⟶ Z)
    (hfg : HEq f g) (hij : i = j ≫ eqToHom h.symm) : i ≫ f = j ≫ g := by
  cases h; cases hfg; cases hij; simp only [eqToHom_refl, Category.comp_id]

lemma sigma_injective :
    Function.Injective (fun a ↦ ⟨⟨X a.val, Sigma.ι X a.val, Presieve.ofArrows.mk a.val⟩, a.prop⟩ :
    {i : α // ¬ (Nonempty (IsInitial (X i))) } → {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) := by
  intro a b h
  simp only [Subtype.mk.injEq, Sigma.mk.inj_iff] at h
  ext
  by_contra hh
  specialize hd _ _ hh
  apply a.prop
  constructor
  refine IsInitial.ofIso hd ⟨pullback.fst, pullback.lift (𝟙 _) (eqToHom h.1) ?_, ?_, ?_⟩
  · refine eq_comp_of_heq h.1 (Sigma.ι X a.val) (Sigma.ι X b.val) (𝟙 _) (eqToHom h.1) ?_ ?_
    · rw [Subtype.heq_iff_coe_heq ?_ ?_] at h
      · exact h.2
      · rw [h.1]
      · rw [h.1]
    · simp
  · exact IsInitial.hom_ext hd _ _
  · simp

noncomputable
def prod_iso₄ : (∏ fun (f : {g : Σ(Y : C), { f : Y ⟶ ∐ X //
    Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f } // ¬ (Nonempty (IsInitial g.fst)) }) ↦
    F.obj (op f.val.fst)) ≅
    ∏ fun (a : {i : α // ¬ (Nonempty (IsInitial (X i))) }) ↦ F.obj (op (X a.val)) :=
  (Pi.whiskerEquiv (Equiv.ofBijective _ ⟨sigma_injective X hd, (sigma_surjective X)⟩)
    (fun _ ↦ Iso.refl _)).symm

lemma prod_map_comp : prod_map X F ≫ prod_map₂ F X = prod_map₃ F X ≫ (prod_iso₄ F X hd).hom := by
  ext; simp [prod_map, prod_map₂, prod_map₃, prod_iso₄, Pi.map']

instance iso_prod_map_aux {β : Type w} {Z : β → Type (max w (max u v))} (p : β → Prop)
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
    let i : ∀ (γ : Type w) (Y : γ → Type (max w (max u v))), ∏ Y ≅ (x : γ) → Y x :=
      fun γ Y ↦ Types.productIso.{w, (max u v)} _
    haveI : ∀ b, p b → Inhabited (Z b) := fun b hb ↦ (h b hb).some.instInhabited
    let a' : (b : β) → Z b := fun b ↦ if hb : p b then @default _ (this b hb)
      else (i {a : β // ¬ (p a)} (fun c ↦ Z c.val)).hom a ⟨b, hb⟩
    use (i _ Z).inv a'
    apply_fun (i {a : β // ¬ (p a)} (fun c ↦ Z c.val)).hom using injective_of_mono _
    ext j
    simp only [Types.productIso_hom_comp_eval_apply]
    rw [← types_comp_apply (g := Pi.π _ _)]
    simp only [Pi.map'_comp_π]
    simp only [types_comp_apply, types_id_apply]
    rw [← types_comp_apply (g := Pi.π _ _)]
    simp only [Types.productIso_inv_comp_π]
    exact dif_neg j.prop

open Classical in
instance is_iso₂ : IsIso (prod_map₂ F X) :=
  let _ := preservesTerminalOfIsSheafForEmpty F hF
  iso_prod_map_aux.{v, u, 0} (fun b ↦ Nonempty (IsInitial (X b))) fun b ⟨hb⟩ ↦
    ⟨(Types.isTerminalEquivUnique _) <|
    IsTerminal.isTerminalObj F (op (X b)) (terminalOpOfInitial hb )⟩

open Classical in
instance is_iso₃ : IsIso (prod_map₃ F X) :=
  let _ := preservesTerminalOfIsSheafForEmpty F hF
  iso_prod_map_aux.{v, u, max u v} (fun (g : Σ(Y : C),
    { f : Y ⟶ ∐ X // Presieve.ofArrows X (fun i ↦ Sigma.ι X i) f }) ↦ Nonempty (IsInitial g.fst))
    fun b ⟨hb⟩ ↦ ⟨(Types.isTerminalEquivUnique _) <|
    IsTerminal.isTerminalObj F (op b.fst) (terminalOpOfInitial hb )⟩

instance iso_prod_map : IsIso (prod_map X F) := by
  haveI := is_iso₂ F hF X
  haveI : IsIso (prod_map X F ≫ prod_map₂ F X) := by
    rw [prod_map_comp F X hd]
    haveI := is_iso₃ F hF X
    exact IsIso.comp_isIso
  exact IsIso.of_isIso_comp_right (prod_map X F) (prod_map₂ F X)

lemma one : F.map (opCoproductIsoProduct X).inv ≫
    Equalizer.forkMap F (Presieve.ofArrows X (fun j ↦ Sigma.ι X j)) ≫ prod_map X F =
    piComparison F (fun z ↦ op (X z)) := by
  have : (Equalizer.forkMap F (Presieve.ofArrows X (fun j ↦ Sigma.ι X j)) ≫
      prod_map X F) = Pi.lift (fun j ↦ F.map ((fun j ↦ Sigma.ι X j) j).op) := by
    ext; simp [prod_map, Pi.map', Equalizer.forkMap]
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

variable (hF' : (Presieve.ofArrows X (fun i ↦ Sigma.ι X i)).IsSheafFor F)

noncomputable
instance : PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [← one F]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
    exact fun b ↦ hF' b (congr_fun (two F hF X hd) b)
  · exact iso_prod_map F hF X hd
