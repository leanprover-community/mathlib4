import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Opposites

universe u v w w'

namespace CategoryTheory

open Limits Category IsCofiltered

section Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J] (F F' : J ⥤ C)

open IsFiltered in
lemma HasLimit_of_transition_iso_of_isFiltered [IsFiltered J] (hF : ∀ {X Y : J} (u : X ⟶ Y),
    IsIso (F.map u)) : HasLimit F := by
  set X : J := Classical.choice nonempty
  refine HasLimit.mk {cone := ?_, isLimit := ?_}
  · refine {pt := F.obj X, π := ?_}
    refine {app := ?_, naturality := ?_}
    · intro Y
      have := hF (rightToMax X Y)
      exact F.map (leftToMax X Y) ≫ inv (F.map (rightToMax X Y))
    · intro Y Z u
      dsimp
      simp only [id_comp, assoc, IsIso.comp_inv_eq]
      have := hF (leftToMax (max X Z) (max X Y))
      rw [← cancel_mono (F.map (leftToMax (max X Z) (max X Y)))]
      have eq : F.map (leftToMax X Z) ≫ F.map (leftToMax (max X Z) (max X Y)) =
          F.map (leftToMax X Y) ≫ F.map (rightToMax (max X Z) (max X Y)) := by
        set v := coeqHom (leftToMax X Z ≫ (leftToMax (max X Z) (max X Y)))
          (leftToMax X Y ≫ rightToMax (max X Z) (max X Y))
        have := hF v
        rw [← cancel_mono (F.map v), ← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp,
          coeq_condition _ _]
      rw [eq]
      simp only [assoc]
      have := hF (leftToMax X Y)
      rw [cancel_epi (F.map (leftToMax X Y))]
      have := hF (rightToMax X Y)
      rw [← cancel_epi (F.map (rightToMax X Y)), IsIso.hom_inv_id_assoc]
      set v := coeqHom (rightToMax X Y ≫ rightToMax (max X Z) (max X Y))
        (u ≫ rightToMax X Z ≫ leftToMax (max X Z) (max X Y))
      have := hF v
      rw [← cancel_mono (F.map v), ← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp,
        ← F.map_comp, coeq_condition _ _]
  · refine IsLimit.mk (fun s ↦ s.π.app X) (by simp) ?_
    · intro s u h
      convert h X
      simp only [Functor.const_obj_obj, Functor.const_obj_map, id_eq, eq_mpr_eq_cast]
      have := hF (rightToMax X X)
      rw [← cancel_mono (F.map (rightToMax X X)), assoc, assoc, IsIso.inv_hom_id, comp_id]
      have := hF (coeqHom (leftToMax X X) (rightToMax X X))
      rw [← cancel_mono (F.map (coeqHom (leftToMax X X) (rightToMax X X))), assoc, assoc,
        ← F.map_comp, ← F.map_comp, coeq_condition _ _, cancel_mono]

lemma HasLimit_of_transition_iso_of_isCofiltered [IsCofiltered J] (hF : ∀ {X Y : J} (u : X ⟶ Y),
    IsIso (F.map u)) : HasLimit F := by
  set X : J := Classical.choice nonempty
  refine HasLimit.mk {cone := ?_, isLimit := ?_}
  · refine {pt := F.obj X, π := ?_}
    refine {app := ?_, naturality := ?_}
    · intro Y
      have := hF (minToRight Y X)
      exact inv (F.map (minToLeft X Y)) ≫ F.map (minToRight X Y)
    · intro Y Z u
      dsimp
      simp
      have := hF (minToLeft (min X Y) (min X Z))
      rw [← cancel_epi (F.map (minToLeft (min X Y) (min X Z)))]
      have eq :  F.map (minToLeft (min X Y) (min X Z)) ≫ F.map (minToRight X Y) ≫ F.map u =
          F.map (minToRight (min X Y) (min X Z)) ≫ F.map (minToRight X Z) := by
        set v := eqHom (minToLeft (min X Y) (min X Z) ≫ minToRight X Y ≫ u)
          (minToRight (min X Y) (min X Z) ≫ minToRight X Z) with vdef
        have := hF v
        rw [← cancel_epi (F.map v)]
        conv_lhs => rw [← F.map_comp, ← F.map_comp, ← F.map_comp, vdef, eq_condition _ _]
        simp only [Functor.map_comp, v]
      rw [eq]
      have := hF (minToRight X Z)
      have := hF (minToLeft X Z)
      rw [← cancel_mono (inv (F.map (minToRight X Z))), ← cancel_mono (F.map (minToLeft X Z))]
      simp only [assoc, IsIso.hom_inv_id, comp_id, IsIso.inv_hom_id]
      set v := eqHom (minToLeft (min X Y) (min X Z) ≫ minToLeft X Y)
        (minToRight (min X Y) (min X Z) ≫ minToLeft X Z)
      have := hF v
      rw [← cancel_epi (F.map v), ← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp,
        eq_condition _ _]
  · refine IsLimit.mk (fun s ↦ s.π.app X) ?_ ?_
    · intro s Y
      simp only [Functor.const_obj_obj, Functor.const_obj_map, id_eq, eq_mpr_eq_cast]
      have := s.π.naturality (minToLeft X Y)
      simp only [Functor.const_obj_obj, Functor.const_obj_map, id_comp] at this
      rw [this, assoc, IsIso.hom_inv_id_assoc, Cone.w]
    · intro s u h
      convert h X
      simp
      conv_lhs => rw [← comp_id u]
      congr 1
      have := hF (minToLeft X X)
      rw [← cancel_epi (F.map (minToLeft X X)), comp_id, IsIso.hom_inv_id_assoc]
      set v := eqHom (minToLeft X X) (minToRight X X)
      have := hF v
      rw [← cancel_epi (F.map v), ← F.map_comp, eq_condition _ _, F.map_comp]

lemma HasLimit_of_transition_eventually_iso [IsCofiltered J] (X : J)
    (hF : ∀ {Y Z : Over X} (u : Y ⟶ Z), IsIso (F.map u.1)) : HasLimit F := by
  have : HasLimit ((Over.forget X) ⋙ F) := HasLimit_of_transition_iso_of_isCofiltered _ hF
  exact Functor.Initial.hasLimit_of_comp (Over.forget X)

noncomputable def Hom_of_almost_NatTrans_aux [HasLimit F] [HasLimit F']
    (α : (X : J) → (F.obj X ⟶ F'.obj X)) {X : J} [(Over.forget X).Initial]
    (nat : ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1) :
    Limits.limit F ⟶ Limits.limit F' := by
  refine (Functor.Initial.limitIso (Over.forget X) F).inv ≫ ?_ ≫
    (Functor.Initial.limitIso (Over.forget X) F').hom
  exact limMap {app := fun Y ↦ α Y.1, naturality := nat}

@[simp]
noncomputable def iso_limit_of_map [HasLimit F] [IsCofiltered J] {X X' : J} (u : X ⟶ X') :
    Limits.limit (Over.forget X' ⋙ F) ≅ Limits.limit (Over.forget X ⋙ F) := by
  set ι : Over.map u ⋙ Over.forget X' ≅ Over.forget X :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by aesop)
  have := Limits.hasLimit_of_iso ((isoWhiskerRight ι F).symm ≪≫ Functor.associator _ _ _)
  set α := Limits.limit.pre (Over.forget X' ⋙ F) (Over.map u) ≫ (Limits.HasLimit.isoOfNatIso
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ι F)).hom
  have : IsIso α := by
    have := Functor.Initial.limit_pre_isIso (Over.forget X) (G := F)
    have := Functor.Initial.limit_pre_isIso (Over.forget X') (G := F)
    refine IsIso.of_isIso_fac_left ?_ (f := Limits.limit.pre F (Over.forget X'))
      (h := Limits.limit.pre F (Over.forget X))
    ext
    dsimp [α]
    simp only [assoc, HasLimit.isoOfNatIso_hom_π, Functor.comp_obj, Over.forget_obj,
      Over.map_obj_left, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.associator_inv_app, whiskerRight_app, id_comp, limit.pre_π_assoc, limit.w,
      limit.pre_π, α]
  exact asIso α

lemma iso_limit_of_map_prop₀ [HasLimit F] [IsCofiltered J] {X X' : J} (u : X ⟶ X') :
    Limits.limit.pre F (Over.forget X') ≫ (iso_limit_of_map F u).hom = Limits.limit.pre
    F (Over.forget X) := by aesop

lemma iso_limit_of_map_prop [HasLimit F] [IsCofiltered J] {X X' : J} (u : X ⟶ X') :
    iso_limit_of_map F u ≪≫ Functor.Initial.limitIso (Over.forget X) F =
    Functor.Initial.limitIso (Over.forget X') F := by
  rw [← Iso.symm_eq_iff]
  ext1
  rw [← cancel_mono (iso_limit_of_map F u).hom, Iso.trans_symm, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_hom, assoc, Iso.inv_hom_id, comp_id, Iso.symm_hom]
  ext
  rw [← cancel_epi (Functor.Initial.limitIso (Over.forget X') F).hom]
  dsimp [Functor.Initial.limitIso_inv]
  simp only [limit.pre_π, Over.forget_obj, assoc, HasLimit.isoOfNatIso_hom_π, Functor.comp_obj,
    Over.map_obj_left, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_inv_app, whiskerRight_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Functor.map_id, comp_id]

lemma Hom_of_almost_NatTrans_aux_indep_bound_aux [HasLimit F] [HasLimit F'] [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F'.obj X)) {X X' : J} (u : X ⟶ X')
    (nat : ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∀ ⦃Y Z : Over X'⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1) :
    Hom_of_almost_NatTrans_aux F F' α nat =
    Hom_of_almost_NatTrans_aux F F' α nat' := by
  set e₂ := Functor.Initial.limitIso (Over.forget X') F
  set e'₂ := Functor.Initial.limitIso (Over.forget X') F'
  set e₁ := Functor.Initial.limitIso (Over.forget X) F
  set e'₁ := Functor.Initial.limitIso (Over.forget X) F'
  set f₂ : limit (Over.forget X' ⋙ F) ⟶ limit (Over.forget X' ⋙ F') :=
    limMap {app := fun Y ↦ α Y.1, naturality := nat'}
  set f₁ : limit (Over.forget X ⋙ F) ⟶ limit (Over.forget X ⋙ F') :=
    limMap {app := fun Y ↦ α Y.1, naturality := nat}
  change e₁.inv ≫ f₁ ≫ e'₁.hom = e₂.inv ≫ f₂ ≫ e'₂.hom
  set I : Over X ⥤ Over X' := Over.map u
  set ι : I ⋙ Over.forget X' ≅ Over.forget X :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by aesop)
  have eq : e₂ = iso_limit_of_map F u ≪≫ e₁ := (iso_limit_of_map_prop F u).symm
  have eq' : e'₂ = iso_limit_of_map F' u ≪≫ e'₁ := (iso_limit_of_map_prop F' u).symm
  have eq'' : f₁ = (iso_limit_of_map F u).inv ≫ f₂ ≫ (iso_limit_of_map F' u).hom := by
    ext
    simp [f₁, f₂]
  rw [eq, eq', eq'']
  rw [Iso.trans_inv, Iso.trans_hom]
  simp only [assoc]

lemma Hom_of_almost_NatTrans_aux_indep_bound [HasLimit F] [HasLimit F'] [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F'.obj X)) {X X' : J}
    (nat : ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∀ ⦃Y Z : Over X'⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1) :
    Hom_of_almost_NatTrans_aux F F' α nat =
    Hom_of_almost_NatTrans_aux F F' α nat' := by
  have nat'' : ∀ ⦃Y Z : Over (min X X')⦄ (u : Y ⟶ Z),
      F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1 :=
    fun _ _ u ↦ nat ((Over.map (minToLeft X X')).map u)
  rw [← Hom_of_almost_NatTrans_aux_indep_bound_aux F F' α (minToLeft X X') nat'' nat,
    Hom_of_almost_NatTrans_aux_indep_bound_aux F F' α (minToRight X X') nat'' nat']

lemma Hom_of_almost_NatTrans_aux_indep_map_aux [HasLimit F] [HasLimit F']
    (α α' : (X : J) → (F.obj X ⟶ F'.obj X)) {X : J} [(Over.forget X).Initial]
    (nat : ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (eq : ∀ (Y : Over X), α Y.1 = α' Y.1) :
    Hom_of_almost_NatTrans_aux F F' α nat = Hom_of_almost_NatTrans_aux F F' α'
    (fun Y Z u ↦ by rw [← eq Y, ← eq Z]; exact nat u) := by
  simp only [Hom_of_almost_NatTrans_aux, Iso.cancel_iso_hom_right_assoc, Iso.cancel_iso_inv_left]
  congr 1
  ext
  simp only [Functor.comp_obj, Monotone.functor_obj, eq]

lemma Hom_of_almost_NatTrans_aux_indep_map [HasLimit F] [HasLimit F'] [IsCofiltered J]
    (α α' : (X : J) → (F.obj X ⟶ F'.obj X)) {X X' : J}
    (nat : ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∀ ⦃Y Z : Over X'⦄ (u : Y ⟶ Z), F.map u.1 ≫ α' Z.1 = α' Y.1 ≫ F'.map u.1)
    (eq : ∃ (X'' : J), ∀ (Y : Over X''), α Y.1 = α' Y.1) :
    Hom_of_almost_NatTrans_aux F F' α nat =
    Hom_of_almost_NatTrans_aux F F' α' nat' := by
  obtain ⟨X'', eq⟩ := eq
  set A := min X'' (min X X')
  have nat₁'' : ∀ ⦃Y Z : Over A⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1 :=
    fun Y Z u ↦ nat (Over.homMk u.1 : Over.mk (Y.hom ≫ minToRight _ _ ≫ minToLeft _ _) ⟶
      Over.mk (Z.hom ≫ minToRight _ _ ≫ minToLeft _ _))
  have nat₂'' : ∀ ⦃Y Z : Over A⦄ (u : Y ⟶ Z), F.map u.1 ≫ α' Z.1 = α' Y.1 ≫ F'.map u.1 :=
    fun Y Z u ↦ nat' (Over.homMk u.1 : Over.mk (Y.hom ≫ minToRight _ _ ≫ minToRight _ _) ⟶
      Over.mk (Z.hom ≫ minToRight _ _ ≫ minToRight _ _))
  rw [Hom_of_almost_NatTrans_aux_indep_bound F F' α nat nat₁'',
    Hom_of_almost_NatTrans_aux_indep_bound F F' α' nat' nat₂'']
  rw [Hom_of_almost_NatTrans_aux_indep_map_aux F F' α α' nat₁''
    (fun Y ↦ eq (Over.mk (Y.hom ≫ minToLeft _ _)))]

noncomputable def Hom_of_almost_NatTrans [HasLimit F] [HasLimit F'] [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F'.obj X))
    (nat : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1) :
    Limits.limit F ⟶ Limits.limit F' :=
  Hom_of_almost_NatTrans_aux F F' α nat.choose_spec

lemma Hom_of_almost_NatTrans_indep [HasLimit F] [HasLimit F'] [IsCofiltered J]
    (α α' : (X : J) → (F.obj X ⟶ F'.obj X))
    (nat : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∃ (X' : J), ∀ ⦃Y Z : Over X'⦄ (u : Y ⟶ Z), F.map u.1 ≫ α' Z.1 = α' Y.1 ≫ F'.map u.1)
    (eq : ∃ (X'' : J), ∀ (Y : Over X''), α Y.1 = α' Y.1) :
    Hom_of_almost_NatTrans F F' α nat = Hom_of_almost_NatTrans F F' α' nat' := by
  simp only [Hom_of_almost_NatTrans]
  rw [Hom_of_almost_NatTrans_aux_indep_map]
  exact eq

lemma almost_id_almost_natTrans (α : (X : J) → (F.obj X ⟶ F.obj X))
    (isId : ∃ (X : J), ∀ (Y : Over X), α Y.1 = 𝟙 (F.obj Y.1)) :
    ∃ (X : J), ∀ (Y Z : Over X) (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F.map u.1 := by
  use isId.choose
  intro Y Z _
  rw [isId.choose_spec Y, isId.choose_spec Z]
  simp

lemma Hom_of_almost_NatTrans_id [HasLimit F] [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F.obj X)) (isId : ∃ (X : J), ∀ (Y : Over X), α Y.1 = 𝟙 (F.obj Y.1)) :
    Hom_of_almost_NatTrans F F α (almost_id_almost_natTrans F α isId) = 𝟙 (limit F) := by
  dsimp [Hom_of_almost_NatTrans]
  set nat : ∀ ⦃Y Z : Over isId.choose⦄ (u : Y ⟶ Z), F.map u.left ≫ α Z.left =
      α Y.left ≫ F.map u.left :=
    fun Y Z _ ↦ by rw [isId.choose_spec Y, isId.choose_spec Z, id_comp, comp_id]
  rw [Hom_of_almost_NatTrans_aux_indep_bound F F α
    (almost_id_almost_natTrans F α isId).choose_spec nat,
    Hom_of_almost_NatTrans_aux_indep_map_aux F F α (fun X ↦ 𝟙 _) nat isId.choose_spec]
  dsimp [Hom_of_almost_NatTrans_aux]
  rw [← cancel_mono (Functor.Initial.limitIso (Over.forget isId.choose) F).inv]
  simp only [assoc, Iso.hom_inv_id, comp_id, id_comp]
  ext
  erw [limit.pre_π]
  simp only [Functor.comp_obj, Over.forget_obj, assoc, limMap_π, comp_id]
  erw [limit.pre_π]
  simp only [Over.forget_obj]

variable (F'' : J ⥤ C)

lemma comp_almost_natTrans [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F'.obj X)) (β : (X : J) → (F'.obj X ⟶ F''.obj X))
    (nat : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F'.map u.1 ≫ β Z.1 = β Y.1 ≫ F''.map u.1) :
    ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z),
    F.map u.1 ≫ α Z.1 ≫ β Z.1 = (α Y.1 ≫ β Y.1) ≫ F''.map u.1 := by
  use min nat.choose nat'.choose
  intro Y Z u
  erw [reassoc_of% (nat.choose_spec (Over.homMk u.1 : Over.mk (Y.hom ≫ minToLeft _ _) ⟶ Over.mk
    (Z.hom ≫ minToLeft _ _))), nat'.choose_spec (Over.homMk u.1 : Over.mk (Y.hom ≫ minToRight _ _)
    ⟶ Over.mk (Z.hom ≫ minToRight _ _))]
  simp only [Functor.const_obj_obj, Over.mk_left, Functor.id_obj, Over.homMk_left, assoc]

-- Which one of the following two statements is really used?
lemma Hom_of_almost_NatTrans_comp_aux [HasLimit F] [HasLimit F'] [HasLimit F''] [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F'.obj X)) (β : (X : J) → (F'.obj X ⟶ F''.obj X))
    (nat : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F'.map u.1 ≫ β Z.1 = β Y.1 ≫ F''.map u.1) :
    Hom_of_almost_NatTrans F F' α nat ≫ Hom_of_almost_NatTrans F' F'' β nat' =
    Hom_of_almost_NatTrans F F'' (fun n ↦ α n ≫ β n) (comp_almost_natTrans F F' F'' α β nat nat')
    := by
  dsimp [Hom_of_almost_NatTrans]
  set X := min (min nat.choose nat'.choose) (comp_almost_natTrans F F' F'' α β nat nat').choose
  rw [← Hom_of_almost_NatTrans_aux_indep_bound F F'' (fun X ↦ α X ≫ β X) (X := X)
    (fun Y Z u ↦ ((comp_almost_natTrans F F' F'' α β nat nat').choose_spec
    (Over.homMk u.1 : Over.mk (Y.hom ≫ minToRight _ _) ⟶ Over.mk (Z.hom ≫ minToRight _ _))))
    (comp_almost_natTrans F F' F'' α β nat nat').choose_spec,
    ← Hom_of_almost_NatTrans_aux_indep_bound F F' α (X := X) (fun Y Z u ↦ nat.choose_spec
    (Over.homMk u.1 : Over.mk (Y.hom ≫ minToLeft _ _ ≫ minToLeft _ _) ⟶
    Over.mk (Z.hom ≫ minToLeft _ _ ≫ minToLeft _ _))) nat.choose_spec,
    ← Hom_of_almost_NatTrans_aux_indep_bound F' F'' β (X := X) (fun Y Z u ↦ nat'.choose_spec
    (Over.homMk u.1 : Over.mk (Y.hom ≫ minToLeft _ _ ≫ minToRight _ _) ⟶
    Over.mk (Z.hom ≫ minToLeft _ _ ≫ minToRight _ _))) nat'.choose_spec]
  simp only [Hom_of_almost_NatTrans_aux, assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_inv_left]
  rw [← cancel_mono (Functor.Initial.limitIso (Over.forget X) F'').inv]
  simp only [assoc, Iso.hom_inv_id, comp_id]
  ext
  simp only [Functor.comp_obj, Over.forget_obj, assoc, limMap_π, limMap_π_assoc]

lemma Hom_of_almost_NatTrans_comp [HasLimit F] [HasLimit F'] [HasLimit F''] [IsCofiltered J]
    (α : (X : J) → (F.obj X ⟶ F'.obj X)) (β : (X : J) → (F'.obj X ⟶ F''.obj X))
    (γ : (X : J) → (F.obj X ⟶ F''.obj X))
    (nat : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ α Z.1 = α Y.1 ≫ F'.map u.1)
    (nat' : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F'.map u.1 ≫ β Z.1 = β Y.1 ≫ F''.map u.1)
    (nat'' : ∃ (X : J), ∀ ⦃Y Z : Over X⦄ (u : Y ⟶ Z), F.map u.1 ≫ γ Z.1 = γ Y.1 ≫ F''.map u.1)
    (eq : ∃ (X : J), ∀ ⦃Y : Over X⦄, γ Y.1 = α Y.1 ≫ β Y.1) :
    Hom_of_almost_NatTrans F F' α nat ≫ Hom_of_almost_NatTrans F' F'' β nat' =
    Hom_of_almost_NatTrans F F'' γ nat'' := by
  rw [Hom_of_almost_NatTrans_indep F F'' γ (fun X ↦ α X ≫ β X) nat'' (comp_almost_natTrans
    F F' F'' α β nat nat') eq]
  exact Hom_of_almost_NatTrans_comp_aux F F' F'' α β nat nat'

end Limits

section Shift

variable {C : Type u} {A : Type*} [CategoryTheory.Category.{v, u} C] [AddCommMonoid A]
  [CategoryTheory.HasShift C A]

attribute [local instance] endofunctorMonoidalCategory

open Category

@[reassoc]
lemma shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd'_hom_app (m₁ m₂ m₃ m : A)
    (hm : m₂ + m₃ = m) (X : C) :
    (shiftFunctorComm C m₁ m).hom.app X ≫
    ((shiftFunctorAdd' C m₂ m₃ m hm).hom.app X)⟦m₁⟧' =
  (shiftFunctorAdd' C m₂ m₃ m hm).hom.app (X⟦m₁⟧) ≫
    ((shiftFunctorComm C m₁ m₂).hom.app X)⟦m₃⟧' ≫
    (shiftFunctorComm C m₁ m₃).hom.app (X⟦m₂⟧) := by
  rw [← cancel_mono ((shiftFunctorComm C m₁ m₃).inv.app (X⟦m₂⟧)),
    ← cancel_mono (((shiftFunctorComm C m₁ m₂).inv.app X)⟦m₃⟧')]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  simp only [shiftFunctorComm_eq C _ _ _ rfl]
  dsimp
  simp only [Functor.map_comp, Category.assoc]
  slice_rhs 3 4 => rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rw [Category.id_comp]
  conv_rhs => rw [← Functor.map_comp, Iso.inv_hom_id_app]; erw [Functor.map_id, Category.comp_id]
  slice_lhs 2 3 => rw [shiftFunctorAdd'_assoc_hom_app m₂ m₃ m₁ m (m₁ + m₃) (m₁ + m) hm
    (add_comm _ _) (by rw [hm]; exact add_comm _ _)]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  slice_lhs 2 3 => rw [← shiftFunctorAdd'_assoc_hom_app m₂ m₁ m₃ (m₁ + m₂) (m₁ + m₃) (m₁ + m)
    (add_comm _ _) rfl (by rw [add_comm m₂, add_assoc, hm])]
  slice_lhs 3 4 => rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  erw [Category.id_comp]
  rw [shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃ (m₁ + m₂) m (m₁ + m) rfl hm (by rw [add_assoc, hm])]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]

end Shift

/-
section Shift

variable {C : Type u} {A : Type*} [CategoryTheory.Category.{v, u} C] [AddMonoid A]
  [CategoryTheory.HasShift C A]

attribute [local instance] endofunctorMonoidalCategory

open Category

lemma shiftFunctorAdd_symm_eqToIso (i j i' j' : A) (hi : i = i') (hj : j = j') :
    (shiftFunctorAdd C i j).symm = eqToIso (by rw [hi, hj]) ≪≫
    (shiftFunctorAdd C i' j').symm ≪≫ eqToIso (by rw [hi, hj]) := by
  ext X
  simp only [Functor.comp_obj, Iso.symm_hom, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app]
  have := Functor.LaxMonoidal.μ_natural_left (shiftMonoidalFunctor C A) (X := {as := i})
    (Y := {as := i'}) (eqToHom (by rw [hi])) {as := j}
  apply_fun (fun T ↦ T.app X) at this
  simp only [endofunctorMonoidalCategory_tensorObj_obj, MonoidalCategory.eqToHom_whiskerRight,
    NatTrans.comp_app] at this
  change _ ≫ (shiftFunctorAdd C i' j).inv.app X = (shiftFunctorAdd C i j).inv.app X ≫ _ at this
  simp only [Functor.comp_obj, endofunctorMonoidalCategory_whiskerRight_app] at this
  set f : ((shiftMonoidalFunctor C A).obj (MonoidalCategory.tensorObj { as := i' }
    { as := j })).obj X ⟶ ((shiftMonoidalFunctor C A).obj
    (MonoidalCategory.tensorObj { as := i } { as := j })).obj X := eqToHom (by rw [hi])
  rw [← cancel_mono f] at this
  simp only [eqToHom_map, eqToHom_app, assoc, eqToHom_trans, eqToHom_refl, comp_id, f] at this
  rw [← this]
  have := Functor.LaxMonoidal.μ_natural_right (shiftMonoidalFunctor C A) (X := {as := j})
    (Y := {as := j'}) {as := i'} (eqToHom (by rw [hj]))
  apply_fun (fun T ↦ T.app X) at this
  simp only [endofunctorMonoidalCategory_tensorObj_obj, MonoidalCategory.eqToHom_whiskerRight,
    NatTrans.comp_app] at this
  change _ ≫ (shiftFunctorAdd C i' j').inv.app X = (shiftFunctorAdd C i' j).inv.app X ≫ _ at this
  simp only [Functor.comp_obj, MonoidalCategory.whiskerLeft_eqToHom, eqToHom_app,
    endofunctorMonoidalCategory_tensorObj_obj, eqToHom_map, eqToHom_app] at this
  set f : ((shiftMonoidalFunctor C A).obj (MonoidalCategory.tensorObj { as := i' }
    { as := j' })).obj X ⟶ ((shiftMonoidalFunctor C A).obj
    (MonoidalCategory.tensorObj { as := i' } { as := j })).obj X := eqToHom (by rw [hj])
  rw [← cancel_mono f] at this
  simp only [assoc, eqToHom_trans, eqToHom_refl, comp_id, f] at this
  rw [← this]
  simp

lemma shiftFunctorAdd_eqToIso (i j i' j' : A) (hi : i = i') (hj : j = j') :
    shiftFunctorAdd C i j = eqToIso (by rw [hi, hj]) ≪≫
    shiftFunctorAdd C i' j' ≪≫ eqToIso (by rw [hi, hj]) := by
  conv_lhs => rw [← Iso.symm_symm_eq (shiftFunctorAdd C i j),
                shiftFunctorAdd_symm_eqToIso i j i' j' hi hj]
  ext X
  simp

lemma shiftFunctorAdd'_symm_eqToIso (i j k i' j' k' : A) (h : i + j = k) (h' : i' + j' = k')
    (hi : i = i') (hj : j = j') :
    (shiftFunctorAdd' C i j k h).symm = eqToIso (by rw [hi, hj]) ≪≫
    (shiftFunctorAdd' C i' j' k' h').symm ≪≫ eqToIso (by rw [← h, ← h', hi, hj])
    := by
  dsimp [shiftFunctorAdd']
  rw [shiftFunctorAdd_symm_eqToIso i j i' j' hi hj]
  ext X
  simp only [Functor.comp_obj, Iso.trans_assoc, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv, eqToHom_trans, NatTrans.comp_app, eqToHom_app]

lemma shiftFunctorAdd'_eqToIso (i j k i' j' k' : A) (h : i + j = k) (h' : i' + j' = k')
    (hi : i = i') (hj : j = j') :
    shiftFunctorAdd' C i j k h = eqToIso (by rw [← h, ← h', hi, hj]) ≪≫
    shiftFunctorAdd' C i' j' k' h' ≪≫ eqToIso (by rw [hi, hj]) := by
  dsimp [shiftFunctorAdd']
  rw [shiftFunctorAdd_eqToIso i j i' j' hi hj]
  ext X
  simp only [Functor.comp_obj, Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc, NatTrans.comp_app,
    eqToHom_app, Iso.trans_assoc]

variable (C)

/-- Here be other doc string.-/
lemma shiftFunctorAdd'_add_zero' (a b : A) (hb : b = 0) (h : a + b = a) :
    shiftFunctorAdd' C a b a h = (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (shiftFunctor C a) (shiftFunctorZero' C b hb).symm := by
  rw [shiftFunctorAdd'_eqToIso a b a a 0 a (by simp [hb]) (by simp) rfl hb,
    shiftFunctorAdd'_add_zero]
  ext
  dsimp
  simp [shiftFunctorZero']

/-- Fake doc string again.-/
lemma shiftFunctorAdd'_zero_add' (a b : A) (ha : a = 0) (h : a + b = b) :
    shiftFunctorAdd' C a b b h = (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (shiftFunctorZero' C a ha).symm (shiftFunctor C b) := by
  rw [shiftFunctorAdd'_eqToIso a b b 0 b b (by simp [ha]) (by simp) ha rfl,
    shiftFunctorAdd'_zero_add]
  ext
  dsimp
  simp [shiftFunctorZero', eqToHom_map]

end Shift
-/

/-
section Shift

variable {C : Type u} {A : Type*} [CategoryTheory.Category.{v, u} C] [AddGroup A]
  [CategoryTheory.HasShift C A]

attribute [local instance] endofunctorMonoidalCategory

open Category Opposite

variable (C)

-- leav for now
lemma shiftEquiv'_unit (a a' : A) (h : a + a' = 0) :
    (shiftEquiv' C a a' h).unit = (shiftFunctorCompIsoId C a a' h).inv := by
  ext _
  change (shiftEquiv' C a a' h).unitIso.hom.app _ = _
  rw [shiftEquiv'_unitIso]
  rfl

lemma shiftEquiv'_counit (a a' : A) (h : a + a' = 0) :
    (shiftEquiv' C a a' h).counit = (shiftFunctorCompIsoId C a' a
    (by simp only [eq_neg_of_add_eq_zero_left h, add_neg_cancel])).hom := by
  ext _
  change (shiftEquiv' C a a' h).counitIso.hom.app _ = _
  rw [shiftEquiv'_counitIso]

lemma shiftEquiv'_symm_unit (a a' : A) (h : a + a' = 0) :
    (shiftEquiv' C a a' h).symm.unit = (shiftFunctorCompIsoId C a' a
    (by simp [eq_neg_of_add_eq_zero_left h])).inv := by
  ext _
  change (shiftEquiv' C a a' h).counitIso.inv.app _ = _
  rw [shiftEquiv'_counitIso]

lemma shiftEquiv'_symm_counit (a a' : A) (h : a + a' = 0) :
    (shiftEquiv' C a a' h).symm.counit = (shiftFunctorCompIsoId C a a' h).hom := by
  ext _
  change (shiftEquiv' C a a' h).unitIso.inv.app _ = _
  rw [shiftEquiv'_unitIso]
  rfl

-- leave for now
lemma shiftEquiv_homEquiv_zero'_app (a : A) (ha : a = 0) (X Y : C) (u : X⟦-a⟧ ⟶ Y) :
    (shiftEquiv C a).symm.toAdjunction.homEquiv X Y u =
    (shiftFunctorZero' C (-a) (by simp [ha])).inv.app X ≫ u ≫
    (shiftFunctorZero' C a ha).inv.app Y := by
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, Equivalence.symm_functor,
    shiftEquiv'_inverse, Adjunction.homEquiv_apply, Functor.comp_obj, Equivalence.toAdjunction_unit,
    Functor.id_obj]
  have : (shiftEquiv C a).symm.unit.app X = (shiftFunctorZero' C (-a) (by simp [ha])).inv.app X ≫
      (shiftFunctorZero' C a ha).inv.app (X⟦-a⟧) := by
    change (shiftEquiv C a).symm.unitIso.hom.app X = _
    rw [Equivalence.symm_unitIso]
    simp only [Functor.id_obj, Equivalence.symm_functor, shiftEquiv'_inverse,
      Equivalence.symm_inverse, shiftEquiv'_functor, Functor.comp_obj, shiftEquiv'_counitIso,
      Iso.symm_hom]
    rw [shiftFunctorCompIsoId]
    rw [shiftFunctorAdd'_eqToIso (-a) a 0 (-a) 0 (-a) (by simp) (by simp) rfl ha]
    rw [shiftFunctorAdd'_add_zero, shiftFunctorZero', shiftFunctorZero']
    simp
  rw [this, assoc, ← (shiftFunctorZero' C a ha).inv.naturality u]
  simp

/-- Doc string doc string.-/
lemma shiftEquiv_homEquiv_zero' (a : A) (ha : a = 0) (X Y : C) :
    (shiftEquiv C a).symm.toAdjunction.homEquiv X Y =
    ((yoneda.obj Y).mapIso ((shiftFunctorZero' C (-a) (by simp [ha])).symm.app X).op ≪≫
    (coyoneda.obj (op X)).mapIso ((shiftFunctorZero' C a ha).symm.app Y)).toEquiv := by
  ext u
  rw [shiftEquiv_homEquiv_zero'_app C a ha]
  simp

lemma shiftEquiv_homEquiv_zero (X Y : C) :
    (shiftEquiv C (0 : A)).symm.toAdjunction.homEquiv X Y =
    ((yoneda.obj Y).mapIso ((shiftFunctorZero' C (-0 : A) (by simp)).symm.app X).op ≪≫
    (coyoneda.obj (op X)).mapIso ((shiftFunctorZero C A).symm.app Y)).toEquiv := by
  rw [shiftEquiv_homEquiv_zero' C (0 : A) rfl]
  simp [shiftFunctorZero']

lemma shiftEquiv_homEquiv_zero'_symm_app (a : A) (ha : a = 0) (X Y : C) (u : X ⟶ Y⟦a⟧) :
    ((shiftEquiv C a).symm.toAdjunction.homEquiv X Y).symm u =
    (shiftFunctorZero' C (-a) (by simp [ha])).hom.app X ≫ u ≫
    (shiftFunctorZero' C a ha).hom.app Y := by
  rw [shiftEquiv_homEquiv_zero' C a ha]
  simp

-- ok for now
lemma shiftEquiv'_add_symm_homEquiv (a a' b b' c c' : A) (ha : a + a' = 0) (hb : b + b' = 0)
    (hc : c + c' = 0) (h : a + b = c) (X Y : C) (u : (X⟦b'⟧)⟦a'⟧ ⟶ Y) :
    ((shiftEquiv' C b b' hb).symm.toAdjunction.homEquiv X ((shiftFunctor C a).obj Y))
      (((shiftEquiv' C a a' ha).symm.toAdjunction.homEquiv
      ((shiftFunctor C (b')).obj X) Y) u) ≫
      (shiftFunctorAdd' C a b c h).inv.app Y =
      ((shiftEquiv' C c c' hc).symm.toAdjunction.homEquiv X Y)
      ((shiftFunctorAdd' C b' a' c' (by rw [eq_neg_of_add_eq_zero_right hc,
        eq_neg_of_add_eq_zero_right ha, eq_neg_of_add_eq_zero_right hb, ← h,
        neg_add_rev])).hom.app X ≫ u) := by
  have he : ∀ (a a' : A) (ha : a + a' = 0) (X : C), (shiftEquiv' C a a' ha).symm.unit.app X =
      (shiftFunctorZero C A).inv.app X ≫ (shiftFunctorAdd' C a' a 0
      (by rw [eq_neg_of_add_eq_zero_left ha, add_neg_cancel])).hom.app X := by
    intro a a' ha X
    change (shiftEquiv' C a a' ha).symm.unitIso.hom.app X = _
    rw [Equivalence.symm_unitIso]
    simp [shiftFunctorCompIsoId]
  simp only [Equivalence.symm_inverse, shiftEquiv'_functor, Equivalence.symm_functor,
    shiftEquiv'_inverse, Adjunction.homEquiv_apply, Functor.comp_obj, Equivalence.toAdjunction_unit,
    Functor.map_comp, assoc]
  rw [he b b' hb, he c c' hc, he a a' ha]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, assoc]
  have heq : u⟦c⟧' = (shiftFunctorAdd' C a b c h).hom.app ((X⟦b'⟧)⟦a'⟧) ≫ (u⟦a⟧')⟦b⟧' ≫
      (shiftFunctorAdd' C a b c h).inv.app Y := by
    conv_rhs => rw [← assoc]; erw [← (shiftFunctorAdd' C a b c h).hom.naturality u]
                rw [assoc, Iso.hom_inv_id_app, comp_id]
  rw [heq]
  slice_rhs 2 3 => rw [shiftFunctorAdd'_assoc_hom_app b' a' c c' b 0
        (by rw [eq_neg_of_add_eq_zero_right hc,
        eq_neg_of_add_eq_zero_right ha, eq_neg_of_add_eq_zero_right hb, ← h,
        neg_add_rev]) (by rw [eq_neg_of_add_eq_zero_right ha, ← h]; simp)
        (by rw [eq_neg_of_add_eq_zero_right ha, eq_neg_of_add_eq_zero_right hb, ← h, add_assoc,
        ← add_assoc (-a)]; simp) X]
  slice_rhs 3 4 => rw [← shiftFunctorAdd'_assoc_hom_app a' a b 0 c b
    (by rw [eq_neg_of_add_eq_zero_right ha]; simp) h (by rw [eq_neg_of_add_eq_zero_right ha]; simp)
    (X⟦b'⟧)]
  rw [shiftFunctorAdd'_zero_add]
  simp

-- ok for now
lemma shiftEquiv_add_symm_homEquiv (a a' b b' c c' : A) (ha : a + a' = 0) (hb : b + b' = 0)
    (hc : c + c' = 0) (h : a + b = c) (X Y : C) (u : X ⟶ Y⟦c⟧) :
        ((shiftEquiv' C a a' ha).symm.toAdjunction.homEquiv (X⟦b'⟧) Y).symm
        (((shiftEquiv' C b b' hb).symm.toAdjunction.homEquiv X
        ((shiftFunctor C a).obj Y)).symm (u ≫ (shiftFunctorAdd' C a b c h).hom.app Y)) =
        ((shiftFunctorAdd' C b' a' c' (by rw [eq_neg_of_add_eq_zero_right hc,
        eq_neg_of_add_eq_zero_right ha, eq_neg_of_add_eq_zero_right hb, ← h,
        neg_add_rev])).inv.app X ≫
        ((shiftEquiv' C c c' hc).symm.toAdjunction.homEquiv X Y).symm u) := by
  have := shiftEquiv'_add_symm_homEquiv C a a' b b' c c' ha hb hc h X Y
    ((shiftFunctorAdd' C b' a' c' (by rw [eq_neg_of_add_eq_zero_right hc,
        eq_neg_of_add_eq_zero_right ha, eq_neg_of_add_eq_zero_right hb, ← h,
        neg_add_rev])).inv.app X ≫
    ((shiftEquiv' C c c' hc).symm.toAdjunction.homEquiv X Y).symm u)
  rw [← cancel_mono ((shiftFunctorAdd' C a b c h).hom.app Y), assoc, Iso.inv_hom_id_app] at this
  conv_lhs at this => erw [comp_id]
  apply_fun (fun x ↦ ((shiftEquiv' C b b' hb).symm.toAdjunction.homEquiv X
        ((shiftFunctor C a).obj Y)).symm x) at this
  erw [Equiv.apply_symm_apply] at this
  sorry
/-  erw [this]
  congr 1
  conv_rhs => rw [← assoc, Iso.hom_inv_id_app]; erw [id_comp]
              rw [Equiv.apply_symm_apply]-/

end Shift
-/

/-
namespace Adjunction

open Opposite

universe u' v' u'' v''

variable {C : Type u} {D : Type u'} {E : Type u''} [Category.{v,u} C] [Category.{v',u'} D]
  [Category.{v'', u''} E] (F F' : C ⥤ D) (G G' : D ⥤ C) (adj : F ⊣ G) (adj' : F' ⊣ G')
  (H : D ⥤ E) (K : E ⥤ D) (adj₁ : H ⊣ K)

@[simp]
def Functor_iso_to_iso_op : (F ≅ F') ≃ (F'.op ≅ F.op) :=
  Equiv.mk NatIso.op NatIso.removeOp (fun _ ↦ by aesop) (fun _ ↦ by aesop)

lemma natIsoEquiv_compat_op : (Functor_iso_to_iso_op G G').trans
    ((conjugateIsoEquiv adj.op adj'.op).trans
    (Functor_iso_to_iso_op F' F).symm) = (conjugateIsoEquiv adj adj').symm := by
  ext
  simp only [Functor_iso_to_iso_op, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    NatIso.removeOp_hom, conjugateIsoEquiv_apply_hom, NatIso.op_hom, NatTrans.removeOp_app,
    Functor.op_obj, conjugateEquiv_apply_app, op_unit, NatTrans.op_app, Functor.comp_obj,
    Functor.id_obj, Functor.op_map, Quiver.Hom.unop_op, op_counit, unop_comp, Category.assoc,
    conjugateIsoEquiv_symm_apply_hom, conjugateEquiv_symm_apply_app]

variable (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

lemma shiftEquiv'_symm_toAdjunction_op (a b : A) (h : a + b = 0) :
    (shiftEquiv' C a b h).symm.toAdjunction.op =
    (shiftEquiv' (OppositeShift C A) b a
    (by rw [eq_neg_of_add_eq_zero_left h]; simp)).symm.toAdjunction := by
  ext
  · simp only [Functor.id_obj, Equivalence.symm_inverse, shiftEquiv'_functor,
    Equivalence.symm_functor, shiftEquiv'_inverse, Functor.comp_obj, Functor.op_obj, op_unit,
    Equivalence.toAdjunction_counit, NatTrans.op_app, id_eq, eq_mpr_eq_cast,
    Equivalence.toAdjunction_unit]
    rw [shiftEquiv'_symm_unit, shiftEquiv'_symm_counit]
    simp only [unop_id, Functor.map_id, shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Category.id_comp, op_comp, op_unop,
      Iso.trans_inv, Iso.symm_inv, Functor.op_obj]
    rw [oppositeShiftFunctorAdd'_hom_app, oppositeShiftFunctorZero_inv_app]

lemma shiftEquiv_symm_toAdjunction_op (a : A) :
    (shiftEquiv C a).symm.toAdjunction.op =
    (shiftEquiv' (OppositeShift C A) (-a) a (by simp)).symm.toAdjunction := by
  rw [shiftEquiv'_symm_toAdjunction_op]

lemma comp_op : (Adjunction.comp adj adj₁).op =
    Adjunction.comp adj₁.op adj.op := by aesop

end Adjunction
-/

section

variable {C : Type u} [Category.{v,u} C]

lemma IsIso.comp_left_bijective {X Y Z : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (fun (g : Y ⟶ Z) ↦ f ≫ g) := by
  constructor
  · exact Epi.left_cancellation
  · intro g; existsi inv f ≫ g; simp only [hom_inv_id_assoc]

lemma IsIso.comp_right_bijective {X Y Z : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (fun (g : Z ⟶ X) ↦ g ≫ f) := by
  constructor
  · exact Mono.right_cancellation
  · intro g; existsi g ≫ inv f; simp only [Category.assoc, inv_hom_id, Category.comp_id]

end

open Limits Category Functor Pretriangulated

namespace Triangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

abbrev IsTriangleMorphism (T T' : Triangle C) (u : T.obj₁ ⟶ T'.obj₁) (v : T.obj₂ ⟶ T'.obj₂)
    (w : T.obj₃ ⟶ T'.obj₃) :=
  (T.mor₁ ≫ v = u ≫ T'.mor₁) ∧ (T.mor₂ ≫ w = v ≫ T'.mor₂) ∧
  (T.mor₃ ≫ (shiftFunctor C 1).map u = w ≫ T'.mor₃)

/-- Doc string, why the "'"?
-/
lemma NineGrid' {T_X T_Y : Triangle C} (dT_X : T_X ∈ distinguishedTriangles)
    (dT_Y : T_Y ∈ distinguishedTriangles) (u₁ : T_X.obj₁ ⟶ T_Y.obj₁) (u₂ : T_X.obj₂ ⟶ T_Y.obj₂)
    (comm : T_X.mor₁ ≫ u₂ = u₁ ≫ T_Y.mor₁) {Z₂ : C} (v₂ : T_Y.obj₂ ⟶ Z₂) (w₂ : Z₂ ⟶ T_X.obj₂⟦1⟧)
    (dT₂ : Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles) :
    ∃ (Z₁ Z₃ : C) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦1⟧) (v₁ : T_Y.obj₁ ⟶ Z₁)
    (w₁ : Z₁ ⟶ T_X.obj₁⟦1⟧) (u₃ : T_X.obj₃ ⟶ T_Y.obj₃) (v₃ : T_Y.obj₃ ⟶ Z₃)
    (w₃ : Z₃ ⟶ T_X.obj₃⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism T_X T_Y u₁ u₂ u₃ ∧
    IsTriangleMorphism T_Y (Triangle.mk f g h) v₁ v₂ v₃ ∧
    w₁ ≫ T_X.mor₁⟦1⟧' = f ≫ w₂ ∧ w₂ ≫ T_X.mor₂⟦1⟧' = g ≫ w₃ ∧
    w₃ ≫ T_X.mor₃⟦1⟧' = - h ≫ w₁⟦1⟧' := by
  obtain ⟨Z₁, v₁, w₁, dT₁⟩ := distinguished_cocone_triangle u₁
  obtain ⟨A, a, b, dTdiag⟩ := distinguished_cocone_triangle (T_X.mor₁ ≫ u₂)
  set oct₁ := someOctahedron (u₁₂ := T_X.mor₁) (u₂₃ := u₂) (u₁₃ := T_X.mor₁ ≫ u₂) rfl dT_X
    dT₂ dTdiag
  set oct₂ := someOctahedron (u₁₂ := u₁) (u₂₃ := T_Y.mor₁) (u₁₃ := T_X.mor₁ ≫ u₂)
    comm.symm dT₁ dT_Y dTdiag
  obtain ⟨Z₃, g, h, dT_Z⟩ := distinguished_cocone_triangle (oct₂.m₁ ≫ oct₁.m₃)
  set oct₃ := someOctahedron (u₁₂ := oct₂.m₁) (u₂₃ := oct₁.m₃) (u₁₃ := oct₂.m₁ ≫ oct₁.m₃) rfl
    oct₂.mem ((rotate_distinguished_triangle _).mp oct₁.mem) dT_Z
  existsi Z₁, Z₃, (oct₂.m₁ ≫ oct₁.m₃), g, h, v₁, w₁, oct₁.m₁ ≫ oct₂.m₃, oct₃.m₁, oct₃.m₃
  constructor
  · exact dT_Z
  · constructor
    · exact dT₁
    · constructor
      · have := inv_rot_of_distTriang _ oct₃.mem
        refine isomorphic_distinguished _ this _ (Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_)
        · have := (shiftFunctorCompIsoId C 1 (-1)
              (by simp only [Int.reduceNeg, add_neg_cancel])).app T_X.obj₃
          simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj] at this
          exact this.symm
        · exact Iso.refl _
        · exact Iso.refl _
        · simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Triangle.invRotate_obj₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₁, Int.reduceNeg,
          Triangle.mk_obj₃, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_mor₁,
          Preadditive.neg_comp, Functor.map_neg, Functor.map_comp, assoc, neg_neg]
          rw [← cancel_epi ((shiftFunctorCompIsoId C 1 (-1) (by simp)).hom.app T_X.obj₃)]
          rw [← cancel_mono ((shiftFunctorCompIsoId C 1 (-1) (by simp)).inv.app T_Y.obj₃)]
          rw [assoc]; conv_lhs => erw [← shift_shift_neg']
          simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc,
            assoc, Iso.hom_inv_id_app, comp_id]
          simp only [Int.reduceNeg, Functor.map_comp]
        · simp only [Triangle.mk_obj₂, Triangle.invRotate_obj₃, Triangle.mk_obj₃,
          Triangle.mk_mor₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₂, Triangle.mk_obj₁,
          Triangle.invRotate_mor₂, Triangle.mk_mor₁, id_comp]
        · simp only [Triangle.mk_obj₃, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₁,
           Triangle.mk_mor₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_obj₃,
           Triangle.mk_obj₂, Iso.refl_hom, Triangle.invRotate_mor₃, Triangle.mk_mor₂, id_comp]
          rw [shift_shiftFunctorCompIsoId_inv_app]
      · constructor
        · constructor
          · exact comm
          · constructor
            · rw [← assoc, oct₁.comm₁, assoc, oct₂.comm₃]
            · conv_rhs => rw [assoc, ← oct₂.comm₄, ← assoc, oct₁.comm₂]
        · constructor
          · constructor
            · simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₁]
              conv_rhs => rw [← assoc, oct₂.comm₁, assoc, oct₁.comm₃]
            · constructor
              · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
                Triangle.mk_mor₁, Triangle.mk_mor₂]
                conv_lhs => congr; rw [← oct₂.comm₃]
                rw [assoc, oct₃.comm₁, ← assoc, oct₁.comm₃]
              · exact oct₃.comm₂.symm
          · constructor
            · simp only [Triangle.mk_obj₁, Triangle.shiftFunctor_obj, Int.negOnePow_one,
              Functor.comp_obj, Triangle.mk_obj₂, Triangle.mk_mor₁, assoc, Units.neg_smul, one_smul,
              Preadditive.comp_neg]
              rw [← oct₁.comm₄, ← assoc, oct₂.comm₂]
            · constructor
              · rw [oct₃.comm₃]; simp only [Triangle.mk_mor₃]
              · conv_rhs => congr; rw [← oct₂.comm₂]
                simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
                  Functor.map_comp]
                conv_lhs => congr; rfl; rw [← oct₁.comm₂]
                have := oct₃.comm₄
                simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
                  Preadditive.comp_neg] at this
                rw [← assoc, this]
                simp only [Functor.map_comp, Preadditive.neg_comp, assoc, neg_neg]

/-- Proposition 1.1.11 of of [BBD].
-/
lemma NineGrid {X₁ X₂ Y₁ Y₂ : C} (u₁ : X₁ ⟶ Y₁) (u₂ : X₂ ⟶ Y₂) (f_X : X₁ ⟶ X₂) (f_Y : Y₁ ⟶ Y₂)
    (comm : f_X ≫ u₂ = u₁ ≫ f_Y) :
    ∃ (X₃ Y₃ Z₁ Z₂ Z₃ : C) (g_X : X₂ ⟶ X₃) (h_X : X₃ ⟶ X₁⟦1⟧) (g_Y : Y₂ ⟶ Y₃)
    (h_Y : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦(1 : ℤ)⟧) (u₃ : X₃ ⟶ Y₃)
    (v₁ : Y₁ ⟶ Z₁) (v₂ : Y₂ ⟶ Z₂) (v₃ : Y₃ ⟶ Z₃) (w₁ : Z₁ ⟶ X₁⟦(1 : ℤ)⟧) (w₂ : Z₂ ⟶ X₂⟦(1 : ℤ)⟧)
    (w₃ : Z₃ ⟶ X₃⟦(1 : ℤ)⟧),
    Triangle.mk f_X g_X h_X ∈ distinguishedTriangles ∧
    Triangle.mk f_Y g_Y h_Y ∈ distinguishedTriangles ∧
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism (Triangle.mk f_X g_X h_X) (Triangle.mk f_Y g_Y h_Y) u₁ u₂ u₃ ∧
    IsTriangleMorphism (Triangle.mk f_Y g_Y h_Y) (Triangle.mk f g h) v₁ v₂ v₃ ∧
    w₁ ≫ f_X⟦1⟧' = f ≫ w₂ ∧ w₂ ≫ g_X⟦1⟧' = g ≫ w₃ ∧ w₃ ≫ h_X⟦1⟧' = - h ≫ w₁⟦1⟧' := by
  obtain ⟨X₃, g_X, h_X, dT_X⟩ := Pretriangulated.distinguished_cocone_triangle f_X
  obtain ⟨Y₃, g_Y, h_Y, dT_Y⟩ := Pretriangulated.distinguished_cocone_triangle f_Y
  obtain ⟨Z₂, v₂, w₂, dT₂⟩ := Pretriangulated.distinguished_cocone_triangle u₂
  obtain ⟨Z₁, Z₃, f, g, h, v₁, w₁, u₃, v₃, w₃, dT_Z, dT₁, dT₃, comm_XY, comm_YZ, comm₁, comm₂,
    comm₃⟩ := NineGrid' dT_X dT_Y u₁ u₂ comm v₂ w₂ dT₂
  existsi X₃, Y₃, Z₁, Z₂, Z₃, g_X, h_X, g_Y, h_Y, f, g, h, u₃, v₁, v₂, v₃, w₁, w₂, w₃
  exact ⟨dT_X, dT_Y, dT_Z, dT₁, dT₂, dT₃, comm_XY, comm_YZ, comm₁, comm₂, comm₃⟩

end Triangulated

namespace Pretriangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable instance : (Triangle.π₁ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₁_obj,
      Triangle.mk_obj₁, Functor.comp_map, Triangle.π₁_map, Triangle.shiftFunctor_map_hom₁,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₁_obj,
      Triangle.mk_obj₁, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₁_map, Triangle.shiftFunctorAdd'_hom_app_hom₁, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₁_commShiftIso_app (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₁_commShiftIso_hom_app (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₁_commShiftIso_inv_app (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).inv.app T = 𝟙 _ := rfl

noncomputable instance : (Triangle.π₂ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₂_obj,
      Triangle.mk_obj₂, Functor.comp_map, Triangle.π₂_map, Triangle.shiftFunctor_map_hom₂,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₂_obj,
      Triangle.mk_obj₂, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₂_map, Triangle.shiftFunctorAdd'_hom_app_hom₂, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₂_commShiftIso (a : ℤ) (T : Triangle C) :
    ((Triangle.π₂ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₂_commShiftIso_hom (a : ℤ) (T : Triangle C) :
    ((Triangle.π₂ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

noncomputable instance : (Triangle.π₃ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₃_obj,
      Triangle.mk_obj₃, Functor.comp_map, Triangle.π₃_map, Triangle.shiftFunctor_map_hom₃,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₃_obj,
      Triangle.mk_obj₃, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₃_map, Triangle.shiftFunctorAdd'_hom_app_hom₃, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₃_commShiftIso (a : ℤ) (T : Triangle C) :
    ((Triangle.π₃ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₃_commShiftIso_hom (a : ℤ) (T : Triangle C) :
    ((Triangle.π₃ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

end Pretriangulated

namespace Pretriangulated.TriangleMorphism

variable {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

@[simp]
theorem smul_iso_hom {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ≅ T₂) (n : ℤˣ) :
    (n • f).hom = n.1 • f.hom := by rw [Preadditive.smul_iso_hom]; rfl

@[simp]
theorem smul_hom₁ {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ⟶ T₂) (n : ℤ) :
    (n • f).hom₁ = n • f.hom₁ := by simp only [instSMulHomTriangle_smul_hom₁]

@[simp]
theorem smul_hom₂ {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ⟶ T₂) (n : ℤ) :
    (n • f).hom₂ = n • f.hom₂ := by simp only [instSMulHomTriangle_smul_hom₂]

@[simp]
theorem smul_hom₃ {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ⟶ T₂) (n : ℤ) :
    (n • f).hom₃ = n • f.hom₃ := by simp only [instSMulHomTriangle_smul_hom₃]

end Pretriangulated.TriangleMorphism

end CategoryTheory
