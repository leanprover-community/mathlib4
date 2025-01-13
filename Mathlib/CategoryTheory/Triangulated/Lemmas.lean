import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Opposites

universe u v

namespace CategoryTheory

section LimitOnZ

open Limits Category

variable {C : Type u} [CategoryTheory.Category.{v, u} C] (F F' : ℤ ⥤ C)

lemma HasLimit_of_transition_iso {a : ℤ} (G : Set.Iic a ⥤ C) (hG : ∀ (b c : Set.Iic a)
    (u : b ⟶ c), IsIso (G.map u)) : HasLimit G := by
  refine HasLimit.mk {cone := ?_, isLimit := ?_}
  · refine {pt := G.obj ⟨a, by simp only [Set.mem_Iic, le_refl]⟩, π := ?_}
    refine {app := ?_, naturality := ?_}
    · intro b
      simp only [Functor.const_obj_obj]
      have := hG b ⟨a, by simp only [Set.mem_Iic, le_refl]⟩ (homOfLE (Set.mem_Iic.mp b.2))
      exact inv (G.map (homOfLE (Set.mem_Iic.mp b.2)))
    · intro b c u
      simp only [Functor.const_obj_obj, Functor.const_obj_map, id_eq, Category.id_comp,
        IsIso.eq_inv_comp, IsIso.comp_inv_eq]
      rw [← Functor.map_comp]
      congr 1
  · exact {lift := fun s ↦ s.π.app ⟨a, by simp only [Set.mem_Iic, le_refl]⟩,
           fac := by simp, uniq := by simp}

abbrev Inclusion_Iic (a : ℤ) : Set.Iic a ⥤ ℤ :=
  Monotone.functor (f := fun b ↦ b.1) (fun _ _ h ↦ h)

lemma Initial_inclusion_Iic (a : ℤ) : Functor.Initial (Inclusion_Iic a) := by
  have : (Inclusion_Iic a).Full :=
      {map_surjective := fun u ↦ by existsi homOfLE (Subtype.mk_le_mk.mpr (leOfHom u)); rfl}
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro d
  existsi ⟨min a d, by simp only [Set.mem_Iic, min_le_iff, le_refl, true_or]⟩
  exact Nonempty.intro (homOfLE (min_le_right a d))

lemma HasLimit_inclusion_of_transition_eventually_iso {a : ℤ}
    (hF : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), IsIso (F.map u)) :
    HasLimit (Inclusion_Iic a ⋙ F) := by
  apply HasLimit_of_transition_iso
  intro b c u
  simp only [Functor.comp_obj, Functor.comp_map]
  exact hF b c u

lemma HasLimit_of_transition_eventually_iso {a : ℤ} (hF : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1),
    IsIso (F.map u)) : HasLimit F := by
  have : (Inclusion_Iic a).Initial := Initial_inclusion_Iic a
  have : HasLimit (Inclusion_Iic a ⋙ F) := HasLimit_inclusion_of_transition_eventually_iso F hF
  exact Functor.Initial.hasLimit_of_comp (Inclusion_Iic a)

noncomputable def Hom_of_almost_NatTrans_aux [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) (a : ℤ)
    (nat : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u) :
    Limits.limit F ⟶ Limits.limit F' := by
  have := Initial_inclusion_Iic a
  refine (Functor.Initial.limitIso (Inclusion_Iic a) F).inv ≫ ?_ ≫
    (Functor.Initial.limitIso (Inclusion_Iic a) F').hom
  exact limMap {app := fun b ↦ α b.1, naturality := nat}

lemma Hom_of_almost_NatTrans_aux_ext [HasLimit F] [HasLimit F']
    (α α' : (n : ℤ) → (F.obj n ⟶ F'.obj n)) (a : ℤ)
    (nat : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u)
    (comp : ∀ (b : Set.Iic a), α b.1 = α' b.1) :
    Hom_of_almost_NatTrans_aux F F' α a nat = Hom_of_almost_NatTrans_aux F F' α' a
    (fun b c u ↦ by rw [← comp b, ← comp c]; exact nat b c u) := by
  simp only [Hom_of_almost_NatTrans_aux, Iso.cancel_iso_hom_right_assoc, Iso.cancel_iso_inv_left]
  congr 1
  ext b
  simp only [Functor.comp_obj, Monotone.functor_obj, comp b]

lemma Hom_of_almost_NatTrans_aux_indep_bound [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) {a₁ a₂ : ℤ} (h : a₁ ≤ a₂)
    (nat : ∀ (b c : Set.Iic a₂) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u) :
    Hom_of_almost_NatTrans_aux F F' α a₁
    (fun b c u ↦ nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) h⟩
                 ⟨c.1, le_trans (Set.mem_Iic.mp c.2) h⟩ u) =
    Hom_of_almost_NatTrans_aux F F' α a₂ nat := by
  have := Initial_inclusion_Iic a₁
  have := Initial_inclusion_Iic a₂
  set e₂ := Functor.Initial.limitIso (Inclusion_Iic a₂) F
  set e'₂ := Functor.Initial.limitIso (Inclusion_Iic a₂) F'
  set e₁ := Functor.Initial.limitIso (Inclusion_Iic a₁) F
  set e'₁ := Functor.Initial.limitIso (Inclusion_Iic a₁) F'
  set f₂ : limit (Inclusion_Iic a₂ ⋙ F) ⟶ limit (Inclusion_Iic a₂ ⋙ F') :=
    limMap {app := fun b ↦ α b.1, naturality := nat}
  set f₁ : limit (Inclusion_Iic a₁ ⋙ F) ⟶ limit (Inclusion_Iic a₁ ⋙ F') :=
    limMap {app := fun b ↦ α b.1, naturality :=
    fun b c u ↦ nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) h⟩
                ⟨c.1, le_trans (Set.mem_Iic.mp c.2) h⟩ u}
  change e₁.inv ≫ f₁ ≫ e'₁.hom = e₂.inv ≫ f₂ ≫ e'₂.hom
  set I : Set.Iic a₁ ⥤ Set.Iic a₂ := Monotone.functor
    (f := fun b ↦ ⟨b.1, le_trans (Set.mem_Iic.mp b.2) h⟩) (fun _ _ h ↦ h)
  have : Functor.Initial I := by
    have : I.Full :=
      {map_surjective := fun u ↦ by existsi homOfLE (Subtype.mk_le_mk.mpr (leOfHom u)); rfl}
    apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    intro d
    existsi ⟨min a₁ d, by simp only [Set.mem_Iic, min_le_iff, le_refl, true_or]⟩
    exact Nonempty.intro (homOfLE (min_le_right a₁ d))
  set ι : Inclusion_Iic a₁ ⋙ F ≅ I ⋙ Inclusion_Iic a₂ ⋙ F :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp [Inclusion_Iic, Monotone.functor, I])
  set ι' : Inclusion_Iic a₁ ⋙ F' ≅ I ⋙ Inclusion_Iic a₂ ⋙ F' :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp [Inclusion_Iic, Monotone.functor, I])
  have heq : e₂ = (Functor.Initial.limitIso I (Inclusion_Iic a₂ ⋙ F)).symm ≪≫
      (HasLimit.isoOfNatIso ι).symm ≪≫ e₁ := by
    apply Iso.ext
    rw [← cancel_mono e₁.inv, ← cancel_epi e₂.inv]
    ext a
    simp only [Functor.comp_obj, Monotone.functor_obj, Iso.inv_hom_id_assoc, Iso.trans_hom,
      Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id, HasLimit.isoOfNatIso_inv_π,
      NatIso.ofComponents_inv_app, Iso.refl_inv, ι]
    erw [comp_id, limit.pre_π, limit.pre_π, limit.pre_π]
    rfl
  have heq' : e'₂ = (Functor.Initial.limitIso I (Inclusion_Iic a₂ ⋙ F')).symm ≪≫
      (HasLimit.isoOfNatIso ι').symm ≪≫ e'₁ := by
    apply Iso.ext
    rw [← cancel_mono e'₁.inv, ← cancel_epi e'₂.inv]
    ext a
    simp only [Functor.comp_obj, Monotone.functor_obj, Iso.inv_hom_id_assoc, Iso.trans_hom,
      Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id, HasLimit.isoOfNatIso_inv_π,
      NatIso.ofComponents_inv_app, Iso.refl_inv, ι']
    erw [comp_id, limit.pre_π, limit.pre_π, limit.pre_π]
    rfl
  rw [heq, heq']
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    Iso.cancel_iso_inv_left]
  rw [← assoc, ← assoc, ← assoc, ← assoc]; congr 1
  apply limit.hom_ext
  intro a
  simp only [Functor.comp_obj, Monotone.functor_obj, Category.assoc, HasLimit.isoOfNatIso_inv_π,
    NatIso.ofComponents_inv_app, Iso.refl_inv, ι, ι']
  erw [comp_id, limit.pre_π, limMap_π, limMap_π]
  simp only [Functor.comp_obj, Monotone.functor_obj]
  have h : α a.1 = α (I.obj a).1 := by simp [I]
  rw [← h]; rw [← assoc, ← assoc]; congr 1
  rw [← cancel_epi (HasLimit.isoOfNatIso ι).inv]
  rw [← assoc, ← assoc]; erw [Iso.inv_hom_id]; rw [id_comp]
  rw [← cancel_epi (Functor.Initial.limitIso I (Inclusion_Iic a₂ ⋙ F)).inv]
  conv_rhs => rw [← assoc, Iso.inv_hom_id, id_comp]
  simp only [Functor.comp_obj, Monotone.functor_obj, HasLimit.isoOfNatIso_inv_π]
  erw [← assoc, limit.pre_π]
  simp only [Functor.comp_obj, Monotone.functor_obj, NatIso.ofComponents_inv_app, Iso.refl_inv, ι]
  erw [comp_id]

lemma Hom_of_almost_NatTrans_aux_indep_map [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n))
    (α' : (n : ℤ) → (F.obj n ⟶ F'.obj n)) {a a' : ℤ}
    (nat : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u)
    (nat' : ∀ (b c : Set.Iic a') (u : b.1 ⟶ c.1), F.map u ≫ α' c.1 = α' b.1 ≫ F'.map u)
    (comp : ∃ a'', ∀ (b : Set.Iic a''), α b.1 = α' b.1) :
    Hom_of_almost_NatTrans_aux F F' α a nat =
    Hom_of_almost_NatTrans_aux F F' α' a' nat' := by
  obtain ⟨a'', comp⟩ := comp
  set A := min a'' (min a a')
  have _ : ∀ (b c : Set.Iic A) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u :=
    fun b c u ↦ nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) (le_trans (min_le_right _ _)
    (min_le_left _ _))⟩ ⟨c.1, le_trans (Set.mem_Iic.mp c.2) (le_trans (min_le_right _ _)
    (min_le_left _ _))⟩ u
  rw [← Hom_of_almost_NatTrans_aux_indep_bound F F' α (a₁ := A) (le_trans (min_le_right _ _)
    (min_le_left _ _))]
  rw [← Hom_of_almost_NatTrans_aux_indep_bound F F' α' (a₁ := A) (le_trans (min_le_right _ _)
    (min_le_right _ _))]
  rw [Hom_of_almost_NatTrans_aux_ext]
  intro b
  exact comp ⟨b.1, by rw [Set.mem_Iic]; exact le_trans (Set.mem_Iic.mp b.2) (min_le_left _ _)⟩

noncomputable def Hom_of_almost_NatTrans [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n))
    (nat : ∃ a, ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u) :
    Limits.limit F ⟶ Limits.limit F' :=
  Hom_of_almost_NatTrans_aux F F' α nat.choose nat.choose_spec

lemma Hom_of_almost_NatTrans_indep [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) (α' : (n : ℤ) → (F.obj n ⟶ F'.obj n))
    (nat : ∃ a, ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u)
    (nat' : ∃ a', ∀ (b c : Set.Iic a') (u : b.1 ⟶ c.1), F.map u ≫ α' c.1 = α' b.1 ≫ F'.map u)
    (compat : ∃ a, ∀ (b : Set.Iic a), α b.1 = α' b.1) :
    Hom_of_almost_NatTrans F F' α nat = Hom_of_almost_NatTrans F F' α' nat' := by
  simp only [Hom_of_almost_NatTrans]
  rw [Hom_of_almost_NatTrans_aux_indep_map]
  exact compat

lemma almost_id_almost_natTrans (α : (n : ℤ) → (F.obj n ⟶ F.obj n))
    (isId : ∃ (a : ℤ), ∀ (b : Set.Iic a), α b.1 = 𝟙 (F.obj b)) :
    ∃ a, ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F.map u := by
  use isId.choose
  intro b c u
  rw [isId.choose_spec b, isId.choose_spec c]
  simp

lemma Hom_of_almost_NatTrans_id [HasLimit F] (α : (n : ℤ) → (F.obj n ⟶ F.obj n))
    (isId : ∃ (a : ℤ), ∀ (b : Set.Iic a), α b.1 = 𝟙 (F.obj b)) :
    Hom_of_almost_NatTrans F F α (almost_id_almost_natTrans F α isId) = 𝟙 (limit F)
    := by
  simp only [Hom_of_almost_NatTrans]
  set a := min isId.choose (almost_id_almost_natTrans F α isId).choose
  have := Initial_inclusion_Iic a
  rw [← Hom_of_almost_NatTrans_aux_indep_bound F F α (a₁ := a) (min_le_right _ _)]
  simp only [Hom_of_almost_NatTrans_aux]
  rw [← cancel_mono (Functor.Initial.limitIso (Inclusion_Iic a) F).inv]
  simp only [assoc, Iso.hom_inv_id, comp_id, id_comp]
  ext j
  erw [limit.pre_π]
  simp only [Functor.comp_obj, Monotone.functor_obj, assoc, limMap_π]
  erw [← assoc, limit.pre_π]
  rw [isId.choose_spec ⟨j.1, Set.mem_Iic.mpr (le_trans j.2 (min_le_left _ _))⟩]
  simp

variable (F'' : ℤ ⥤ C)

lemma comp_almost_natTrans (α : (n : ℤ) → (F.obj n ⟶ F'.obj n))
    (β : (n : ℤ) → (F'.obj n ⟶ F''.obj n))
    (nat₁ : ∃ a₁, ∀ (b c : Set.Iic a₁) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u)
    (nat₂ : ∃ a₂, ∀ (b c : Set.Iic a₂) (u : b.1 ⟶ c.1), F'.map u ≫ β c.1 = β b.1 ≫ F''.map u) :
    ∃ a, ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ (fun n ↦ α n ≫ β n) c.1 =
    (fun n ↦ α n ≫ β n) b.1 ≫ F''.map u := by
  use min nat₁.choose nat₂.choose
  intro b c u
  erw [← assoc, nat₁.choose_spec ⟨b.1, Set.mem_Iic.mpr (le_trans b.2 (min_le_left _ _))⟩
    ⟨c.1, Set.mem_Iic.mpr (le_trans c.2 (min_le_left _ _))⟩ u, assoc,
    nat₂.choose_spec ⟨b.1, Set.mem_Iic.mpr (le_trans b.2 (min_le_right _ _))⟩
    ⟨c.1, Set.mem_Iic.mpr (le_trans c.2 (min_le_right _ _))⟩ u, assoc]

/-- Here be doc string.-/
lemma Hom_of_almost_NatTrans_comp' [HasLimit F] [HasLimit F'] [HasLimit F'']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) (β : (n : ℤ) → (F'.obj n ⟶ F''.obj n))
    (nat₁ : ∃ a₁, ∀ (b c : Set.Iic a₁) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u)
    (nat₂ : ∃ a₂, ∀ (b c : Set.Iic a₂) (u : b.1 ⟶ c.1), F'.map u ≫ β c.1 = β b.1 ≫ F''.map u) :
    Hom_of_almost_NatTrans F F' α nat₁ ≫ Hom_of_almost_NatTrans F' F'' β nat₂ =
    Hom_of_almost_NatTrans F F'' (fun n ↦ α n ≫ β n) (comp_almost_natTrans F F' F'' α β nat₁ nat₂)
    := by
  simp only [Hom_of_almost_NatTrans]
  set a := min (min nat₁.choose nat₂.choose) (comp_almost_natTrans F F' F'' α β nat₁ nat₂).choose
  have := Initial_inclusion_Iic a
  rw [← Hom_of_almost_NatTrans_aux_indep_bound F F'' (fun n ↦ α n ≫ β n) (a₁ := a)
    (min_le_right _ _), ← Hom_of_almost_NatTrans_aux_indep_bound F F' α (a₁ := a)
    (le_trans (min_le_left _ _) (min_le_left _ _)),
    ← Hom_of_almost_NatTrans_aux_indep_bound F' F'' β (a₁ := a)
    (le_trans (min_le_left _ _) (min_le_right _ _))]
  simp only [Hom_of_almost_NatTrans_aux, assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_inv_left]
  rw [← cancel_mono (Functor.Initial.limitIso (Inclusion_Iic a) F'').inv]
  simp; ext _; simp

lemma Hom_of_almost_NatTrans_comp [HasLimit F] [HasLimit F'] [HasLimit F'']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) (β : (n : ℤ) → (F'.obj n ⟶ F''.obj n))
    (γ : (n : ℤ) → (F.obj n ⟶ F''.obj n))
    (nat₁ : ∃ a₁, ∀ (b c : Set.Iic a₁) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u)
    (nat₂ : ∃ a₂, ∀ (b c : Set.Iic a₂) (u : b.1 ⟶ c.1), F'.map u ≫ β c.1 = β b.1 ≫ F''.map u)
    (nat₃ : ∃ a₃, ∀ (b c : Set.Iic a₃) (u : b.1 ⟶ c.1), F.map u ≫ γ c.1 = γ b.1 ≫ F''.map u)
    (comp : ∃ a, ∀ (b : Set.Iic a), α b.1 ≫ β b.1 = γ b.1) :
    Hom_of_almost_NatTrans F F' α nat₁ ≫ Hom_of_almost_NatTrans F' F'' β nat₂ =
    Hom_of_almost_NatTrans F F'' γ nat₃ := by
  rw [Hom_of_almost_NatTrans_indep F F'' γ (fun n ↦ α n ≫ β n) nat₃ (comp_almost_natTrans F F' F''
    α β nat₁ nat₂) (by use comp.choose; exact fun b ↦ (comp.choose_spec b).symm)]
  exact Hom_of_almost_NatTrans_comp' F F' F'' α β nat₁ nat₂

end LimitOnZ

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

namespace Functor
namespace CommShift

universe u' v'

variable {C : Type u} {D : Type u'} [Category.{v,u} C] [Category.{v',u'} D] (F : C ⥤ D) (A : Type*)
  [AddMonoid A] [HasShift C A] [HasShift D A]

/-
theorem zero' (a : A) (ha : a = 0) : ∀ [self : F.CommShift A],
    CommShift.iso a = CommShift.isoZero' F a ha := by
  intro _
  ext _
  simp only [comp_obj, isoZero'_hom_app, shiftFunctorZero', Iso.trans_hom, eqToIso.hom,
    NatTrans.comp_app, id_obj, eqToHom_app, map_comp, Iso.trans_inv, eqToIso.inv, Category.assoc]
-/

-- Should be `Functor.CommShift.op` probably, and take an instance argument.
def op (commF : CommShift F A) :
    CommShift (C := OppositeShift C A) (D := OppositeShift D A) F.op A where
  iso a := (NatIso.op (commF.iso a)).symm
  zero := by
    simp only
    rw [commF.zero]
    ext _
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app, isoZero_inv_app,
      op_comp, isoZero_hom_app, op_map]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    simp
  add a b := by
    simp only
    rw [commF.add]
    ext _
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app, isoAdd_inv_app,
      op_comp, Category.assoc, isoAdd_hom_app, op_map]
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    rfl

noncomputable def removeOp (commFop : CommShift (C := OppositeShift C A)
    (D := OppositeShift D A) F.op A) : CommShift F A where
  iso a := NatIso.removeOp (commFop.iso a).symm
  zero := by
    simp only
    rw [commFop.zero]
    ext _
    simp only [comp_obj, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      isoZero_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, isoZero_hom_app]
    erw [oppositeShiftFunctorZero_hom_app, oppositeShiftFunctorZero_inv_app]
    simp
  add a b := by
    simp only
    rw [commFop.add]
    ext _
    simp only [comp_obj, NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app, op_obj,
      isoAdd_inv_app, op_map, unop_comp, Quiver.Hom.unop_op, Category.assoc, isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_hom_app, oppositeShiftFunctorAdd_inv_app]
    rfl

end CommShift
end Functor

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

/-- Doc string, why the "'"?-/
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
lemma Triangle_π₁_commShiftIso (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

omit [HasZeroObject C] [Pretriangulated C] in
lemma Triangle_π₁_commShiftIso_hom (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

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
