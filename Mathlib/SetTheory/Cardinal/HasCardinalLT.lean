/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.SetTheory.Cardinal.Regular

/-!
# The property of being of cardinality less than a cardinal

Given `X : Type u` and `κ : Cardinal.{v}`, we introduce a predicate
`HasCardinalLT X κ` expressing that
`Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ`.

-/

universe w v u u'

/-- The property that the cardinal of a type `X : Type u` is less than `κ : Cardinal.{v}`. -/
def HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop :=
  Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ

lemma hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) :
    HasCardinalLT X κ ↔ Cardinal.mk X < κ := by
  simp [HasCardinalLT]

namespace HasCardinalLT

section

variable {X : Type u} {κ : Cardinal.{v}} (h : HasCardinalLT X κ)

include h

lemma small : Small.{v} X := by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_, v + 1}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)

lemma of_le {κ' : Cardinal.{v}} (hκ' : κ ≤ κ') :
    HasCardinalLT X κ' :=
  lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

variable {Y : Type u'}

lemma of_injective (f : Y → X) (hf : Function.Injective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULift.up_injective
      (Function.Injective.comp hf ULift.down_injective))) h

lemma of_surjective (f : X → Y) (hf : Function.Surjective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp ULift.up_surjective (Function.Surjective.comp hf
      ULift.down_surjective))) h

end

end HasCardinalLT

lemma hasCardinalLT_iff_of_equiv {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) :
    HasCardinalLT X κ ↔ HasCardinalLT Y κ :=
  ⟨fun h ↦ h.of_injective _ e.symm.injective,
    fun h ↦ h.of_injective _ e.injective⟩

@[simp]
lemma hasCardinalLT_aleph0_iff (X : Type u) :
    HasCardinalLT X Cardinal.aleph0.{v} ↔ Finite X := by
  simpa [HasCardinalLT] using Cardinal.mk_lt_aleph0_iff

lemma hasCardinalLT_of_finite
    (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT X κ :=
  .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

@[simp]
lemma hasCardinalLT_lift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT X (Cardinal.lift.{u} κ) ↔ HasCardinalLT X κ := by
  simp [HasCardinalLT, ← (Cardinal.lift_strictMono.{max v w, max u}).lt_iff_lt]

@[simp]
lemma hasCardinalLT_ulift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT (ULift.{u} X) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv Equiv.ulift κ

lemma hasCardinalLT_sum_iff (X : Type u) (Y : Type u') (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (X ⊕ Y) κ ↔ HasCardinalLT X κ ∧ HasCardinalLT Y κ := by
  constructor
  · intro h
    exact ⟨h.of_injective _ Sum.inl_injective,
      h.of_injective _ Sum.inr_injective⟩
  · rintro ⟨hX, hY⟩
    dsimp [HasCardinalLT] at hX hY ⊢
    rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at hX
    rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift] at hY
    simp only [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift]
    exact Cardinal.add_lt_of_lt (by simpa using hκ) hX hY

lemma hasCardinalLT_option_iff (X : Type u) (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Option X) κ ↔ HasCardinalLT X κ := by
  rw [hasCardinalLT_iff_of_equiv (Equiv.optionEquivSumPUnit.{0} X),
    hasCardinalLT_sum_iff _ _ _ hκ, and_iff_left_iff_imp]
  refine fun _ ↦ HasCardinalLT.of_le ?_ hκ
  rw [hasCardinalLT_aleph0_iff]
  infer_instance

lemma hasCardinalLT_subtype_max
    {X : Type*} {P₁ P₂ : X → Prop} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT (Subtype P₁) κ) (h₂ : HasCardinalLT (Subtype P₂) κ) :
    HasCardinalLT (Subtype (P₁ ⊔ P₂)) κ := by
  have : HasCardinalLT (Subtype P₁ ⊕ Subtype P₂) κ := by
    rw [hasCardinalLT_sum_iff _ _ _ hκ]
    exact ⟨h₁, h₂⟩
  refine this.of_surjective (Sum.elim (fun x ↦ ⟨x.1, Or.inl x.2⟩)
    (fun x ↦ ⟨x.1, Or.inr x.2⟩)) ?_
  rintro ⟨x, hx | hx⟩
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

lemma hasCardinalLT_union
    {X : Type*} {S₁ S₂ : Set X} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardinalLT S₂ κ) :
    HasCardinalLT (S₁ ∪ S₂ : Set _) κ :=
  hasCardinalLT_subtype_max hκ h₁ h₂

/-- The particular case of `hasCardinatLT_sigma` when all the inputs are in the
same universe `w`. It is used to prove the general case. -/
lemma hasCardinalLT_sigma' {ι : Type w} (α : ι → Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : ∀ i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  simp only [hasCardinalLT_iff_cardinal_mk_lt] at hι hα ⊢
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_lift_of_isRegular.{w, w} Fact.out (by simpa) hα

lemma hasCardinalLT_sigma {ι : Type u} (α : ι → Type v) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : ∀ i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  have : Fact (Cardinal.lift.{max u v} κ).IsRegular := ⟨Cardinal.IsRegular.lift Fact.out⟩
  have := hasCardinalLT_sigma'
    (fun (i : ULift.{max v w} ι) ↦ ULift.{max u w} (α (ULift.down i)))
    (Cardinal.lift.{max u v} κ) (by simpa)
    (fun i ↦ by simpa using hα (ULift.down i))
  rw [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨i, a⟩ ↦ ⟨ULift.down i, ULift.down a⟩)
    (fun ⟨i, a⟩ ↦ ⟨⟨ULift.up i, ULift.up a⟩, rfl⟩)

lemma hasCardinalLT_subtype_iSup
    {ι : Type*} {X : Type*} (P : ι → X → Prop) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hP : ∀ i, HasCardinalLT (Subtype (P i)) κ) :
    HasCardinalLT (Subtype (⨆ i, P i)) κ :=
  (hasCardinalLT_sigma (fun i ↦ Subtype (P i)) κ hι hP).of_surjective
    (fun ⟨i, x, hx⟩ ↦ ⟨x, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨i, hx⟩⟩) (by
    rintro ⟨_, h⟩
    simp only [iSup_apply, iSup_Prop_eq] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, _, hi⟩, rfl⟩)

lemma hasCardinalLT_iUnion
    {ι : Type*} {X : Type*} (S : ι → Set X) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hS : ∀ i, HasCardinalLT (S i) κ) :
    HasCardinalLT (⋃ i, S i) κ := by
  convert show HasCardinalLT (setOf ((⨆ i, S i))) κ from hasCardinalLT_subtype_iSup S hι hS
  aesop

/-- The particular case of `hasCardinatLT_prod` when all the inputs are in the
same universe `w`. It is used to prove the general case. -/
lemma hasCardinalLT_prod' {T₁ T₂ : Type w} {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ := by
  rw [hasCardinalLT_iff_cardinal_mk_lt] at h₁ h₂ ⊢
  simpa using Cardinal.mul_lt_of_lt hκ h₁ h₂

lemma hasCardinalLT_prod {T₁ : Type u} {T₂ : Type u'}
    {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ := by
  have := hasCardinalLT_prod' (T₁ := ULift.{max u' w} T₁) (T₂ := ULift.{max u w} T₂)
    (κ := Cardinal.lift.{max u u'} κ) (by simpa) (by simpa) (by simpa)
  simp only [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨x₁, x₂⟩ ↦ ⟨ULift.down x₁, ULift.down x₂⟩) (fun ⟨x₁, x₂⟩ ↦
    ⟨⟨ULift.up x₁, ULift.up x₂⟩, rfl⟩)

namespace HasCardinalLT

/-- For any `w`-small type `X`, there exists a regular cardinal `κ : Cardinal.{w}`
such that `HasCardinalLT X κ`. -/
lemma exists_regular_cardinal (X : Type u) [Small.{w} X] :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ HasCardinalLT X κ :=
  ⟨Order.succ (max (Cardinal.mk (Shrink.{w} X)) .aleph0),
    Cardinal.isRegular_succ (le_max_right _ _), by
      simp [hasCardinalLT_iff_of_equiv (equivShrink.{w} X),
        hasCardinalLT_iff_cardinal_mk_lt]⟩

/-- For any `w`-small family `X : ι → Type u` of `w`-small types, there exists
a regular cardinal `κ : Cardinal.{w}` such that `HasCardinalLT (X i) κ` for all `i : ι`. -/
lemma exists_regular_cardinal_forall {ι : Type v} (X : ι → Type u) [Small.{w} ι]
    [∀ i, Small.{w} (X i)] :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ ∀ (i : ι), HasCardinalLT (X i) κ := by
  obtain ⟨κ, hκ, h⟩ := exists_regular_cardinal.{w} (Sigma X)
  exact ⟨κ, hκ, fun i ↦ h.of_injective _ sigma_mk_injective⟩

end HasCardinalLT
