/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Batteries.Tactic.Congr
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Data.Set.SymmDiff
public import Mathlib.Data.Set.Inclusion

/-!
# Images and preimages of sets

## Main definitions

* `preimage f t : Set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `range f : Set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

## Notation

* `f ⁻¹' t` for `Set.preimage f t`

* `f '' s` for `Set.image f s`

## Tags

set, sets, image, preimage, pre-image, range

-/

@[expose] public section

assert_not_exists WithTop OrderIso

universe u v

open Function Set

namespace Set

variable {α β γ : Type*} {ι : Sort*}

/-! ### Inverse image -/


section Preimage

variable {f : α → β} {g : β → γ}

@[simp]
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl

theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s := by
  congr with x
  simp [h]

@[gcongr]
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := fun _ hx => h hx

@[simp, mfld_simps]
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl

theorem subset_preimage_univ {s : Set α} : s ⊆ f ⁻¹' univ :=
  subset_univ _

@[simp, mfld_simps]
theorem preimage_inter {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl

@[simp]
theorem preimage_union {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl

@[simp]
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl

@[simp]
theorem preimage_diff (f : α → β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl

open scoped symmDiff in
@[simp]
lemma preimage_symmDiff {f : α → β} (s t : Set β) : f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
  rfl

@[simp]
theorem preimage_ite (f : α → β) (s t₁ t₂ : Set β) :
    f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl

@[simp]
theorem preimage_setOf_eq {p : α → Prop} {f : β → α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl

@[simp]
theorem preimage_id_eq : preimage (id : α → α) = id :=
  rfl

@[mfld_simps]
theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl

@[simp, mfld_simps]
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl

@[simp]
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun _ : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun _ => h

@[simp]
theorem preimage_const_of_notMem {b : β} {s : Set β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun _ hx => h hx

@[deprecated (since := "2025-05-23")] alias preimage_const_of_not_mem := preimage_const_of_notMem

theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] :
    (fun _ : α => b) ⁻¹' s = if b ∈ s then univ else ∅ := by grind

/-- If preimage of each singleton under `f : α → β` is either empty or the whole type,
then `f` is a constant. -/
lemma exists_eq_const_of_preimage_singleton [Nonempty β] {f : α → β}
    (hf : ∀ b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b} = univ) : ∃ b, f = const α b := by
  rcases em (∃ b, f ⁻¹' {b} = univ) with ⟨b, hb⟩ | hf'
  · exact ⟨b, funext fun x ↦ eq_univ_iff_forall.1 hb x⟩
  · have : ∀ x b, f x ≠ b := fun x b ↦
      eq_empty_iff_forall_notMem.1 ((hf b).resolve_right fun h ↦ hf' ⟨b, h⟩) x
    exact ⟨Classical.arbitrary β, funext fun x ↦ absurd rfl (this x _)⟩

theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl

theorem preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g :=
  rfl

theorem preimage_iterate_eq {f : α → α} {n : ℕ} : Set.preimage f^[n] = (Set.preimage f)^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, iterate_succ', preimage_comp_eq, ih]

theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} :
    f ⁻¹' (g ⁻¹' s) = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ ∀ (x) (h : p x), (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t := by grind

theorem nonempty_of_nonempty_preimage {s : Set β} {f : α → β} (hf : (f ⁻¹' s).Nonempty) :
    s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩

@[simp] theorem preimage_singleton_true (p : α → Prop) : p ⁻¹' {True} = {a | p a} := by ext; simp

@[simp] theorem preimage_singleton_false (p : α → Prop) : p ⁻¹' {False} = {a | ¬p a} := by ext; simp

theorem preimage_subtype_coe_eq_compl {s u v : Set α} (hsuv : s ⊆ u ∪ v)
    (H : s ∩ (u ∩ v) = ∅) : ((↑) : s → α) ⁻¹' u = ((↑) ⁻¹' v)ᶜ := by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_notMem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · grind

lemma preimage_subset {s t} (hs : s ⊆ f '' t) (hf : Set.InjOn f (f ⁻¹' s)) : f ⁻¹' s ⊆ t := by
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hs ha
  rwa [hf ha _ hba.symm]
  simpa [hba]

end Preimage

/-! ### Image of a set under a function -/


section Image

variable {f : α → β} {s t : Set α}

theorem image_eta (f : α → β) : f '' s = (fun x => f x) '' s :=
  rfl

theorem _root_.Function.Injective.mem_set_image {f : α → β} (hf : Injective f) {s : Set α} {a : α} :
    f a ∈ f '' s ↔ a ∈ s :=
  ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, by grind⟩

lemma preimage_subset_of_surjOn {t : Set β} (hf : Injective f) (h : SurjOn f s t) :
    f ⁻¹' t ⊆ s := fun _ hx ↦
  hf.mem_set_image.1 <| h hx

theorem forall_mem_image {f : α → β} {s : Set α} {p : β → Prop} :
    (∀ y ∈ f '' s, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x) := by simp

theorem exists_mem_image {f : α → β} {s : Set α} {p : β → Prop} :
    (∃ y ∈ f '' s, p y) ↔ ∃ x ∈ s, p (f x) := by simp

@[congr]
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f '' s = g '' s := by
  aesop

/-- A common special case of `image_congr` -/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f '' s = g '' s := by
  grind

@[gcongr]
lemma image_mono (h : s ⊆ t) : f '' s ⊆ f '' t := by grind

/-- `Set.image` is monotone. See `Set.image_mono` for the statement in terms of `⊆`. -/
lemma monotone_image : Monotone (image f) := fun _ _ => image_mono

theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g '' a = f '' (g '' a) := by aesop

theorem image_comp_eq {g : β → γ} : image (g ∘ f) = image g ∘ image f := by grind

/-- A variant of `image_comp`, useful for rewriting -/
@[grind =]
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g '' (f '' s) = (fun x => g (f x)) '' s :=
  (image_comp g f s).symm

theorem image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').image g' := by grind

theorem _root_.Function.Semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h

theorem _root_.Function.Commute.set_image {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  Function.Semiconj.set_image h

@[deprecated image_mono (since := "2025-08-01")]
theorem image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
  image_mono h

theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t := by grind

@[simp]
theorem image_empty (f : α → β) : f '' ∅ = ∅ := by grind

theorem image_inter_subset (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  subset_inter (image_mono inter_subset_left) (image_mono inter_subset_right)

theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x ∈ t, ∀ y ∈ s, f x = f y → x = y) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  (image_inter_subset _ _ _).antisymm
    fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ ↦
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩

theorem image_inter {f : α → β} {s t : Set α} (H : Injective f) : f '' (s ∩ t) = f '' s ∩ f '' t :=
  image_inter_on fun _ _ _ _ h => H h

theorem image_univ_of_surjective {ι : Type*} {f : ι → β} (H : Surjective f) : f '' univ = univ :=
  eq_univ_of_forall <| by simpa [image]

@[simp]
theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} := by grind

@[simp]
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) '' s = {a} :=
  ext fun _ =>
    ⟨fun ⟨_, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun _ hy => ⟨hy, rfl⟩⟩

@[simp, mfld_simps]
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f '' s = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_forall_notMem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (s : Set α) :
    HasCompl.compl ⁻¹' s = HasCompl.compl '' s :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun _ hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩

theorem mem_compl_image [BooleanAlgebra α] (t : α) (s : Set α) :
    t ∈ HasCompl.compl '' s ↔ tᶜ ∈ s := by
  simp [← preimage_compl_eq_image_compl]

@[simp]
theorem image_id_eq : image (id : α → α) = id := by ext; simp

/-- A variant of `image_id` -/
@[simp]
theorem image_id' (s : Set α) : (fun x => x) '' s = s := by
  ext
  simp

theorem image_id (s : Set α) : id '' s = s := by simp

lemma image_iterate_eq {f : α → α} {n : ℕ} : image (f^[n]) = (image f)^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ', iterate_succ', ← ih, image_comp_eq]

theorem compl_compl_image [BooleanAlgebra α] (s : Set α) :
    HasCompl.compl '' (HasCompl.compl '' s) = s := by
  rw [← image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : Set α} :
    f '' insert a s = insert (f a) (f '' s) := by grind

theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} := by grind

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set α) :
    f '' s ⊆ g ⁻¹' s := fun _ ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set β) :
    f ⁻¹' s ⊆ g '' s := fun b h => ⟨f b, h, I b⟩

theorem range_inter_ssubset_iff_preimage_ssubset {f : α → β} {s s' : Set β} :
    range f ∩ s ⊂ range f ∩ s' ↔ f ⁻¹' s ⊂ f ⁻¹' s' := by
  simp only [Set.ssubset_iff_exists]
  apply and_congr ?_ (by aesop)
  constructor
  all_goals
    intro r x hx
    simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage,
      mem_inter_iff, mem_range, true_and]
    aesop

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : image f = preimage g :=
  funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)

theorem _root_.Function.Involutive.image_eq_preimage_symm {f : α → α} (hf : f.Involutive) :
    image f = preimage f :=
  image_eq_preimage_of_inverse hf.leftInverse hf.rightInverse

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b ∈ f '' s ↔ g b ∈ s := by
  rw [image_eq_preimage_of_inverse h₁ h₂]; rfl

theorem image_compl_subset {f : α → β} {s : Set α} (H : Injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
  Disjoint.subset_compl_left <| by simp [disjoint_iff_inf_le, ← image_inter H]

theorem subset_image_compl {f : α → β} {s : Set α} (H : Surjective f) : (f '' s)ᶜ ⊆ f '' sᶜ :=
  compl_subset_iff_union.2 <| by
    rw [← image_union]
    simp [image_univ_of_surjective H]

theorem image_compl_eq {f : α → β} {s : Set α} (H : Bijective f) : f '' sᶜ = (f '' s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

theorem subset_image_diff (f : α → β) (s t : Set α) : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rw [diff_subset_iff, ← image_union, union_diff_self]
  exact image_mono subset_union_right

open scoped symmDiff in
theorem subset_image_symmDiff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
  (union_subset_union (subset_image_diff _ _ _) <| subset_image_diff _ _ _).trans
    (superset_of_eq (image_union _ _ _))

theorem image_diff {f : α → β} (hf : Injective f) (s t : Set α) : f '' (s \ t) = f '' s \ f '' t :=
  Subset.antisymm
    (Subset.trans (image_inter_subset _ _ _) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_diff f s t)

open scoped symmDiff in
theorem image_symmDiff (hf : Injective f) (s t : Set α) : f '' s ∆ t = (f '' s) ∆ (f '' t) := by
  simp_rw [Set.symmDiff_def, image_union, image_diff hf]

theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f '' s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩

theorem Nonempty.of_image {f : α → β} {s : Set α} : (f '' s).Nonempty → s.Nonempty
  | ⟨_, x, hx, _⟩ => ⟨x, hx⟩

@[simp]
theorem image_nonempty {f : α → β} {s : Set α} : (f '' s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.image f⟩

theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : Surjective f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, by grind⟩

instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f '' s) :=
  (Set.Nonempty.image f .of_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  forall_mem_image

theorem image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s :=
  image_subset_iff.2 Subset.rfl

theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f '' s) := fun _ =>
  mem_image_of_mem f

theorem preimage_image_univ {f : α → β} : f ⁻¹' (f '' univ) = univ :=
  Subset.antisymm (fun _ _ => trivial) (subset_preimage_image f univ)

@[simp]
theorem preimage_image_eq {f : α → β} (s : Set α) (h : Injective f) : f ⁻¹' (f '' s) = s :=
  Subset.antisymm (fun _ ⟨_, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

@[simp]
theorem image_preimage_eq {f : α → β} (s : Set β) (h : Surjective f) : f '' (f ⁻¹' s) = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, by grind⟩

@[simp]
theorem Nonempty.subset_preimage_const {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β) :
    s ⊆ (fun _ => a) ⁻¹' t ↔ a ∈ t := by
  rw [← image_subset_iff, hs.image_const, singleton_subset_iff]

-- Note defeq abuse identifying `preimage` with function composition in the following two proofs.

@[simp]
theorem preimage_injective : Injective (preimage f) ↔ Surjective f :=
  injective_comp_right_iff_surjective

@[simp]
theorem preimage_surjective : Surjective (preimage f) ↔ Injective f :=
  surjective_comp_right_iff_injective

@[simp]
theorem preimage_eq_preimage {f : β → α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  (preimage_injective.mpr hf).eq_iff

theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) :
    f '' (s ∩ f ⁻¹' t) = f '' s ∩ t := by grind

theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) :
    f '' (f ⁻¹' t ∩ s) = t ∩ f '' s := by simp only [inter_comm, image_inter_preimage]

@[simp]
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} :
    (f '' s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty := by
  rw [← image_inter_preimage, image_nonempty]

theorem disjoint_image_left {f : α → β} {s : Set α} {t : Set β} :
    Disjoint (f '' s) t ↔ Disjoint s (f ⁻¹' t) := by
  simp_rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, image_inter_nonempty_iff]

theorem disjoint_image_right {f : α → β} {s : Set α} {t : Set β} :
    Disjoint t (f '' s) ↔ Disjoint (f ⁻¹' t) s := by
  rw [disjoint_comm, disjoint_comm (b := s), disjoint_image_left]

theorem image_diff_preimage {f : α → β} {s : Set α} {t : Set β} :
    f '' (s \ f ⁻¹' t) = f '' s \ t := by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

theorem compl_image : image (compl : Set α → Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : Set α → Prop} : compl '' { s | p s } = { s | p sᶜ } :=
  congr_fun compl_image p

theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) := fun _ h => ⟨mem_image_of_mem _ h.left, h.right⟩

theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) := fun _ h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r

theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)

theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} :
    f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl

theorem image_eq_image {f : α → β} (hf : Injective f) : f '' s = f '' t ↔ s = t :=
  Iff.symm <|
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, eq]

theorem subset_image_iff {t : Set β} :
    t ⊆ f '' s ↔ ∃ u, u ⊆ s ∧ f '' u = t := by
  refine ⟨fun h ↦ ⟨f ⁻¹' t ∩ s, inter_subset_right, ?_⟩,
    fun ⟨u, hu, hu'⟩ ↦ hu'.symm ▸ image_mono hu⟩
  rwa [image_preimage_inter, inter_eq_left]

@[simp]
lemma exists_subset_image_iff {p : Set β → Prop} : (∃ t ⊆ f '' s, p t) ↔ ∃ t ⊆ s, p (f '' t) := by
  simp [subset_image_iff]

@[simp]
lemma forall_subset_image_iff {p : Set β → Prop} : (∀ t ⊆ f '' s, p t) ↔ ∀ t ⊆ s, p (f '' t) := by
  simp [subset_image_iff]

theorem image_subset_image_iff {f : α → β} (hf : Injective f) : f '' s ⊆ f '' t ↔ s ⊆ t := by
  grind [Set.image_subset_iff, Set.preimage_image_eq]

theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s → β) {h : α → β}
    (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) ∈ r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) '' ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quot.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) ∈ r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩

theorem exists_image_iff (f : α → β) (x : Set α) (P : β → Prop) :
    (∃ a : f '' x, P a) ↔ ∃ a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.choose_spec.1⟩, a.prop.choose_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩

theorem imageFactorization_eq {f : α → β} {s : Set α} :
    Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun _ => rfl

theorem imageFactorization_surjective {f : α → β} {s : Set α} :
    Surjective (imageFactorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩

@[deprecated (since := "2025-08-18")] alias surjective_onto_image := imageFactorization_surjective

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a ≠ a } ⊆ s) : σ '' s = s := by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine ⟨?_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine iff_of_true ⟨σ.symm i, hs fun h => hi ?_, σ.apply_symm_apply _⟩ (hs hi)
    grind

end Image

/-! ### Lemmas about the powerset and image. -/

/-- The powerset of `{a} ∪ s` is `𝒫 s` together with `{a} ∪ t` for each `t ∈ 𝒫 s`. -/
theorem powerset_insert (s : Set α) (a : α) : 𝒫 insert a s = 𝒫 s ∪ insert a '' 𝒫 s := by
  ext t
  constructor
  · intro h
    by_cases hs : a ∈ t
    · right
      refine ⟨t \ {a}, by grind⟩
    · grind
  · grind

theorem disjoint_powerset_insert {s : Set α} {a : α} (h : a ∉ s) :
    Disjoint (𝒫 s) (insert a '' 𝒫 s) := by
  grind

theorem powerset_insert_injOn {s : Set α} {a : α} (h : a ∉ s) :
    Set.InjOn (insert a) (𝒫 s) := fun u u_mem v v_mem eq ↦ by
  grind

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α} {s t : Set α}

theorem forall_mem_range {p : α → Prop} : (∀ a ∈ range f, p a) ↔ ∀ i, p (f i) := by simp

theorem forall_subtype_range_iff {p : range f → Prop} :
    (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ := by grind

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ ∃ i, p (f i) := by simp

theorem exists_subtype_range_iff {p : range f → Prop} :
    (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ := by grind

theorem range_eq_univ : range f = univ ↔ Surjective f :=
  eq_univ_iff_forall

alias ⟨_, _root_.Function.Surjective.range_eq⟩ := range_eq_univ

@[simp]
theorem subset_range_of_surjective {f : α → β} (h : Surjective f) (s : Set β) :
    s ⊆ range f := Surjective.range_eq h ▸ subset_univ s

@[simp]
theorem image_univ {f : α → β} : f '' univ = range f := by grind

lemma image_compl_eq_range_diff_image {f : α → β} (hf : Injective f) (s : Set α) :
    f '' sᶜ = range f \ f '' s := by rw [← image_univ, ← image_diff hf, compl_eq_univ_diff]

/-- Alias of `Set.image_compl_eq_range_sdiff_image`. -/
lemma range_diff_image {f : α → β} (hf : Injective f) (s : Set α) : range f \ f '' s = f '' sᶜ := by
  rw [image_compl_eq_range_diff_image hf]

@[simp]
theorem preimage_eq_univ_iff {f : α → β} {s} : f ⁻¹' s = univ ↔ range f ⊆ s := by
  rw [← univ_subset_iff, ← image_subset_iff, image_univ]

theorem image_subset_range (f : α → β) (s) : f '' s ⊆ range f := by
  rw [← image_univ]; exact image_mono (subset_univ _)

theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f '' s) : x ∈ range f :=
  image_subset_range f s h

theorem _root_.Nat.mem_range_succ (i : ℕ) : i ∈ range Nat.succ ↔ 0 < i :=
  ⟨by grind, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩

theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : s ⊆ range f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨_, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, by grind⟩

theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g '' range f := by aesop

/--
Variant of `range_comp` using a lambda instead of function composition.
-/
theorem range_comp' (g : α → β) (f : ι → α) : range (fun x => g (f x)) = g '' range f :=
  range_comp g f

theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_mem_range

theorem range_subset_range_iff_exists_comp {f : α → γ} {g : β → γ} :
    range f ⊆ range g ↔ ∃ h : α → β, f = g ∘ h := by
  simp only [range_subset_iff, mem_range, Classical.skolem, funext_iff, (· ∘ ·), eq_comm]

theorem range_eq_iff (f : α → β) (s : Set β) :
    range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b := by grind

theorem range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g := by grind

theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨_, x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩

theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h

@[simp]
theorem range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]

theorem range_eq_empty [IsEmpty ι] (f : ι → α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›

@[simp]
theorem range_eq_singleton_iff [Nonempty ι] {y} :
    Set.range f = {y} ↔ ∀ (x : ι), f x = y := by
  simp_rw [Set.ext_iff, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun h _ => by simp_rw [← h, exists_apply_eq_apply],
      fun h _ => by simp_rw [h, exists_const, eq_comm]⟩

theorem range_eq_singleton [Nonempty ι] {y} (hy : ∀ (x : ι), f x = y) :
    Set.range f = {y} := range_eq_singleton_iff.mpr hy

instance instNonemptyRange [Nonempty ι] (f : ι → α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

@[simp]
theorem image_union_image_compl_eq_range (f : α → β) : f '' s ∪ f '' sᶜ = range f := by grind

theorem insert_image_compl_eq_range (f : α → β) (x : α) : insert (f x) (f '' {x}ᶜ) = range f := by
  grind

theorem image_preimage_eq_range_inter {f : α → β} {t : Set β} : f '' (f ⁻¹' t) = range f ∩ t := by
  grind

theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f '' (f ⁻¹' t) = t ∩ range f := by
  grind

theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ range f) :
    f '' (f ⁻¹' s) = s := by grind

theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ range f := by grind

theorem subset_range_iff_exists_image_eq {f : α → β} {s : Set β} : s ⊆ range f ↔ ∃ t, f '' t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨_, ht⟩ => ht ▸ image_subset_range _ _⟩

theorem range_image (f : α → β) : range (image f) = 𝒫 range f :=
  ext fun _ => subset_range_iff_exists_image_eq.symm

@[simp]
theorem exists_subset_range_and_iff {f : α → β} {p : Set β → Prop} :
    (∃ s, s ⊆ range f ∧ p s) ↔ ∃ s, p (f '' s) := by
  rw [← exists_range_iff, range_image]; rfl

@[simp]
theorem forall_subset_range_iff {f : α → β} {p : Set β → Prop} :
    (∀ s, s ⊆ range f → p s) ↔ ∀ s, p (f '' s) := by
  rw [← forall_mem_range, range_image]; simp only [mem_powerset_iff]

@[simp]
theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ range f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h

theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply Subset.antisymm
    · rw [← preimage_subset_preimage_iff hs, h]
    · rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl

-- Not `@[simp]` since `simp` can prove this.
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩

-- Not `@[simp]` since `simp` can prove this.
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]

theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s := by
  rw [image_preimage_eq_range_inter, preimage_range_inter]

@[simp, mfld_simps]
theorem range_id : range (@id α) = univ :=
  range_eq_univ.2 surjective_id

@[simp, mfld_simps]
theorem range_id' : (range fun x : α => x) = univ :=
  range_id

@[simp]
theorem _root_.Prod.range_fst [Nonempty β] : range (Prod.fst : α × β → α) = univ :=
  Prod.fst_surjective.range_eq

@[simp]
theorem _root_.Prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq

@[simp]
theorem range_eval {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
    range (eval i : (∀ i, α i) → α i) = univ :=
  (surjective_eval i).range_eq

theorem range_inl : range (@Sum.inl α β) = {x | Sum.isLeft x} := by ext (_ | _) <;> simp
theorem range_inr : range (@Sum.inr α β) = {x | Sum.isRight x} := by ext (_ | _) <;> simp

theorem isCompl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.inr) :=
  IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, h⟩⟩
      exact Sum.noConfusion h)
    (by rintro (x | y) - <;> [left; right] <;> exact mem_range_self _)

@[simp]
theorem range_inl_union_range_inr : range (Sum.inl : α → α ⊕ β) ∪ range Sum.inr = univ :=
  isCompl_range_inl_range_inr.sup_eq_top

@[simp]
theorem range_inl_inter_range_inr : range (Sum.inl : α → α ⊕ β) ∩ range Sum.inr = ∅ :=
  isCompl_range_inl_range_inr.inf_eq_bot

@[simp]
theorem range_inr_union_range_inl : range (Sum.inr : β → α ⊕ β) ∪ range Sum.inl = univ :=
  isCompl_range_inl_range_inr.symm.sup_eq_top

@[simp]
theorem range_inr_inter_range_inl : range (Sum.inr : β → α ⊕ β) ∩ range Sum.inl = ∅ :=
  isCompl_range_inl_range_inr.symm.inf_eq_bot

@[simp]
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' (@Sum.inr α β '' s) = ∅ := by
  ext
  simp

@[simp]
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' (@Sum.inl α β '' s) = ∅ := by
  ext
  simp

@[simp]
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β → α ⊕ β) = ∅ := by
  rw [← image_univ, preimage_inl_image_inr]

@[simp]
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α → α ⊕ β) = ∅ := by
  rw [← image_univ, preimage_inr_image_inl]

@[simp]
theorem compl_range_inl : (range (Sum.inl : α → α ⊕ β))ᶜ = range (Sum.inr : β → α ⊕ β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr

@[simp]
theorem compl_range_inr : (range (Sum.inr : β → α ⊕ β))ᶜ = range (Sum.inl : α → α ⊕ β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr.symm

theorem preimage_sumElim (s : Set γ) (f : α → γ) (g : β → γ) :
    Sum.elim f g ⁻¹' s = Sum.inl '' (f ⁻¹' s) ∪ Sum.inr '' (g ⁻¹' s) := by
  ext (_ | _) <;> simp

theorem image_preimage_inl_union_image_preimage_inr (s : Set (α ⊕ β)) :
    Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) = s := by
  rw [← preimage_sumElim, Sum.elim_inl_inr, preimage_id]

theorem image_sumElim (s : Set (α ⊕ β)) (f : α → γ) (g : β → γ) :
    Sum.elim f g '' s = f '' (Sum.inl ⁻¹' s) ∪ g '' (Sum.inr ⁻¹' s) := by
  grind

@[simp]
theorem range_quot_mk (r : α → α → Prop) : range (Quot.mk r) = univ :=
  Quot.mk_surjective.range_eq

@[simp]
theorem range_quot_lift {r : ι → ι → Prop} (hf : ∀ x y, r x y → f x = f y) :
    range (Quot.lift f hf) = range f :=
  ext fun _ => Quot.mk_surjective.exists

@[simp]
theorem range_quotient_mk {s : Setoid α} : range (Quotient.mk s) = univ :=
  range_quot_mk _

@[simp]
theorem range_quotient_lift [s : Setoid ι] (hf) :
    range (Quotient.lift f hf : Quotient s → α) = range f :=
  range_quot_lift _

@[simp]
theorem range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α → Quotient s) = univ :=
  range_quot_mk _

lemma Quotient.range_mk'' {sa : Setoid α} : range (Quotient.mk'' (s₁ := sa)) = univ :=
  range_quotient_mk

@[simp]
theorem range_quotient_lift_on' {s : Setoid ι} (hf) :
    (range fun x : Quotient s => Quotient.liftOn' x f hf) = range f :=
  range_quot_lift _

instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Set α) (Set β) (c '' ·) fun s => ∀ x ∈ s, p x where
  prf _ hs := subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)

theorem range_const_subset {c : α} : (range fun _ : ι => c) ⊆ {c} :=
  range_subset_iff.2 fun _ => rfl

@[simp]
theorem range_const : ∀ [Nonempty ι] {c : α}, (range fun _ : ι => c) = {c} :=
  range_eq_singleton (fun _ => rfl)

theorem range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
    range (Subtype.map f h) = (↑) ⁻¹' (f '' { x | p x }) := by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map]
  simp only [Subtype.mk.injEq, exists_prop, mem_setOf_eq]

theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse

theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ range f :=
  Iff.rfl

theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not

theorem range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x := by
  simp [funext_iff]

theorem image_compl_preimage {f : α → β} {s : Set β} : f '' (f ⁻¹' s)ᶜ = range f \ s := by
  rw [compl_eq_univ_diff, image_diff_preimage, image_univ]

theorem rangeFactorization_eq {f : ι → β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun _ => rfl

@[simp]
theorem rangeFactorization_coe (f : ι → β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl

@[simp]
theorem coe_comp_rangeFactorization (f : ι → β) : (↑) ∘ rangeFactorization f = f := rfl

@[deprecated (since := "2025-08-18")] alias surjective_onto_range := rangeFactorization_surjective

theorem image_eq_range (f : α → β) (s : Set α) : f '' s = range fun x : s => f x := by
  ext
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩
  · rintro ⟨⟨x, h1⟩, h2⟩
    exact ⟨x, h1, h2⟩

theorem _root_.Sum.range_eq (f : α ⊕ β → γ) :
    range f = range (f ∘ Sum.inl) ∪ range (f ∘ Sum.inr) :=
  ext fun _ => Sum.exists

@[simp]
theorem Sum.elim_range (f : α → γ) (g : β → γ) : range (Sum.elim f g) = range f ∪ range g :=
  Sum.range_eq _

theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} :
    range (if p then f else g) ⊆ range f ∪ range g := by grind

theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
    (range fun x => if p x then f x else g x) ⊆ range f ∪ range g := by grind

@[simp]
theorem preimage_range (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self

/-- The range of a function from a `Unique` type contains just the
function applied to its single value. -/
theorem range_unique [h : Unique ι] : range f = {f default} := by
  ext x
  rw [mem_range]
  constructor
  · rintro ⟨i, hi⟩
    rw [h.uniq i] at hi
    grind
  · grind

theorem range_diff_image_subset (f : α → β) (s : Set α) : range f \ f '' s ⊆ f '' sᶜ :=
  fun _ ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

@[simp]
theorem range_inclusion (h : s ⊆ t) : range (inclusion h) = { x : t | (x : α) ∈ s } := by
  ext ⟨x, hx⟩
  simp

-- When `f` is injective, see also `Equiv.ofInjective`.
theorem leftInverse_rangeSplitting (f : α → β) :
    LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x => by
  ext
  simp only [rangeFactorization_coe]
  apply apply_rangeSplitting

theorem rangeSplitting_injective (f : α → β) : Injective (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).injective

theorem rightInverse_rangeSplitting {f : α → β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).rightInverse_of_injective fun _ _ hxy =>
    h <| Subtype.ext_iff.1 hxy

theorem preimage_rangeSplitting {f : α → β} (hf : Injective f) :
    preimage (rangeSplitting f) = image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (rightInverse_rangeSplitting hf)
      (leftInverse_rangeSplitting f)).symm

theorem isCompl_range_some_none (α : Type*) : IsCompl (range (some : α → Option α)) {none} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, (hn : _ = none)⟩ => Option.some_ne_none _ (ha.trans hn))
    fun x _ => Option.casesOn x (Or.inr rfl) fun _ => Or.inl <| mem_range_self _

@[simp]
theorem compl_range_some (α : Type*) : (range (some : α → Option α))ᶜ = {none} :=
  (isCompl_range_some_none α).compl_eq

@[simp]
theorem range_some_inter_none (α : Type*) : range (some : α → Option α) ∩ {none} = ∅ :=
  (isCompl_range_some_none α).inf_eq_bot

-- Not `@[simp]` since `simp` can prove this.
theorem range_some_union_none (α : Type*) : range (some : α → Option α) ∪ {none} = univ :=
  (isCompl_range_some_none α).sup_eq_top

@[simp]
theorem insert_none_range_some (α : Type*) : insert none (range (some : α → Option α)) = univ :=
  (isCompl_range_some_none α).symm.sup_eq_top

lemma image_of_range_union_range_eq_univ {α β γ γ' δ δ' : Type*}
    {h : β → α} {f : γ → β} {f₁ : γ' → α} {f₂ : γ → γ'} {g : δ → β} {g₁ : δ' → α} {g₂ : δ → δ'}
    (hf : h ∘ f = f₁ ∘ f₂) (hg : h ∘ g = g₁ ∘ g₂) (hfg : range f ∪ range g = univ) (s : Set β) :
    h '' s = f₁ '' (f₂ '' (f ⁻¹' s)) ∪ g₁ '' (g₂ '' (g ⁻¹' s)) := by
  rw [← image_comp, ← image_comp, ← hf, ← hg, image_comp, image_comp, image_preimage_eq_inter_range,
    image_preimage_eq_inter_range, ← image_union, ← inter_union_distrib_left, hfg, inter_univ]

end Range

section Subsingleton

variable {s : Set α} {f : α → β}

/-- The image of a subsingleton is a subsingleton. -/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α → β) : (f '' s).Subsingleton :=
  fun _ ⟨_, hx, Hx⟩ _ ⟨_, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton)
    (hf : Function.Injective f) : (f ⁻¹' s).Subsingleton := fun _ ha _ hb => hf <| hs ha hb

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
theorem subsingleton_of_image (hf : Function.Injective f) (s : Set α)
    (hs : (f '' s).Subsingleton) : s.Subsingleton :=
  (hs.preimage hf).anti <| subset_preimage_image _ _

/-- If the preimage of a set under a surjective map is a subsingleton,
the set is a subsingleton. -/
theorem subsingleton_of_preimage (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)

theorem subsingleton_range {α : Sort*} [Subsingleton α] (f : α → β) : (range f).Subsingleton :=
  forall_mem_range.2 fun x => forall_mem_range.2 fun y => congr_arg f (Subsingleton.elim x y)

/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial)
    (hf : Function.Surjective f) : (f ⁻¹' s).Nontrivial := by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

/-- The image of a nontrivial set under an injective map is nontrivial. -/
theorem Nontrivial.image (hs : s.Nontrivial) (hf : Function.Injective f) :
    (f '' s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩

theorem Nontrivial.image_of_injOn (hs : s.Nontrivial) (hf : s.InjOn f) :
    (f '' s).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

/-- If the image of a set is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_image (f : α → β) (s : Set α) (hs : (f '' s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

@[simp]
theorem image_nontrivial (hf : f.Injective) : (f '' s).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image f s, fun h ↦ h.image hf⟩

@[simp]
theorem InjOn.image_nontrivial_iff (hf : s.InjOn f) :
    (f '' s).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image f s, fun h ↦ h.image_of_injOn hf⟩

/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_preimage (hf : Function.Injective f) (s : Set β)
    (hs : (f ⁻¹' s).Nontrivial) : s.Nontrivial :=
  (hs.image hf).mono <| image_preimage_subset _ _

end Subsingleton

end Set

namespace Function

variable {α β : Type*} {ι : Sort*} {f : α → β}

open Set

theorem Surjective.preimage_injective (hf : Surjective f) : Injective (preimage f) := fun _ _ =>
  (preimage_eq_preimage hf).1

theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' (f '' s) = s :=
  preimage_image_eq s hf

theorem Injective.preimage_surjective (hf : Injective f) : Surjective (preimage f) :=
  Set.preimage_surjective.mpr hf

theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} :
    (f '' s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩

theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f '' (f ⁻¹' s) = s :=
  image_preimage_eq s hf

theorem Surjective.image_surjective (hf : Surjective f) : Surjective (image f) := by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]

@[simp]
theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} :
    (f ⁻¹' s).Nonempty ↔ s.Nonempty := by rw [← image_nonempty, hf.image_preimage]

theorem Injective.image_injective (hf : Injective f) : Injective (image f) := by
  intro s t h
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, h]

lemma Injective.image_strictMono (inj : Function.Injective f) : StrictMono (image f) :=
  monotone_image.strictMono_of_injective inj.image_injective

theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  apply Set.preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ

theorem Surjective.range_comp {ι' : Sort*} {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    range (g ∘ f) = range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm

theorem Injective.mem_range_iff_existsUnique (hf : Injective f) {b : β} :
    b ∈ range f ↔ ∃! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun _ ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

alias ⟨Injective.existsUnique_of_mem_range, _⟩ := Injective.mem_range_iff_existsUnique

theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) :
    (f '' s)ᶜ = f '' sᶜ ∪ (range f)ᶜ := by
  grind

theorem LeftInverse.image_image {g : β → α} (h : LeftInverse g f) (s : Set α) :
    g '' (f '' s) = s := by rw [← image_comp, h.comp_eq_id, image_id]

theorem LeftInverse.preimage_preimage {g : β → α} (h : LeftInverse g f) (s : Set α) :
    f ⁻¹' (g ⁻¹' s) = s := by rw [← preimage_comp, h.comp_eq_id, preimage_id]

protected theorem Involutive.preimage {f : α → α} (hf : Involutive f) : Involutive (preimage f) :=
  hf.rightInverse.preimage_preimage

end Function

namespace EquivLike

variable {ι ι' : Sort*} {E : Type*} [EquivLike E ι ι']

@[simp] lemma range_comp {α : Type*} (f : ι' → α) (e : E) : range (f ∘ e) = range f :=
  (EquivLike.surjective _).range_comp _

end EquivLike

/-! ### Image and preimage on subtypes -/


namespace Subtype

variable {α : Type*}

theorem coe_image {p : α → Prop} {s : Set (Subtype p)} :
    (↑) '' s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext fun a =>
    ⟨fun ⟨⟨_, ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : (↑) '' { x : ↥s | ↑x ∈ t } = t := by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨_, hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

theorem range_coe {s : Set α} : range ((↑) : s → α) = s := by
  rw [← image_univ]
  simp [-image_univ, coe_image]

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {s : Set α} : range (Subtype.val : s → α) = s :=
  range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : Set α` the function `(↑) : s → α`, then the inferred implicit arguments of `(↑)` are
  `↑α (fun x ↦ x ∈ s)`. -/
@[simp]
theorem range_coe_subtype {p : α → Prop} : range ((↑) : Subtype p → α) = { x | p x } :=
  range_coe

@[simp]
theorem coe_preimage_self (s : Set α) : ((↑) : s → α) ⁻¹' s = univ := by
  rw [← preimage_range, range_coe]

theorem range_val_subtype {p : α → Prop} : range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe

theorem coe_image_subset (s : Set α) (t : Set s) : ((↑) : s → α) '' t ⊆ s :=
  fun x ⟨y, _, yvaleq⟩ => by
  rw [← yvaleq]; exact y.property

theorem coe_image_univ (s : Set α) : ((↑) : s → α) '' Set.univ = s :=
  image_univ.trans range_coe

@[simp]
theorem image_preimage_coe (s t : Set α) : ((↑) : s → α) '' (((↑) : s → α) ⁻¹' t) = s ∩ t :=
  image_preimage_eq_range_inter.trans <| congr_arg (· ∩ t) range_coe

theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) '' (Subtype.val ⁻¹' t) = s ∩ t :=
  image_preimage_coe s t

theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} :
    ((↑) : s → α) ⁻¹' t = ((↑) : s → α) ⁻¹' u ↔ s ∩ t = s ∩ u := by
  rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]

theorem preimage_coe_self_inter (s t : Set α) :
    ((↑) : s → α) ⁻¹' (s ∩ t) = ((↑) : s → α) ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff, ← inter_assoc, inter_self]

-- Not `@[simp]` since `simp` can prove this.
theorem preimage_coe_inter_self (s t : Set α) :
    ((↑) : s → α) ⁻¹' (t ∩ s) = ((↑) : s → α) ⁻¹' t := by
  rw [inter_comm, preimage_coe_self_inter]

theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ s ∩ t = s ∩ u :=
  preimage_coe_eq_preimage_coe_iff

lemma preimage_val_subset_preimage_val_iff (s t u : Set α) :
    (Subtype.val ⁻¹' t : Set s) ⊆ Subtype.val ⁻¹' u ↔ s ∩ t ⊆ s ∩ u := by
  constructor
  · rw [← image_preimage_coe, ← image_preimage_coe]
    exact image_mono
  · intro h x a
    exact (h ⟨x.2, a⟩).2

theorem exists_set_subtype {t : Set α} (p : Set α → Prop) :
    (∃ s : Set t, p (((↑) : t → α) '' s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s := by
  rw [← exists_subset_range_and_iff, range_coe]

theorem forall_set_subtype {t : Set α} (p : Set α → Prop) :
    (∀ s : Set t, p (((↑) : t → α) '' s)) ↔ ∀ s : Set α, s ⊆ t → p s := by
  rw [← forall_subset_range_iff, range_coe]

theorem preimage_coe_nonempty {s t : Set α} :
    (((↑) : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty := by
  rw [← image_preimage_coe, image_nonempty]

theorem preimage_coe_eq_empty {s t : Set α} : ((↑) : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

-- Not `@[simp]` since `simp` can prove this.
theorem preimage_coe_compl (s : Set α) : ((↑) : s → α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]
theorem preimage_coe_compl' (s : Set α) :
    (fun x : (sᶜ : Set α) => (x : α)) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)

end Subtype

/-! ### Images and preimages on `Option` -/


namespace Option

theorem injective_iff {α β} {f : Option α → β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some) := by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine
    ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne <| Option.some_ne_none _⟩, ?_⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts [rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]

theorem range_eq {α β} (f : Option α → β) : range f = insert (f none) (range (f ∘ some)) :=
  Set.ext fun _ => Option.exists.trans <| eq_comm.or Iff.rfl

/-- The range of `Option.elim b f` is `{b} ∪ range f`. -/
theorem range_elim {α β} (b : β) (f : α → β) :
    range (fun o : Option α => o.elim b f) = insert b (range f) := by
  rw [range_eq]
  simp [Function.comp_def]

/-- The image of `range some` under `Option.elim b f` equals `range f`. -/
theorem image_elim_range_some_eq_range {α β} (f : α → β) (b : β) :
    (fun o : Option α => o.elim b f) '' range some = range f := by
  rw [← range_comp']
  simp

end Option

namespace Set

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

@[simp]
theorem image_surjective : Surjective (image f) ↔ Surjective f := by
  refine ⟨fun h y => ?_, Surjective.image_surjective⟩
  rcases h {y} with ⟨s, hs⟩
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

@[simp]
theorem image_injective : Injective (image f) ↔ Injective f := by
  refine ⟨fun h x x' hx => ?_, Injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton, image_singleton, hx]

theorem preimage_eq_iff_eq_image {f : α → β} (hf : Bijective f) {s t} :
    f ⁻¹' s = t ↔ s = f '' t := by rw [← image_eq_image hf.1, hf.2.image_preimage]

theorem eq_preimage_iff_image_eq {f : α → β} (hf : Bijective f) {s t} :
    s = f ⁻¹' t ↔ f '' s = t := by rw [← image_eq_image hf.1, hf.2.image_preimage]

end ImagePreimage

end Set

/-! ### Disjoint lemmas for image and preimage -/

section Disjoint
variable {α β γ : Type*} {f : α → β} {s t : Set α}

theorem Disjoint.preimage (f : α → β) {s t : Set β} (h : Disjoint s t) :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) :=
  disjoint_iff_inf_le.mpr fun _ hx => h.le_bot hx

lemma Codisjoint.preimage (f : α → β) {s t : Set β} (h : Codisjoint s t) :
    Codisjoint (f ⁻¹' s) (f ⁻¹' t) := by
  simp only [codisjoint_iff_le_sup, Set.sup_eq_union, top_le_iff, ← Set.preimage_union] at h ⊢
  rw [h]; rfl

lemma IsCompl.preimage (f : α → β) {s t : Set β} (h : IsCompl s t) :
    IsCompl (f ⁻¹' s) (f ⁻¹' t) :=
  ⟨h.1.preimage f, h.2.preimage f⟩

namespace Set

theorem disjoint_image_image {f : β → α} {g : γ → α} {s : Set β} {t : Set γ}
    (h : ∀ b ∈ s, ∀ c ∈ t, f b ≠ g c) : Disjoint (f '' s) (g '' t) :=
  disjoint_iff_inf_le.mpr <| by rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩; exact h b hb c hc eq

theorem disjoint_image_of_injective (hf : Injective f) {s t : Set α} (hd : Disjoint s t) :
    Disjoint (f '' s) (f '' t) :=
  disjoint_image_image fun _ hx _ hy => hf.ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩

theorem _root_.Disjoint.of_image (h : Disjoint (f '' s) (f '' t)) : Disjoint s t :=
  disjoint_iff_inf_le.mpr fun _ hx =>
    disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)

@[simp]
theorem disjoint_image_iff (hf : Injective f) : Disjoint (f '' s) (f '' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩

theorem _root_.Disjoint.of_preimage (hf : Surjective f) {s t : Set β}
    (h : Disjoint (f ⁻¹' s) (f ⁻¹' t)) : Disjoint s t := by
  rw [disjoint_iff_inter_eq_empty, ← image_preimage_eq (_ ∩ _) hf, preimage_inter, h.inter_eq,
    image_empty]

@[simp]
theorem disjoint_preimage_iff (hf : Surjective f) {s t : Set β} :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩

theorem preimage_eq_empty {s : Set β} (h : Disjoint s (range f)) :
    f ⁻¹' s = ∅ := by
  simpa using h.preimage f

theorem preimage_eq_empty_iff {s : Set β} : f ⁻¹' s = ∅ ↔ Disjoint s (range f) :=
  ⟨fun h => by
    simp only [eq_empty_iff_forall_notMem, disjoint_iff_inter_eq_empty, mem_preimage] at h ⊢
    grind,
  preimage_eq_empty⟩

@[simp]
theorem disjoint_image_inl_image_inr {u : Set α} {v : Set β} :
    Disjoint (Sum.inl '' u) (Sum.inr '' v) :=
  disjoint_image_image <| by simp

@[simp]
theorem disjoint_range_inl_image_inr {v : Set β} :
    Disjoint (α := Set (α ⊕ β)) (range Sum.inl) (Sum.inr '' v) := by
  grind

@[simp]
theorem disjoint_image_inl_range_inr {u : Set α} :
    Disjoint (α := Set (α ⊕ β)) (Sum.inl '' u) (range Sum.inr) := by
  grind

end Set

end Disjoint

section Sigma

variable {α : Type*} {β : α → Type*} {i j : α} {s : Set (β i)}

lemma sigma_mk_preimage_image' (h : i ≠ j) : Sigma.mk j ⁻¹' (Sigma.mk i '' s) = ∅ := by
  simp [image, h]

lemma sigma_mk_preimage_image_eq_self : Sigma.mk i ⁻¹' (Sigma.mk i '' s) = s := by
  simp [image]

end Sigma

namespace Quot

variable {α : Type*} {r : α → α → Prop}

theorem range_toSet_eq_range_equivClassOf :
    range (toSet (r := r)) = range (equivClassOf (r := r)) :=
  lift_equivClassOf_eq_toSet ▸ range_quot_lift _

theorem mk_preimage_singleton_eq_toSet (q : Quot r) : Quot.mk _ ⁻¹' {q} = toSet q := by
  ext
  grind

end Quot

namespace Quotient

variable {α : Type*} {s : Setoid α}

theorem range_toSet_eq_range_equivClassOf :
    range (toSet (s := s)) = range (equivClassOf (s := s)) :=
  lift_equivClassOf_eq_toSet ▸ range_quotient_lift _

theorem mk_preimage_singleton_eq_toSet (q : Quotient s) : Quotient.mk _ ⁻¹' {q} = toSet q := by
  ext
  grind

end Quotient
