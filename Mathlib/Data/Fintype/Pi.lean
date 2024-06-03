/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Basic

#align_import data.fintype.pi from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Fintype instances for pi types
-/


variable {α : Type*}

open Finset

namespace Fintype

variable [DecidableEq α] [Fintype α] {γ δ : α → Type*} {s : ∀ a, Finset (γ a)}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `Fintype.piFinset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `Finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ Finset.univ` in the `Finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp (config := {contextual := true}) [Function.funext_iff]⟩
#align fintype.pi_finset Fintype.piFinset

@[simp]
theorem mem_piFinset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a := by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩
#align fintype.mem_pi_finset Fintype.mem_piFinset

@[simp]
theorem coe_piFinset (t : ∀ a, Finset (δ a)) :
    (piFinset t : Set (∀ a, δ a)) = Set.pi Set.univ fun a => t a :=
  Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset
#align fintype.coe_pi_finset Fintype.coe_piFinset

theorem piFinset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
    piFinset t₁ ⊆ piFinset t₂ := fun _ hg => mem_piFinset.2 fun a => h a <| mem_piFinset.1 hg a
#align fintype.pi_finset_subset Fintype.piFinset_subset

@[simp]
theorem piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : ∀ i, Finset (δ i)) = ∅ :=
  eq_empty_of_forall_not_mem fun _ => by simp
#align fintype.pi_finset_empty Fintype.piFinset_empty

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
lemma piFinset_nonempty : (piFinset s).Nonempty ↔ ∀ a, (s a).Nonempty := by
  simp [Finset.Nonempty, Classical.skolem]

@[simp]
lemma piFinset_of_isEmpty [IsEmpty α] (s : ∀ a, Finset (γ a)) : piFinset s = univ :=
  eq_univ_of_forall fun _ ↦ by simp

@[simp]
theorem piFinset_singleton (f : ∀ i, δ i) : piFinset (fun i => {f i} : ∀ i, Finset (δ i)) = {f} :=
  ext fun _ => by simp only [Function.funext_iff, Fintype.mem_piFinset, mem_singleton]
#align fintype.pi_finset_singleton Fintype.piFinset_singleton

theorem piFinset_subsingleton {f : ∀ i, Finset (δ i)} (hf : ∀ i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (∀ i, δ i)).Subsingleton := fun _ ha _ hb =>
  funext fun _ => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)
#align fintype.pi_finset_subsingleton Fintype.piFinset_subsingleton

theorem piFinset_disjoint_of_disjoint (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)
#align fintype.pi_finset_disjoint_of_disjoint Fintype.piFinset_disjoint_of_disjoint

lemma piFinset_image [∀ a, DecidableEq (δ a)] (f : ∀ a, γ a → δ a) (s : ∀ a, Finset (γ a)) :
    piFinset (fun a ↦ (s a).image (f a)) = (piFinset s).image fun b a ↦ f _ (b a) := by
  ext; simp only [mem_piFinset, mem_image, Classical.skolem, forall_and, Function.funext_iff]

lemma eval_image_piFinset_subset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)] :
    ((piFinset t).image fun f ↦ f a) ⊆ t a := image_subset_iff.2 fun _x hx ↦ mem_piFinset.1 hx _

lemma eval_image_piFinset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
    (ht : ∀ b, a ≠ b → (t b).Nonempty) : ((piFinset t).image fun f ↦ f a) = t a := by
  refine (eval_image_piFinset_subset _ _).antisymm fun x h ↦ mem_image.2 ?_
  choose f hf using ht
  exact ⟨fun b ↦ if h : a = b then h ▸ x else f _ h, by aesop, by simp⟩

lemma eval_image_piFinset_const {β} [DecidableEq β] (t : Finset β) (a : α) :
    ((piFinset fun _i : α ↦ t).image fun f ↦ f a) = t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · haveI : Nonempty α := ⟨a⟩
    simp
  · exact eval_image_piFinset (fun _ ↦ t) a fun _ _ ↦ ht

variable [∀ a, DecidableEq (δ a)]

lemma filter_piFinset_of_not_mem (t : ∀ a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a) :
    (piFinset t).filter (· a = x) = ∅ := by
  simp only [filter_eq_empty_iff, mem_piFinset]; rintro f hf rfl; exact hx (hf _)

-- TODO: This proof looks like a good example of something that `aesop` can't do but should
lemma piFinset_update_eq_filter_piFinset_mem (s : ∀ i, Finset (δ i)) (i : α) {t : Finset (δ i)}
    (hts : t ⊆ s i) : piFinset (Function.update s i t) = (piFinset s).filter (fun f ↦ f i ∈ t) := by
  ext f
  simp only [mem_piFinset, mem_filter]
  refine ⟨fun h ↦ ?_, fun h j ↦ ?_⟩
  · have := by simpa using h i
    refine ⟨fun j ↦ ?_, this⟩
    obtain rfl | hji := eq_or_ne j i
    · exact hts this
    · simpa [hji] using h j
  · obtain rfl | hji := eq_or_ne j i
    · simpa using h.2
    · simpa [hji] using h.1 j

lemma piFinset_update_singleton_eq_filter_piFinset_eq (s : ∀ i, Finset (δ i)) (i : α) {a : δ i}
    (ha : a ∈ s i) :
    piFinset (Function.update s i {a}) = (piFinset s).filter (fun f ↦ f i = a) := by
  simp [piFinset_update_eq_filter_piFinset_mem, ha]

end Fintype

/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.fintype {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] : Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩
#align pi.fintype Pi.fintype

@[simp]
theorem Fintype.piFinset_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (∀ a, β a)) :=
  rfl
#align fintype.pi_finset_univ Fintype.piFinset_univ

-- Porting note: this instance used to be computable in Lean3 and used `decidable_eq`, but
-- it makes things a lot harder to work with here. in some ways that was because in Lean3
-- we could make this instance irreducible when needed and in the worst case use `congr/convert`,
-- but those don't work with subsingletons in lean4 as-is so we cannot do this here.
noncomputable instance _root_.Function.Embedding.fintype {α β} [Fintype α] [Fintype β] :
  Fintype (α ↪ β) := by
  classical exact Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)
#align function.embedding.fintype Function.Embedding.fintype

@[simp]
theorem Finset.univ_pi_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ := by
  ext; simp
#align finset.univ_pi_univ Finset.univ_pi_univ
