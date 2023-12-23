/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Defs
import Mathlib.Logic.Equiv.Set

#align_import logic.small.basic from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Instances and theorems for `Small`.

In particular we prove `small_of_injective` and `small_of_surjective`.
-/

set_option autoImplicit true


universe u w v v'

section

open Classical

instance small_subtype (α : Type v) [Small.{w} α] (P : α → Prop) : Small.{w} { x // P x } :=
  small_map (equivShrink α).subtypeEquivOfSubtype'
#align small_subtype small_subtype

theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α → β}
    (hf : Function.Injective f) : Small.{u} α :=
  small_map (Equiv.ofInjective f hf)
#align small_of_injective small_of_injective

theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α → β}
    (hf : Function.Surjective f) : Small.{u} β :=
  small_of_injective (Function.injective_surjInv hf)
#align small_of_surjective small_of_surjective

theorem small_subset {α : Type v} {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  let f : t → s := fun x => ⟨x, hts x.prop⟩
  @small_of_injective _ _ _ f fun _ _ hxy => Subtype.ext (Subtype.mk.inj hxy)
#align small_subset small_subset

instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α := by
  rcases isEmpty_or_nonempty α with ⟨⟩ <;> skip
  · apply small_map (Equiv.equivPEmpty α)
  · apply small_map Equiv.punitOfNonemptyOfSubsingleton
#align small_subsingleton small_subsingleton

/-- This can be seen as a version of `small_of_surjective` in which the function `f` doesn't
    actually land in `β` but in some larger type `γ` related to `β` via an injective function `g`.
    -/
theorem small_of_injective_of_exists {α : Type v} {β : Type w} {γ : Type v'} [Small.{u} α]
    (f : α → γ) {g : β → γ} (hg : Function.Injective g) (h : ∀ b : β, ∃ a : α, f a = g b) :
    Small.{u} β := by
  by_cases hβ : Nonempty β
  · refine' small_of_surjective (f := Function.invFun g ∘ f) (fun b => _)
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [Function.comp_apply, ha, Function.leftInverse_invFun hg]⟩
  · simp only [not_nonempty_iff] at hβ
    infer_instance

/-!
We don't define `small_of_fintype` or `small_of_countable` in this file,
to keep imports to `Logic` to a minimum.
-/

instance small_Pi {α} (β : α → Type*) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (∀ a, β a) :=
  ⟨⟨∀ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩
#align small_Pi small_Pi

instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩
#align small_prod small_prod

instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (Sum α β) :=
  ⟨⟨Sum (Shrink α) (Shrink β), ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩
#align small_sum small_sum

instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩
#align small_set small_set

instance small_range {α : Type v} {β : Type w} (f : α → β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.surjective_onto_range
#align small_range small_range

instance small_image {α : Type v} {β : Type w} (f : α → β) (S : Set α) [Small.{u} S] :
    Small.{u} (f '' S) :=
  small_of_surjective Set.surjective_onto_image
#align small_image small_image

end
