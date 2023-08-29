/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Order.FixedPoints
import Mathlib.Order.Zorn

#align_import set_theory.cardinal.schroeder_bernstein from "leanprover-community/mathlib"@"1e05171a5e8cf18d98d9cf7b207540acb044acae"

/-!
# Schröder-Bernstein theorem, well-ordering of cardinals

This file proves the Schröder-Bernstein theorem (see `schroeder_bernstein`), the well-ordering of
cardinals (see `min_injective`) and the totality of their order (see `total`).

## Notes

Cardinals are naturally ordered by `α ≤ β ↔ ∃ f : a → β, Injective f`:
* `schroeder_bernstein` states that, given injections `α → β` and `β → α`, one can get a
  bijection `α → β`. This corresponds to the antisymmetry of the order.
* The order is also well-founded: any nonempty set of cardinals has a minimal element.
  `min_injective` states that by saying that there exists an element of the set that injects into
  all others.

Cardinals are defined and further developed in the folder `SetTheory.Cardinal`.
-/


open Set Function

open Classical

universe u v

namespace Function

namespace Embedding

section antisymm

variable {α : Type u} {β : Type v}

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`. -/
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : α → β, Bijective h := by
  cases' isEmpty_or_nonempty β with hβ hβ
  -- ⊢ ∃ h, Bijective h
  · have : IsEmpty α := Function.isEmpty f
    -- ⊢ ∃ h, Bijective h
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective⟩
    -- 🎉 no goals
  set F : Set α →o Set α :=
    { toFun := fun s => (g '' (f '' s)ᶜ)ᶜ
      monotone' := fun s t hst =>
        compl_subset_compl.mpr <| image_subset _ <| compl_subset_compl.mpr <| image_subset _ hst }
  -- Porting note: dot notation `F.lfp` doesn't work here
  set s : Set α := OrderHom.lfp F
  -- ⊢ ∃ h, Bijective h
  have hs : (g '' (f '' s)ᶜ)ᶜ = s := F.map_lfp
  -- ⊢ ∃ h, Bijective h
  have hns : g '' (f '' s)ᶜ = sᶜ := compl_injective (by simp [hs])
  -- ⊢ ∃ h, Bijective h
  set g' := invFun g
  -- ⊢ ∃ h, Bijective h
  have g'g : LeftInverse g' g := leftInverse_invFun hg
  -- ⊢ ∃ h, Bijective h
  have hg'ns : g' '' sᶜ = (f '' s)ᶜ := by rw [← hns, g'g.image_image]
  -- ⊢ ∃ h, Bijective h
  set h : α → β := s.piecewise f g'
  -- ⊢ ∃ h, Bijective h
  have : Surjective h := by rw [← range_iff_surjective, range_piecewise, hg'ns, union_compl_self]
  -- ⊢ ∃ h, Bijective h
  have : Injective h := by
    refine' (injective_piecewise_iff _).2 ⟨hf.injOn _, _, _⟩
    · intro x hx y hy hxy
      obtain ⟨x', _, rfl⟩ : x ∈ g '' (f '' s)ᶜ := by rwa [hns]
      obtain ⟨y', _, rfl⟩ : y ∈ g '' (f '' s)ᶜ := by rwa [hns]
      rw [g'g _, g'g _] at hxy
      rw [hxy]
    · intro x hx y hy hxy
      obtain ⟨y', hy', rfl⟩ : y ∈ g '' (f '' s)ᶜ := by rwa [hns]
      rw [g'g _] at hxy
      exact hy' ⟨x, hx, hxy⟩
  exact ⟨h, ‹Injective h›, ‹Surjective h›⟩
  -- 🎉 no goals
#align function.embedding.schroeder_bernstein Function.Embedding.schroeder_bernstein

/-- **The Schröder-Bernstein Theorem**: Given embeddings `α ↪ β` and `β ↪ α`, there exists an
equivalence `α ≃ β`. -/
theorem antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β)
  | ⟨_, h₁⟩, ⟨_, h₂⟩ =>
    let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂
    ⟨Equiv.ofBijective f hf⟩
#align function.embedding.antisymm Function.Embedding.antisymm

end antisymm

section Wo

variable {ι : Type u} (β : ι → Type v)

/-- `sets β` -/
@[reducible]
private def sets :=
  { s : Set (∀ i, β i) | ∀ x ∈ s, ∀ y ∈ s, ∀ (i), (x : ∀ i, β i) i = y i → x = y }

/-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
there is an element that injects into the others.
See `Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice instances. -/
theorem min_injective [I : Nonempty ι] : ∃ i, Nonempty (∀ j, β i ↪ β j) :=
  let ⟨s, hs, ms⟩ :=
    show ∃ s ∈ sets β, ∀ a ∈ sets β, s ⊆ a → a = s from
      zorn_subset (sets β) fun c hc hcc =>
        ⟨⋃₀c, fun x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ i hi =>
          (hcc.total hpc hqc).elim (fun h => hc hqc x (h hxp) y hyq i hi) fun h =>
            hc hpc x hxp y (h hyq) i hi,
          fun _ => subset_sUnion_of_mem⟩
  let ⟨i, e⟩ :=
    show ∃ i, ∀ y, ∃ x ∈ s, (x : ∀ i, β i) i = y from
      Classical.by_contradiction fun h =>
        have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y := by
          simpa only [ne_eq, not_exists, not_forall, not_and] using h
          -- 🎉 no goals
        let ⟨f, hf⟩ := Classical.axiom_of_choice h
        have : f ∈ s :=
          have : insert f s ∈ sets β := fun x hx y hy => by
            cases' hx with hx hx <;> cases' hy with hy hy; · simp [hx, hy]
            -- ⊢ ∀ (i : ι), x i = y i → x = y
                                     -- ⊢ ∀ (i : ι), x i = y i → x = y
                                     -- ⊢ ∀ (i : ι), x i = y i → x = y
                                                             -- 🎉 no goals
            · subst x
              -- ⊢ ∀ (i : ι), f i = y i → f = y
              exact fun i e => (hf i y hy e.symm).elim
              -- 🎉 no goals
            · subst y
              -- ⊢ ∀ (i : ι), x i = f i → x = f
              exact fun i e => (hf i x hx e).elim
              -- 🎉 no goals
            · exact hs x hx y hy
              -- 🎉 no goals
          ms _ this (subset_insert f s) ▸ mem_insert _ _
        let ⟨i⟩ := I
        hf i f this rfl
  let ⟨f, hf⟩ := Classical.axiom_of_choice e
  ⟨i,
    ⟨fun j =>
      ⟨fun a => f a j, fun a b e' => by
        let ⟨sa, ea⟩ := hf a
        -- ⊢ a = b
        let ⟨sb, eb⟩ := hf b
        -- ⊢ a = b
        rw [← ea, ← eb, hs _ sa _ sb _ e']⟩⟩⟩
        -- 🎉 no goals
#align function.embedding.min_injective Function.Embedding.min_injective

end Wo

/-- The cardinals are totally ordered. See
`Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice
instance. -/
-- Porting note: `ULift.{max u v, u} α` was `ULift α`
theorem total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) :=
  match @min_injective Bool (fun b => cond b (ULift.{max u v, u} α) (ULift.{max u v, v} β)) ⟨true⟩
    with
  | ⟨true, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h false
    Or.inl ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨false, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h true
    Or.inr ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
#align function.embedding.total Function.Embedding.total

end Embedding

end Function
