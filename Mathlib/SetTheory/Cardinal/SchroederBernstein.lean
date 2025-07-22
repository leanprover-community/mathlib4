/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Piecewise
import Mathlib.Order.FixedPoints
import Mathlib.Order.Zorn

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

universe u v

namespace Function

namespace Embedding

section antisymm

variable {α : Type u} {β : Type v}

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`. -/
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : α → β, Bijective h := by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty α := Function.isEmpty f
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective⟩
  set F : Set α →o Set α :=
    { toFun := fun s => (g '' (f '' s)ᶜ)ᶜ
      monotone' := fun s t hst => by dsimp at hst ⊢; gcongr }
  set s : Set α := F.lfp
  have hs : (g '' (f '' s)ᶜ)ᶜ = s := F.map_lfp
  have hns : g '' (f '' s)ᶜ = sᶜ := compl_injective (by simp [hs])
  set g' := invFun g
  have g'g : LeftInverse g' g := leftInverse_invFun hg
  have hg'ns : g' '' sᶜ = (f '' s)ᶜ := by rw [← hns, g'g.image_image]
  set h : α → β := s.piecewise f g'
  have : Surjective h := by rw [← range_eq_univ, range_piecewise, hg'ns, union_compl_self]
  have : Injective h := by
    refine (injective_piecewise_iff _).2 ⟨hf.injOn, ?_, ?_⟩
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

/-- **The Schröder-Bernstein Theorem**: Given embeddings `α ↪ β` and `β ↪ α`, there exists an
equivalence `α ≃ β`. -/
theorem antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β)
  | ⟨_, h₁⟩, ⟨_, h₂⟩ =>
    let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂
    ⟨Equiv.ofBijective f hf⟩

end antisymm

section Wo

variable {ι : Type u} (β : ι → Type v)

/-- `sets β` -/
private abbrev sets :=
  { s : Set (∀ i, β i) | ∀ i : ι, s.InjOn fun x => x i }

/-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
there is an element that injects into the others.
See `Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice instances. -/
theorem min_injective [I : Nonempty ι] : ∃ i, Nonempty (∀ j, β i ↪ β j) :=
  let ⟨s, hs⟩ := show ∃ s, Maximal (· ∈ sets β) s by
    refine zorn_subset _ fun c hc hcc ↦
      ⟨⋃₀ c, fun i x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ hi ↦ ?_, fun _ ↦ subset_sUnion_of_mem⟩
    exact (hcc.total hpc hqc).elim (fun h ↦ hc hqc i (h hxp) hyq hi)
      fun h ↦ hc hpc i hxp (h hyq) hi
  let ⟨i, e⟩ :=
    show ∃ i, Surjective fun x : s => x.val i from
      Classical.by_contradiction fun h =>
        have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y := by
          simpa [Surjective] using h
        let ⟨f, hf⟩ := Classical.axiom_of_choice h
        have : f ∈ s :=
          have : insert f s ∈ sets β := fun i x hx y hy => by
            rcases hx with hx | hx <;> rcases hy with hy | hy; · simp [hx, hy]
            · subst x
              exact fun e => (hf i y hy e.symm).elim
            · subst y
              exact fun e => (hf i x hx e).elim
            · exact hs.prop i hx hy
          hs.eq_of_subset this (subset_insert _ _) ▸ mem_insert ..
        let ⟨i⟩ := I
        hf i f this rfl
  ⟨i, ⟨fun j => ⟨s.restrict (fun x => x j) ∘ surjInv e,
    ((hs.1 j).injective).comp (injective_surjInv _)⟩⟩⟩

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

end Embedding

end Function
