/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Set.Sigma

#align_import data.finset.sigma from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Finite sets in a sigma type

This file defines a few `Finset` constructions on `Σ i, α i`.

## Main declarations

* `Finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
* `Finset.sigmaLift`: Lifts maps `α i → β i → Finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → Finset (Σ i, γ i)`.

## TODO

`Finset.sigmaLift` can be generalized to any alternative functor. But to make the generalization
worth it, we must first refactor the functor library so that the `alternative` instance for `Finset`
is computable and universe-polymorphic.
-/


open Function Multiset

variable {ι : Type*}

namespace Finset

section Sigma

variable {α : ι → Type*} {β : Type*} (s s₁ s₂ : Finset ι) (t t₁ t₂ : ∀ i, Finset (α i))

/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
protected def sigma : Finset (Σi, α i) :=
  ⟨_, s.nodup.sigma fun i => (t i).nodup⟩
#align finset.sigma Finset.sigma

variable {s s₁ s₂ t t₁ t₂}

@[simp]
theorem mem_sigma {a : Σi, α i} : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 :=
  Multiset.mem_sigma
#align finset.mem_sigma Finset.mem_sigma

@[simp, norm_cast]
theorem coe_sigma (s : Finset ι) (t : ∀ i, Finset (α i)) :
    (s.sigma t : Set (Σ i, α i)) = (s : Set ι).sigma fun i ↦ (t i : Set (α i)) :=
  Set.ext fun _ => mem_sigma
#align finset.coe_sigma Finset.coe_sigma

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem sigma_nonempty : (s.sigma t).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty := by simp [Finset.Nonempty]
#align finset.sigma_nonempty Finset.sigma_nonempty

@[simp]
theorem sigma_eq_empty : s.sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ := by
  simp only [← not_nonempty_iff_eq_empty, sigma_nonempty, not_exists, not_and]
#align finset.sigma_eq_empty Finset.sigma_eq_empty

@[mono]
theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
  fun ⟨i, _⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩
#align finset.sigma_mono Finset.sigma_mono

theorem pairwiseDisjoint_map_sigmaMk :
    (s : Set ι).PairwiseDisjoint fun i => (t i).map (Embedding.sigmaMk i) := by
  intro i _ j _ hij
  rw [Function.onFun, disjoint_left]
  simp_rw [mem_map, Function.Embedding.sigmaMk_apply]
  rintro _ ⟨y, _, rfl⟩ ⟨z, _, hz'⟩
  exact hij (congr_arg Sigma.fst hz'.symm)
#align finset.pairwise_disjoint_map_sigma_mk Finset.pairwiseDisjoint_map_sigmaMk

@[simp]
theorem disjiUnion_map_sigma_mk :
    s.disjiUnion (fun i => (t i).map (Embedding.sigmaMk i)) pairwiseDisjoint_map_sigmaMk =
      s.sigma t :=
  rfl
#align finset.disj_Union_map_sigma_mk Finset.disjiUnion_map_sigma_mk

theorem sigma_eq_biUnion [DecidableEq (Σi, α i)] (s : Finset ι) (t : ∀ i, Finset (α i)) :
    s.sigma t = s.biUnion fun i => (t i).map <| Embedding.sigmaMk i := by
  ext ⟨x, y⟩
  simp [and_left_comm]
#align finset.sigma_eq_bUnion Finset.sigma_eq_biUnion

variable (s t) (f : (Σi, α i) → β)

theorem sup_sigma [SemilatticeSup β] [OrderBot β] :
    (s.sigma t).sup f = s.sup fun i => (t i).sup fun b => f ⟨i, b⟩ := by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_sigma, and_imp, Sigma.forall]
  exact
    ⟨fun i a hi ha => (le_sup hi).trans' <| le_sup (f := fun a => f ⟨i, a⟩) ha, fun i hi a ha =>
      le_sup <| mem_sigma.2 ⟨hi, ha⟩⟩
#align finset.sup_sigma Finset.sup_sigma

theorem inf_sigma [SemilatticeInf β] [OrderTop β] :
    (s.sigma t).inf f = s.inf fun i => (t i).inf fun b => f ⟨i, b⟩ :=
  @sup_sigma _ _ βᵒᵈ _ _ _ _ _
#align finset.inf_sigma Finset.inf_sigma

theorem _root_.biSup_finsetSigma [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → β) : ⨆ ij ∈ s.sigma t, f ij = ⨆ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ := by
  simp_rw [← Finset.iSup_coe, Finset.coe_sigma, biSup_sigma]

theorem _root_.biSup_finsetSigma' [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) : ⨆ (i ∈ s) (j ∈ t i), f i j = ⨆ ij ∈ s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biSup_finsetSigma _ _ _)

theorem _root_.biInf_finsetSigma [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → β) : ⨅ ij ∈ s.sigma t, f ij = ⨅ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ :=
  biSup_finsetSigma (β := βᵒᵈ) _ _ _

theorem _root_.biInf_finsetSigma' [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) : ⨅ (i ∈ s) (j ∈ t i), f i j = ⨅ ij ∈ s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biInf_finsetSigma _ _ _)

theorem _root_.Set.biUnion_finsetSigma (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → Set β) : ⋃ ij ∈ s.sigma t, f ij = ⋃ i ∈ s, ⋃ j ∈ t i, f ⟨i, j⟩ :=
  biSup_finsetSigma _ _ _

theorem _root_.Set.biUnion_finsetSigma' (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → Set β) : ⋃ i ∈ s, ⋃ j ∈ t i, f i j = ⋃ ij ∈ s.sigma t, f ij.fst ij.snd :=
  biSup_finsetSigma' _ _ _

theorem _root_.Set.biInter_finsetSigma (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → Set β) : ⋂ ij ∈ s.sigma t, f ij = ⋂ i ∈ s, ⋂ j ∈ t i, f ⟨i, j⟩ :=
  biInf_finsetSigma _ _ _

theorem _root_.Set.biInter_finsetSigma' (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : ∀ i, α i → Set β) : ⋂ i ∈ s, ⋂ j ∈ t i, f i j = ⋂ ij ∈ s.sigma t, f ij.1 ij.2 :=
  biInf_finsetSigma' _ _ _

end Sigma

section SigmaLift

variable {α β γ : ι → Type*} [DecidableEq ι]

/-- Lifts maps `α i → β i → Finset (γ i)` to a map `Σ i, α i → Σ i, β i → Finset (Σ i, γ i)`. -/
def sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β) :
    Finset (Sigma γ) :=
  dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅
#align finset.sigma_lift Finset.sigmaLift

theorem mem_sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β)
    (x : Sigma γ) :
    x ∈ sigmaLift f a b ↔ ∃ (ha : a.1 = x.1) (hb : b.1 = x.1), x.2 ∈ f (ha ▸ a.2) (hb ▸ b.2) := by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigmaLift]
      simp only [dite_eq_ite, ite_true, mem_map, Embedding.sigmaMk_apply, forall_exists_index,
        and_imp]
      rintro x hx rfl
      exact ⟨rfl, rfl, hx⟩
    · rintro ⟨⟨⟩, ⟨⟩, hx⟩
      rw [sigmaLift, dif_pos rfl, mem_map]
      exact ⟨_, hx, by simp [Sigma.ext_iff]⟩
  · rw [sigmaLift, dif_neg h]
    refine iff_of_false (not_mem_empty _) ?_
    rintro ⟨⟨⟩, ⟨⟩, _⟩
    exact h rfl
#align finset.mem_sigma_lift Finset.mem_sigmaLift

theorem mk_mem_sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (i : ι) (a : α i) (b : β i)
    (x : γ i) : (⟨i, x⟩ : Sigma γ) ∈ sigmaLift f ⟨i, a⟩ ⟨i, b⟩ ↔ x ∈ f a b := by
  rw [sigmaLift, dif_pos rfl, mem_map]
  refine ⟨?_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx
#align finset.mk_mem_sigma_lift Finset.mk_mem_sigmaLift

theorem not_mem_sigmaLift_of_ne_left (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α)
    (b : Sigma β) (x : Sigma γ) (h : a.1 ≠ x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigmaLift]
  exact fun H => h H.fst
#align finset.not_mem_sigma_lift_of_ne_left Finset.not_mem_sigmaLift_of_ne_left

theorem not_mem_sigmaLift_of_ne_right (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) {a : Sigma α}
    (b : Sigma β) {x : Sigma γ} (h : b.1 ≠ x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigmaLift]
  exact fun H => h H.snd.fst
#align finset.not_mem_sigma_lift_of_ne_right Finset.not_mem_sigmaLift_of_ne_right

variable {f g : ∀ ⦃i⦄, α i → β i → Finset (γ i)} {a : Σi, α i} {b : Σi, β i}

theorem sigmaLift_nonempty :
    (sigmaLift f a b).Nonempty ↔ ∃ h : a.1 = b.1, (f (h ▸ a.2) b.2).Nonempty := by
  simp_rw [nonempty_iff_ne_empty, sigmaLift]
  split_ifs with h <;> simp [h]
#align finset.sigma_lift_nonempty Finset.sigmaLift_nonempty

theorem sigmaLift_eq_empty : sigmaLift f a b = ∅ ↔ ∀ h : a.1 = b.1, f (h ▸ a.2) b.2 = ∅ := by
  simp_rw [sigmaLift]
  split_ifs with h
  · simp [h, forall_prop_of_true h]
  · simp [h, forall_prop_of_false h]
#align finset.sigma_lift_eq_empty Finset.sigmaLift_eq_empty

theorem sigmaLift_mono (h : ∀ ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b ⊆ g a b) (a : Σi, α i) (b : Σi, β i) :
    sigmaLift f a b ⊆ sigmaLift g a b := by
  rintro x hx
  rw [mem_sigmaLift] at hx ⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩
#align finset.sigma_lift_mono Finset.sigmaLift_mono

variable (f a b)

theorem card_sigmaLift :
    (sigmaLift f a b).card = dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0 := by
  simp_rw [sigmaLift]
  split_ifs with h <;> simp [h]
#align finset.card_sigma_lift Finset.card_sigmaLift

end SigmaLift

end Finset
