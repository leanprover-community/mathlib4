/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Sups
import Mathlib.Order.Birkhoff
import Mathlib.Order.Booleanisation
import Mathlib.Order.Sublattice
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# The four functions theorem and corollaries

This file proves the four functions theorem. The statement is that if
`f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)` for all `a`, `b` in a finite distributive lattice, then
`(∑ x ∈ s, f₁ x) * (∑ x ∈ t, f₂ x) ≤ (∑ x ∈ s ⊼ t, f₃ x) * (∑ x ∈ s ⊻ t, f₄ x)` where
`s ⊼ t = {a ⊓ b | a ∈ s, b ∈ t}`, `s ⊻ t = {a ⊔ b | a ∈ s, b ∈ t}`.

The proof uses Birkhoff's representation theorem to restrict to the case where the finite
distributive lattice is in fact a finite powerset algebra, namely `Finset α` for some finite `α`.
Then it proves this new statement by induction on the size of `α`.

## Main declarations

The two versions of the four functions theorem are
* `Finset.four_functions_theorem` for finite powerset algebras.
* `four_functions_theorem` for any finite distributive lattices.

We deduce a number of corollaries:
* `Finset.le_card_infs_mul_card_sups`: Daykin inequality. `|s| |t| ≤ |s ⊼ t| |s ⊻ t|`
* `holley`: Holley inequality.
* `fkg`: Fortuin-Kastelyn-Ginibre inequality.
* `Finset.card_le_card_diffs`: Marica-Schönheim inequality. `|s| ≤ |{a \ b | a, b ∈ s}|`

## TODO

Prove that lattices in which `Finset.le_card_infs_mul_card_sups` holds are distributive. See
Daykin, *A lattice is distributive iff |A| |B| <= |A ∨ B| |A ∧ B|*

Prove the Fishburn-Shepp inequality.

Is `collapse` a construct generally useful for set family inductions? If so, we should move it to an
earlier file and give it a proper API.

## References

[*Applications of the FKG Inequality and Its Relatives*, Graham][Graham1983]
-/

open Finset Fintype Function
open scoped FinsetFamily

variable {α β : Type*}

section Finset
variable [DecidableEq α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {𝒜 : Finset (Finset α)} {a : α} {f f₁ f₂ f₃ f₄ : Finset α → β} {s t u : Finset α}

/-- The `n = 1` case of the Ahlswede-Daykin inequality. Note that we can't just expand everything
out and bound termwise since `c₀ * d₁` appears twice on the RHS of the assumptions while `c₁ * d₀`
does not appear. -/
private lemma ineq [ExistsAddOfLE β] {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : β}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h₀₀ : a₀ * b₀ ≤ c₀ * d₀) (h₁₀ : a₁ * b₀ ≤ c₀ * d₁)
    (h₀₁ : a₀ * b₁ ≤ c₀ * d₁) (h₁₁ : a₁ * b₁ ≤ c₁ * d₁) :
    (a₀ + a₁) * (b₀ + b₁) ≤ (c₀ + c₁) * (d₀ + d₁) := by
  calc
    _ = a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) + a₁ * b₁ := by ring
    _ ≤ c₀ * d₀ + (c₀ * d₁ + c₁ * d₀) + c₁ * d₁ := add_le_add_three h₀₀ ?_ h₁₁
    _ = (c₀ + c₁) * (d₀ + d₁) := by ring
  obtain hcd | hcd := (mul_nonneg hc₀ hd₁).eq_or_lt'
  · rw [hcd] at h₀₁ h₁₀
    rw [h₀₁.antisymm, h₁₀.antisymm, add_zero] <;> positivity
  refine le_of_mul_le_mul_right ?_ hcd
  calc (a₀ * b₁ + a₁ * b₀) * (c₀ * d₁)
      = a₀ * b₁ * (c₀ * d₁) + c₀ * d₁ * (a₁ * b₀) := by ring
    _ ≤ a₀ * b₁ * (a₁ * b₀) + c₀ * d₁ * (c₀ * d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀ * b₀ * (a₁ * b₁) + c₀ * d₁ * (c₀ * d₁) := by ring
    _ ≤ c₀ * d₀ * (c₁ * d₁) + c₀ * d₁ * (c₀ * d₁) := by gcongr
    _ = (c₀ * d₁ + c₁ * d₀) * (c₀ * d₁) := by ring

private def collapse (𝒜 : Finset (Finset α)) (a : α) (f : Finset α → β) (s : Finset α) : β :=
  ∑ t ∈ 𝒜 with t.erase a = s, f t

private lemma erase_eq_iff (hs : a ∉ s) : t.erase a = s ↔ t = s ∨ t = insert a s := by
  grind

private lemma filter_collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) :
    {t ∈ 𝒜 | t.erase a = s} =
      if s ∈ 𝒜 then
        (if insert a s ∈ 𝒜 then {s, insert a s} else {s})
      else
        (if insert a s ∈ 𝒜 then {insert a s} else ∅) := by
  ext t; split_ifs <;> simp [erase_eq_iff ha] <;> aesop

omit [LinearOrder β] [IsStrictOrderedRing β] in
lemma collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finset α → β) :
    collapse 𝒜 a f s = (if s ∈ 𝒜 then f s else 0) +
      if insert a s ∈ 𝒜 then f (insert a s) else 0 := by
  rw [collapse, filter_collapse_eq ha]
  split_ifs <;> simp [(ne_of_mem_of_not_mem' (mem_insert_self a s) ha).symm, *]

omit [LinearOrder β] [IsStrictOrderedRing β] in
lemma collapse_of_mem (ha : a ∉ s) (ht : t ∈ 𝒜) (hu : u ∈ 𝒜) (hts : t = s)
    (hus : u = insert a s) : collapse 𝒜 a f s = f t + f u := by
  subst hts; subst hus; simp_rw [collapse_eq ha, if_pos ht, if_pos hu]

lemma le_collapse_of_mem (ha : a ∉ s) (hf : 0 ≤ f) (hts : t = s) (ht : t ∈ 𝒜) :
    f t ≤ collapse 𝒜 a f s := by
  subst hts
  rw [collapse_eq ha, if_pos ht]
  split_ifs
  · exact le_add_of_nonneg_right <| hf _
  · rw [add_zero]

lemma le_collapse_of_insert_mem (ha : a ∉ s) (hf : 0 ≤ f) (hts : t = insert a s) (ht : t ∈ 𝒜) :
    f t ≤ collapse 𝒜 a f s := by
  rw [collapse_eq ha, ← hts, if_pos ht]
  split_ifs
  · exact le_add_of_nonneg_left <| hf _
  · rw [zero_add]

lemma collapse_nonneg (hf : 0 ≤ f) : 0 ≤ collapse 𝒜 a f := fun _s ↦ sum_nonneg fun _t _ ↦ hf _

lemma collapse_modular [ExistsAddOfLE β]
    (hu : a ∉ u) (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ ⦃s⦄, s ⊆ insert a u → ∀ ⦃t⦄, t ⊆ insert a u → f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t))
    (𝒜 ℬ : Finset (Finset α)) :
    ∀ ⦃s⦄, s ⊆ u → ∀ ⦃t⦄, t ⊆ u → collapse 𝒜 a f₁ s * collapse ℬ a f₂ t ≤
      collapse (𝒜 ⊼ ℬ) a f₃ (s ∩ t) * collapse (𝒜 ⊻ ℬ) a f₄ (s ∪ t) := by
  rintro s hsu t htu
  -- Gather a bunch of facts we'll need a lot
  have := hsu.trans <| subset_insert a _
  have := htu.trans <| subset_insert a _
  have := insert_subset_insert a hsu
  have := insert_subset_insert a htu
  have has := notMem_mono hsu hu
  have hat := notMem_mono htu hu
  have : a ∉ s ∩ t := notMem_mono (inter_subset_left.trans hsu) hu
  have := notMem_union.2 ⟨has, hat⟩
  rw [collapse_eq has]
  split_ifs
  · rw [collapse_eq hat]
    split_ifs
    · rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›) rfl
        (insert_inter_distrib _ _ _).symm, collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›)
        (union_mem_sups ‹_› ‹_›) rfl (insert_union_distrib _ _ _).symm]
      refine ineq (h₁ _) (h₁ _) (h₂ _) (h₂ _) (h₃ _) (h₃ _) (h₄ _) (h₄ _) (h ‹_› ‹_›) ?_ ?_ ?_
      · simpa [*] using h ‹insert a s ⊆ _› ‹t ⊆ _›
      · simpa [*] using h ‹s ⊆ _› ‹insert a t ⊆ _›
      · simpa [*] using h ‹insert a s ⊆ _› ‹insert a t ⊆ _›
    · rw [add_zero, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (insert_union _ _ _), insert_inter_of_notMem ‹_›, ← mul_add]
      gcongr
      exacts [add_nonneg (h₄ _) <| h₄ _, le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›]
    · rw [zero_add, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (inter_insert_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm, union_insert,
        insert_union_distrib, ← add_mul]
      gcongr
      exacts [add_nonneg (h₃ _) <| h₃ _,
        le_collapse_of_insert_mem ‹_› h₄ (insert_union_distrib _ _ _).symm (union_mem_sups ‹_› ‹_›)]
    · rw [add_zero, mul_zero]
      exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _
  · rw [add_zero, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (union_insert _ _ _), inter_insert_of_notMem ‹_›, ← mul_add]
      exact mul_le_mul_of_nonneg_right (le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›) <|
        add_nonneg (h₄ _) <| h₄ _
    · rw [mul_zero, add_zero]
      exact (h ‹_› ‹_›).trans <| mul_le_mul (le_collapse_of_mem ‹_› h₃ rfl <|
        inter_mem_infs ‹_› ‹_›) (le_collapse_of_mem ‹_› h₄ rfl <| union_mem_sups ‹_› ‹_›)
        (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
      refine (h ‹_› ‹_›).trans <| mul_le_mul ?_ (le_collapse_of_insert_mem ‹_› h₄
        (union_insert _ _ _) <| union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
      exact le_collapse_of_mem (notMem_mono inter_subset_left ‹_›) h₃
        (inter_insert_of_notMem ‹_›) <| inter_mem_infs ‹_› ‹_›
    · simp_rw [mul_zero, add_zero]
      exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _
  · rw [zero_add, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (insert_inter_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm,
        insert_inter_of_notMem ‹_›, ← insert_inter_distrib, insert_union, insert_union_distrib,
        ← add_mul]
      exact mul_le_mul_of_nonneg_left (le_collapse_of_insert_mem ‹_› h₄
        (insert_union_distrib _ _ _).symm <| union_mem_sups ‹_› ‹_›) <| add_nonneg (h₃ _) <| h₃ _
    · rw [mul_zero, add_zero]
      refine (h ‹_› ‹_›).trans <| mul_le_mul (le_collapse_of_mem ‹_› h₃
        (insert_inter_of_notMem ‹_›) <| inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_› h₄
        (insert_union _ _ _) <| union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
      exact (h ‹_› ‹_›).trans <| mul_le_mul (le_collapse_of_insert_mem ‹_› h₃
        (insert_inter_distrib _ _ _).symm <| inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_›
        h₄ (insert_union_distrib _ _ _).symm <| union_mem_sups ‹_› ‹_›) (h₄ _) <|
        collapse_nonneg h₃ _
    · simp_rw [mul_zero, add_zero]
      exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _
  · simp_rw [add_zero, zero_mul]
    exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _

omit [LinearOrder β] [IsStrictOrderedRing β] in
lemma sum_collapse (h𝒜 : 𝒜 ⊆ (insert a u).powerset) (hu : a ∉ u) :
    ∑ s ∈ u.powerset, collapse 𝒜 a f s = ∑ s ∈ 𝒜, f s := by
  calc
    _ = ∑ s ∈ u.powerset ∩ 𝒜, f s + ∑ s ∈ u.powerset.image (insert a) ∩ 𝒜, f s := ?_
    _ = ∑ s ∈ u.powerset ∩ 𝒜, f s + ∑ s ∈ ((insert a u).powerset \ u.powerset) ∩ 𝒜, f s := ?_
    _ = ∑ s ∈ 𝒜, f s := ?_
  · rw [← Finset.sum_ite_mem, ← Finset.sum_ite_mem, sum_image, ← sum_add_distrib]
    · exact sum_congr rfl fun s hs ↦ collapse_eq (notMem_mono (mem_powerset.1 hs) hu) _ _
    · exact (insert_erase_invOn.2.injOn).mono fun s hs ↦ notMem_mono (mem_powerset.1 hs) hu
  · congr with s
    simp only [mem_image, mem_powerset, mem_sdiff, subset_insert_iff]
    refine ⟨?_, fun h ↦ ⟨_, h.1, ?_⟩⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨subset_insert_iff.1 <| insert_subset_insert _ hs, fun h ↦
        hu <| h <| mem_insert_self _ _⟩
    · rw [insert_erase (erase_ne_self.1 fun hs ↦ ?_)]
      rw [hs] at h
      exact h.2 h.1
  · rw [← sum_union (disjoint_sdiff_self_right.mono inf_le_left inf_le_left),
      ← union_inter_distrib_right, union_sdiff_of_subset (powerset_mono.2 <| subset_insert _ _),
      inter_eq_right.2 h𝒜]

variable [ExistsAddOfLE β]

/-- The **Four Functions Theorem** on a powerset algebra. See `four_functions_theorem` for the
finite distributive lattice generalisation. -/
protected lemma Finset.four_functions_theorem (u : Finset α)
    (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ ⦃s⦄, s ⊆ u → ∀ ⦃t⦄, t ⊆ u → f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t))
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ u.powerset) (hℬ : ℬ ⊆ u.powerset) :
    (∑ s ∈ 𝒜, f₁ s) * ∑ s ∈ ℬ, f₂ s ≤ (∑ s ∈ 𝒜 ⊼ ℬ, f₃ s) * ∑ s ∈ 𝒜 ⊻ ℬ, f₄ s := by
  induction u using Finset.induction generalizing f₁ f₂ f₃ f₄ 𝒜 ℬ with
  | empty =>
    simp only [Finset.powerset_empty, Finset.subset_singleton_iff] at h𝒜 hℬ
    obtain rfl | rfl := h𝒜 <;> obtain rfl | rfl := hℬ <;> simp; exact h (subset_refl ∅) subset_rfl
  | insert a u hu ih =>
    specialize ih (collapse_nonneg h₁) (collapse_nonneg h₂) (collapse_nonneg h₃)
      (collapse_nonneg h₄) (collapse_modular hu h₁ h₂ h₃ h₄ h 𝒜 ℬ) Subset.rfl Subset.rfl
    have : 𝒜 ⊼ ℬ ⊆ powerset (insert a u) := by simpa using infs_subset h𝒜 hℬ
    have : 𝒜 ⊻ ℬ ⊆ powerset (insert a u) := by simpa using sups_subset h𝒜 hℬ
    simpa only [powerset_sups_powerset_self, powerset_infs_powerset_self, sum_collapse,
      not_false_eq_true, *] using ih

variable (f₁ f₂ f₃ f₄) [Fintype α]

private lemma four_functions_theorem_aux (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ s t, f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t)) (𝒜 ℬ : Finset (Finset α)) :
    (∑ s ∈ 𝒜, f₁ s) * ∑ s ∈ ℬ, f₂ s ≤ (∑ s ∈ 𝒜 ⊼ ℬ, f₃ s) * ∑ s ∈ 𝒜 ⊻ ℬ, f₄ s := by
  refine univ.four_functions_theorem h₁ h₂ h₃ h₄ ?_ ?_ ?_ <;> simp [h]

end Finset

section DistribLattice
variable [DistribLattice α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β] (f f₁ f₂ f₃ f₄ g μ : α → β)

/-- The **Four Functions Theorem**, aka **Ahlswede-Daykin Inequality**. -/
lemma four_functions_theorem [DecidableEq α] (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) (s t : Finset α) :
    (∑ a ∈ s, f₁ a) * ∑ a ∈ t, f₂ a ≤ (∑ a ∈ s ⊼ t, f₃ a) * ∑ a ∈ s ⊻ t, f₄ a := by
  classical
  set L : Sublattice α := ⟨latticeClosure (s ∪ t), isSublattice_latticeClosure.1,
    isSublattice_latticeClosure.2⟩
  have : Finite L := (s.finite_toSet.union t.finite_toSet).latticeClosure.to_subtype
  set s' : Finset L := s.preimage (↑) Subtype.coe_injective.injOn
  set t' : Finset L := t.preimage (↑) Subtype.coe_injective.injOn
  have hs' : s'.map ⟨L.subtype, Subtype.coe_injective⟩ = s := by
    simp [s', map_eq_image, image_preimage, filter_eq_self]
    exact fun a ha ↦ subset_latticeClosure <| Set.subset_union_left ha
  have ht' : t'.map ⟨L.subtype, Subtype.coe_injective⟩ = t := by
    simp [t', map_eq_image, image_preimage, filter_eq_self]
    exact fun a ha ↦ subset_latticeClosure <| Set.subset_union_right ha
  clear_value s' t'
  obtain ⟨β, _, _, g, hg⟩ := exists_birkhoff_representation L
  have := four_functions_theorem_aux (extend g (f₁ ∘ (↑)) 0) (extend g (f₂ ∘ (↑)) 0)
    (extend g (f₃ ∘ (↑)) 0) (extend g (f₄ ∘ (↑)) 0) (extend_nonneg (fun _ ↦ h₁ _) le_rfl)
    (extend_nonneg (fun _ ↦ h₂ _) le_rfl) (extend_nonneg (fun _ ↦ h₃ _) le_rfl)
    (extend_nonneg (fun _ ↦ h₄ _) le_rfl) ?_ (s'.map ⟨g, hg⟩) (t'.map ⟨g, hg⟩)
  · simpa only [← hs', ← ht', ← map_sups, ← map_infs, sum_map, Embedding.coeFn_mk, hg.extend_apply]
      using this
  rintro s t
  classical
  obtain ⟨a, rfl⟩ | hs := em (∃ a, g a = s)
  · obtain ⟨b, rfl⟩ | ht := em (∃ b, g b = t)
    · simp_rw [← sup_eq_union, ← inf_eq_inter, ← map_sup, ← map_inf, hg.extend_apply]
      exact h _ _
    · simpa [extend_apply' _ _ _ ht] using mul_nonneg
        (extend_nonneg (fun a : L ↦ h₃ a) le_rfl _) (extend_nonneg (fun a : L ↦ h₄ a) le_rfl _)
  · simpa [extend_apply' _ _ _ hs] using mul_nonneg
      (extend_nonneg (fun a : L ↦ h₃ a) le_rfl _) (extend_nonneg (fun a : L ↦ h₄ a) le_rfl _)

/-- An inequality of Daykin. Interestingly, any lattice in which this inequality holds is
distributive. -/
lemma Finset.le_card_infs_mul_card_sups [DecidableEq α] (s t : Finset α) :
    #s * #t ≤ #(s ⊼ t) * #(s ⊻ t) := by
  simpa using four_functions_theorem (1 : α → ℕ) 1 1 1 zero_le_one zero_le_one zero_le_one
    zero_le_one (fun _ _ ↦ le_rfl) s t

variable [Fintype α]

/-- Special case of the **Four Functions Theorem** when `s = t = univ`. -/
lemma four_functions_theorem_univ (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) :
    (∑ a, f₁ a) * ∑ a, f₂ a ≤ (∑ a, f₃ a) * ∑ a, f₄ a := by
  classical simpa using four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h univ univ

/-- The **Holley Inequality**. -/
lemma holley (hμ₀ : 0 ≤ μ) (hf : 0 ≤ f) (hg : 0 ≤ g) (hμ : Monotone μ)
    (hfg : ∑ a, f a = ∑ a, g a) (h : ∀ a b, f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)) :
    ∑ a, μ a * f a ≤ ∑ a, μ a * g a := by
  classical
  obtain rfl | hf := hf.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, eq_comm, Fintype.sum_eq_zero_iff_of_nonneg hg] at hfg
    simp [hfg]
  obtain rfl | hg := hg.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, Fintype.sum_eq_zero_iff_of_nonneg hf.le] at hfg
    simp [hfg]
  have := four_functions_theorem g (μ * f) f (μ * g) hg.le (mul_nonneg hμ₀ hf.le) hf.le
    (mul_nonneg hμ₀ hg.le) (fun a b ↦ ?_) univ univ
  · simpa [hfg, sum_pos hg] using this
  · simp_rw [Pi.mul_apply, mul_left_comm _ (μ _), mul_comm (g _)]
    rw [sup_comm, inf_comm]
    exact mul_le_mul (hμ le_sup_left) (h _ _) (mul_nonneg (hf.le _) <| hg.le _) <| hμ₀ _

/-- The **Fortuin-Kastelyn-Ginibre Inequality**. -/
lemma fkg (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Monotone f) (hg : Monotone g)
    (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a ≤ (∑ a, μ a) * ∑ a, μ a * (f a * g a) := by
  refine four_functions_theorem_univ (μ * f) (μ * g) μ _ (mul_nonneg hμ₀ hf₀) (mul_nonneg hμ₀ hg₀)
    hμ₀ (mul_nonneg hμ₀ <| mul_nonneg hf₀ hg₀) (fun a b ↦ ?_)
  dsimp
  rw [mul_mul_mul_comm, ← mul_assoc (μ (a ⊓ b))]
  exact mul_le_mul (hμ _ _) (mul_le_mul (hf le_sup_left) (hg le_sup_right) (hg₀ _) <| hf₀ _)
    (mul_nonneg (hf₀ _) <| hg₀ _) <| mul_nonneg (hμ₀ _) <| hμ₀ _

end DistribLattice

open Booleanisation

variable [DecidableEq α] [GeneralizedBooleanAlgebra α]

/-- A slight generalisation of the **Marica-Schönheim Inequality**. -/
lemma Finset.le_card_diffs_mul_card_diffs (s t : Finset α) :
    #s * #t ≤ #(s \\ t) * #(t \\ s) := by
  have : ∀ s t : Finset α, (s \\ t).map ⟨_, liftLatticeHom_injective⟩ =
      s.map ⟨_, liftLatticeHom_injective⟩ \\ t.map ⟨_, liftLatticeHom_injective⟩ := by
    rintro s t
    simp_rw [map_eq_image]
    exact image_image₂_distrib fun a b ↦ rfl
  simpa [← card_compls (_ ⊻ _), ← map_sup, ← map_inf, ← this] using
    (s.map ⟨_, liftLatticeHom_injective⟩).le_card_infs_mul_card_sups
      (t.map ⟨_, liftLatticeHom_injective⟩)ᶜˢ

/-- The **Marica-Schönheim Inequality**. -/
lemma Finset.card_le_card_diffs (s : Finset α) : #s ≤ #(s \\ s) :=
  le_of_pow_le_pow_left₀ two_ne_zero (zero_le _) <| by
    simpa [← sq] using s.le_card_diffs_mul_card_diffs s
