/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## Main definitions

- `InaccessibleByDirectedJoins` - a set `u` is said to be inaccessible by directed joins if, when
  the least upper bound of a directed set `d` lies in `u` then `d` has non-empty intersection with
  `u`.
- `ScottTopology'` - the Scott topology is defined as the join of the topology of upper sets and the
  Scott-Hausdorff topology (the topological space where a set `u` is open if, when the least upper
  bound of a directed set `d` lies in `u` then there is a tail of `d` which is a subset of `u`).

## Main statements

- `ScottTopology.isUpperSet_of_isOpen` - Scott open sets are upper.
- `ScottTopology.isLowerSet_of_isClosed` - Scott closed sets are lower.
- `ScottTopology.monotone_of_continuous` - functions continuous wrt the Scott topology are
  monotone.
- `ScottTopology.scottContinuous_iff_continuous` - a function is Scott continuous (preserves least
  upper bounds of directed sets) if and only if it is continuous wrt the Scott topology.
- `ScottTopology.instT0Space` - the Scott topology on a partial order is T₀.

## Implementation notes

A type synonym `WithScottTopology` is introduced and for a preorder `α`, `WithScottTopology α`
is made an instance of `topological_space` by the `ScottTopology'`.

We define a mixin class `ScottTopology` for the class of types which are both a preorder and a
topology and where the topology is the `ScottTopology'`.
It is shown that `WithScottTopology α` is an instance of `ScottTopology`.

A class `Scott` is defined in `topology.omega_complete_partial_order` and made an instance of a
topological space by defining the open sets to be those which have characteristic functions which
are monotone and preserve limits of countable chains. Whilst this definition of the Scott topology
coincides with the one given here in some special cases, in general they are not the same
[Domain Theory, 2.2.4][abramsky_gabbay_maibaum_1994].

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags
Scott topology, preorder
-/

variable (α β : Type _)

open Set

section preorder

variable {α} {β}

variable [Preorder α] [Preorder β]

def InaccessibleByDirectedJoins (u : Set α) : Prop :=
  ∀ ⦃d : Set α⦄ ⦃a : α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → a ∈ u → (d ∩ u).Nonempty

/--
The Scott-Hausdorff topology is defined as the topological space where a set `u` is open if, when
the least upper bound of a directed set `d` lies in `u` then there is a tail of `d` which is a
subset of `u`.
-/
def ScottHausdorffTopology : TopologicalSpace α :=
{ IsOpen := fun u => ∀ ⦃d : Set α⦄ ⦃a : α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a →
    a ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u,
  isOpen_univ := by
    intros d _ hd₁ _ _ _
    cases' hd₁ with b hb
    use b
    constructor
    · exact hb
    · exact (Ici b ∩ d).subset_univ,
  isOpen_inter := by
    intros s t hs ht d a hd₁ hd₂ hd₃ ha
    obtain ⟨b₁, hb₁_w, hb₁_h⟩ := hs hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂_w, hb₂_h⟩ := ht hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hc_w, hc_h⟩ := hd₂ b₁ hb₁_w b₂ hb₂_w
    refine ⟨c, hc_w, ?_⟩
    · calc
        Ici c ∩ d ⊆ Ici b₁ ∩ Ici b₂ ∩ d := by
        { apply inter_subset_inter_left d
          apply subset_inter (Ici_subset_Ici.mpr hc_h.1) (Ici_subset_Ici.mpr hc_h.2) }
        _ = (Ici b₁ ∩ d) ∩ (Ici b₂ ∩ d) := by rw [inter_inter_distrib_right]
        _ ⊆ s ∩ t := inter_subset_inter hb₁_h hb₂_h
  isOpen_sUnion := by
    intros s h d a hd₁ hd₂ hd₃ ha
    obtain ⟨s₀, hs₀_w, hs₀_h⟩ := ha
    obtain ⟨b, hb_w, hb_h⟩ := h s₀ hs₀_w hd₁ hd₂ hd₃ hs₀_h
    use b
    constructor
    · exact hb_w
    · exact Set.subset_sUnion_of_subset s s₀ hb_h hs₀_w }


lemma ScottHausdorffTopology.Lower_IsOpen {s : Set α} (h : IsLowerSet s) :
    ScottHausdorffTopology.IsOpen s := by
  intros d a hd _ hda ha
  obtain ⟨b, hb⟩  := hd
  use b
  constructor
  · exact hb
  · apply Subset.trans (inter_subset_right (Ici b) d)
      (fun c hc => h (mem_upperBounds.mp hda.1 _ hc) ha)

/--
The Scott topology is defined as the join of the topology of upper sets and the Scott Hausdorff
topology.
-/
def ScottTopology' : TopologicalSpace α := upperSetTopology' α ⊔ ScottHausdorffTopology

lemma upper_le_Scott : upperSetTopology' α ≤  ScottTopology' := le_sup_left

lemma ScottHausdorff_le_Scott : @ScottHausdorffTopology α ≤  @ScottTopology' α := le_sup_right

end preorder

/--
Type synonym for a preorder equipped with the Scott topology
-/
def WithScottTopology := α

variable {α β}

namespace WithScottTopology

/-- `toScott` is the identity function to the `WithScottTopology` of a type.  -/
@[match_pattern] def toScott : α ≃ WithScottTopology α := Equiv.refl _

/-- `ofScott` is the identity function from the `WithScottTopology` of a type.  -/
@[match_pattern] def ofScott : WithScottTopology α ≃ α := Equiv.refl _

@[simp] lemma to_scott_symm_eq : (@toScott α).symm = ofScott := rfl
@[simp] lemma of_scott_symm_eq : (@ofScott α).symm = toScott := rfl
@[simp] lemma toScott_ofScott (a : WithScottTopology α) : toScott (ofScott a) = a := rfl
@[simp] lemma ofScott_toScott (a : α) : ofScott (toScott a) = a := rfl
-- porting note: removed @[simp] to make linter happy
lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl
-- porting note: removed @[simp] to make linter happy
lemma ofScott_inj {a b : WithScottTopology α} : ofScott a = ofScott b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithScottTopology`. Use as `induction x using WithScottTopology.rec`. -/
protected def rec {β : WithScottTopology α → Sort _}
  (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a => h (ofScott a)


instance [Nonempty α] : Nonempty (WithScottTopology α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithScottTopology α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithScottTopology α) := ‹Preorder α›

instance : TopologicalSpace (WithScottTopology α) := ScottTopology'

end WithScottTopology

/--
The Scott topology is defined as the join of the topology of upper sets and the topological space
where a set `u` is open if, when the least upper bound of a directed set `d` lies in `u` then there
is a tail of `d` which is a subset of `u`.
-/
class ScottTopology (α : Type _) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_ScottTopology : t = ScottTopology'

instance [Preorder α] : ScottTopology (WithScottTopology α) :=
  ⟨rfl⟩

namespace ScottTopology

section preorder

variable [Preorder α]

lemma isOpen_iff_upper_and_Scott_Hausdorff_Open' {u : Set α} :
  IsOpen (WithScottTopology.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ ScottHausdorffTopology.IsOpen u :=
by rfl

variable [TopologicalSpace α] [ScottTopology α]

variable (α)

lemma topology_eq : ‹_› = ScottTopology' := topology_eq_ScottTopology

variable {α}

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScottTopology α`.
-/
def withScottTopologyHomeomorph : WithScottTopology α ≃ₜ α :=
  WithScottTopology.ofScott.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

end preorder


section morphisms

variable [Preorder α] [Preorder β]

open TopologicalSpace

lemma upperSetTopology_coinduced' {t₁ : TopologicalSpace α} [UpperSetTopology α]
    (hf : Monotone f) : coinduced f t₁ ≤ @ScottTopology' β _ := by
  apply le_sup_of_le_left
  rwa [← continuous_iff_coinduced_le,
    ← @UpperSetTopology.monotone_iff_continuous α β _ _ t₁ _ (upperSetTopology' β) _ _ ]

lemma Monotone_coinduced {t₁ : TopologicalSpace α} [UpperSetTopology α]
    {t₂ : TopologicalSpace β} [ScottTopology β] (hf : Monotone f) : coinduced f t₁ ≤ t₂ := by
  rw [ScottTopology.topology_eq β]
  apply upperSetTopology_coinduced' hf

lemma Monotone_continuous {t₁ : TopologicalSpace α} [UpperSetTopology α]
    {t₂ : TopologicalSpace β} [ScottTopology β] {f : α → β} (hf : Monotone f)  : Continuous f := by
  rw [continuous_iff_coinduced_le]
  apply Monotone_coinduced hf

end morphisms


section preorder

variable [Preorder α] [TopologicalSpace α] [ScottTopology α]

lemma isOpen_iff_upper_and_Scott_Hausdorff_Open {u : Set α} : IsOpen u
  ↔ IsUpperSet u ∧ ScottHausdorffTopology.IsOpen u := by erw [topology_eq α]; rfl

lemma isOpen_iff_upper_and_InaccessibleByDirectedJoins {u : Set α} :
    IsOpen u ↔ IsUpperSet u ∧ InaccessibleByDirectedJoins u := by
  rw [isOpen_iff_upper_and_Scott_Hausdorff_Open]
  constructor
  · refine' And.imp_right _
    intros h d a d₁ d₂ d₃ ha
    obtain ⟨b, h_1_w, h_1_h⟩ := h d₁ d₂ d₃ ha
    use b
    constructor
    · exact h_1_w
    · apply mem_of_subset_of_mem h_1_h
      constructor
      · exact left_mem_Ici
      · exact h_1_w
  · intros h
    constructor
    · exact h.1
    · intros d a d₁ d₂ d₃ ha
      obtain ⟨b, e1_h_w, e1_h_h⟩ := h.2 d₁ d₂ d₃ ha
      use b
      constructor
      · exact e1_h_w
      · exact Subset.trans (inter_subset_left (Ici b) d) (h.1.Ici_subset e1_h_h)

lemma isClosed_iff_lower_and_subset_implies_LUB_mem {s : Set α} : IsClosed s
    ↔ (IsLowerSet s ∧
    ∀ ⦃d : Set α⦄ ⦃a : α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → d ⊆ s → a ∈ s ) := by
  rw [← isOpen_compl_iff, isOpen_iff_upper_and_InaccessibleByDirectedJoins,
    isLowerSet_compl.symm, compl_compl]
  apply and_congr_right'
  constructor
  · intros h d a d₁ d₂ d₃ d₄
    by_contra h'
    have c1: (d ∩ sᶜ).Nonempty := h d₁ d₂ d₃ h'
    have c2: d ∩ sᶜ =  ∅ := by
      rw [← subset_empty_iff, ← inter_compl_self s]
      exact inter_subset_inter_left _ d₄
    rw [c2] at c1
    simp only [Set.not_nonempty_empty] at c1
  · intros h d a d₁ d₂ d₃ d₄
    rw [inter_compl_nonempty_iff]
    by_contra h'
    have c1: a ∈ s := h d₁ d₂ d₃ h'
    contradiction

lemma isUpperSet_of_isOpen {s : Set α} : IsOpen s → IsUpperSet s := fun h =>
  (isOpen_iff_upper_and_Scott_Hausdorff_Open.mp h).left

lemma isLowerSet_of_isClosed {s : Set α} : IsClosed s → IsLowerSet s := fun h =>
  (isClosed_iff_lower_and_subset_implies_LUB_mem.mp h).left

lemma lowerClosure_le_closure {s : Set α} : lowerClosure s ≤ closure s := by
  convert closure.mono (@upper_le_Scott α _)
  rw [@UpperSetTopology.closure_eq_lowerClosure α _ (upperSetTopology' α) ?_ s]
  exact instUpperSetTopologyUpperSetTopology'
  exact topology_eq α

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
(-∞,a].
-/
lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [le_antisymm_iff]
  constructor
  · apply closure_minimal
    rw [singleton_subset_iff, mem_Iic]
    rw [isClosed_iff_lower_and_subset_implies_LUB_mem]
    constructor
    · exact isLowerSet_Iic a
    · intros d b _ _ d₃ d₄
      exact (isLUB_le_iff d₃).mpr d₄
  · rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
    apply lowerClosure_le_closure

variable [Preorder β] [TopologicalSpace β] [ScottTopology β]

lemma monotone_of_continuous {f : α → β} (hf : Continuous f) : Monotone f := by
  rw [Monotone]
  intros a b hab
  let u := (Iic (f b))ᶜ
  by_contra h
  have s1 : IsOpen u
  { rw [isOpen_compl_iff, ← closure_singleton]
    exact isClosed_closure }
  have u3 : b ∈ f⁻¹'  u := isUpperSet_of_isOpen (IsOpen.preimage hf s1) hab h
  have c1 : f b ∈ (Iic (f b))ᶜ := by
    simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1

@[simp] lemma scottContinuous_iff_continuous {f : α → β} : ScottContinuous f ↔ Continuous f := by
  constructor
  · intro h
    rw [continuous_def]
    intros u hu
    rw [isOpen_iff_upper_and_InaccessibleByDirectedJoins]
    constructor
    · exact IsUpperSet.preimage (isUpperSet_of_isOpen hu) h.monotone
    · intros d a hd₁ hd₂ hd₃ ha
      rw [isOpen_iff_upper_and_InaccessibleByDirectedJoins] at hu
      exact image_inter_nonempty_iff.mp $ hu.2 (hd₁.image f)
          (directedOn_image.mpr (hd₂.mono (by simp only [Order.Preimage]; apply h.monotone)))
          (h hd₁ hd₂ hd₃) ha
  · intros hf d d₁ d₂ a d₃
    rw [IsLUB]
    constructor
    · apply Monotone.mem_upperBounds_image (monotone_of_continuous hf) ((isLUB_le_iff d₃).mp le_rfl)
    · rw [lowerBounds, mem_setOf_eq]
      intros b hb
      let u := (Iic b)ᶜ
      by_contra h
      have s1 : IsOpen u := by
        rw [isOpen_compl_iff, ← closure_singleton]
        exact isClosed_closure
      have s2 : IsOpen (f⁻¹'  u) := IsOpen.preimage hf s1
      rw [isOpen_iff_upper_and_InaccessibleByDirectedJoins] at s2
      obtain ⟨c, h_1_left, h_1_right⟩ := s2.2 d₁ d₂ d₃ h
      simp at h_1_right
      rw [upperBounds] at hb
      simp at hb
      have c1: f c ≤ b := hb _ h_1_left
      contradiction

end preorder

section partial_order
variable [PartialOrder α] [TopologicalSpace α] [ScottTopology α]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90): T0Space α :=
    (t0Space_iff_inseparable α).2 $ fun x y h => Iic_injective $
  by simpa only [inseparable_iff_closure_eq, ScottTopology.closure_singleton] using h

end partial_order

end ScottTopology

section complete_lattice

variable [CompleteLattice α] [TopologicalSpace α] [ScottTopology α]

lemma isOpen_iff_isUpperSet_and_sup_mem_implies_tail_subset {u : Set α} :
    IsOpen u ↔ IsUpperSet u ∧ ∀ ⦃d : Set α⦄,
    d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u := by
  rw [ScottTopology.isOpen_iff_upper_and_Scott_Hausdorff_Open]
  apply and_congr_right'
  constructor
  · exact fun h d hd₁ hd₂ hd₃ => h hd₁ hd₂ (isLUB_sSup d) hd₃
  · exact fun h d a hd₁ hd₂ hd₃ ha => h hd₁ hd₂ (Set.mem_of_eq_of_mem (IsLUB.sSup_eq hd₃) ha)

lemma isOpen_iff_upper_and_sup_mem_implies_inter_nonempty
    {u : Set α} : IsOpen u ↔
    IsUpperSet u ∧  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u →
    (d∩u).Nonempty := by
  rw [ScottTopology.isOpen_iff_upper_and_InaccessibleByDirectedJoins]
  apply and_congr_right'
  constructor
  · exact fun h d hd₁ hd₂ hd₃ => h hd₁ hd₂ (isLUB_sSup d) hd₃
  · exact fun h d a hd₁ hd₂ hd₃ ha => h hd₁ hd₂ (Set.mem_of_eq_of_mem (IsLUB.sSup_eq hd₃) ha)

lemma isClosed_iff_lower_and_closed_under_Directed_Sup {s : Set α} : IsClosed s
    ↔ IsLowerSet s ∧
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → d ⊆ s → sSup d ∈ s := by
  rw [ScottTopology.isClosed_iff_lower_and_subset_implies_LUB_mem]
  apply and_congr_right'
  constructor
  · exact fun h d hd₁ hd₂ hd₃ => h hd₁ hd₂ (isLUB_sSup d) hd₃
  · exact fun h d a h₁ h₂ h₃ ha => Set.mem_of_eq_of_mem (IsLUB.sSup_eq h₃).symm (h h₁ h₂ ha)


end complete_lattice

variable [Preorder α]

lemma scottHausdorffTopology_le_of_scottTopology [TopologicalSpace α] [ScottTopology α] :
    ScottHausdorffTopology ≤ ‹TopologicalSpace α› := by
  rw [ScottTopology.topology_eq α, ScottTopology']
  apply le_sup_right

lemma ScottOpen_implies_ScottHausdorffOpen {s : Set α} :
    IsOpen (WithScottTopology.ofScott ⁻¹' s) → ScottHausdorffTopology.IsOpen s :=
  scottHausdorffTopology_le_of_scottTopology _

lemma scottHausdorffTopology_le_Lower [TopologicalSpace α] [LowerTopology α] :
    ScottHausdorffTopology ≤  ‹TopologicalSpace α› :=
  fun _ h => ScottHausdorffTopology.Lower_IsOpen (LowerTopology.isLowerSet_of_isOpen h)

lemma ScottHausdorffOpen_implies_LowerOpen {s : Set α} :
    IsOpen (WithLowerTopology.ofLower ⁻¹' s) → ScottHausdorffTopology.IsOpen s :=
  scottHausdorffTopology_le_Lower _
