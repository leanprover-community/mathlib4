/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Directed
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.ContinuousFunction.Basic

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## Main definitions

- `ScottTopology'` - the Scott topology is defined as the join of the topology of upper sets and the
  topological space where a set `u` is open if, when the least upper bound of a directed set `d`
  lies in `u` then there is a tail of `d` which is a subset of `u`.

## Main statements

- `ScottTopology.isOpen_isUpper` - Scott open sets are upper.
- `ScottTopology.isClosed_isLower` - Scott closed sets are lower.
- `ScottTopology.continuous_monotone` - functions continuous wrt the Scott topology are
  monotone.
- `ScottTopology.continuous_iff_scottContinuous` - a function is Scott continuous (preserves least
  upper bounds of directed sets) if and only if it is continuous wrt the Scott topology.
- `ScottTopology.T0space` - the Scott topology on a partial order is T₀.

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

lemma isUpperSet_iff_forall_le  {s : Set α} : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a ≤ b →
  a ∈ s → b ∈ s := Iff.rfl

/--
The set of upper sets forms a topology
-/
def upperSetTopology : TopologicalSpace α :=
{ IsOpen := IsUpperSet,
  isOpen_univ := isUpperSet_univ,
  isOpen_inter := fun _ _ => IsUpperSet.inter,
  isOpen_unionₛ := fun _ h => isUpperSet_unionₛ h, }

/--
The Scott topology is defined as the join of the topology of upper sets and the topological space
where a set `u` is open if, when the least upper bound of a directed set `d` lies in `u` then there
is a tail of `d` which is a subset of `u`.
-/
def ScottTopology' : TopologicalSpace α := (upperSetTopology ⊔
    { IsOpen := fun u => ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a →
      a ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u,
      isOpen_univ := by
        intros d _ hd₁ _ _ _
        cases' hd₁ with b hb
        use b
        constructor
        . exact hb
        . exact (Ici b ∩ d).subset_univ,
      isOpen_inter := by
        intros s t hs ht d a hd₁ hd₂ hd₃ ha
        obtain ⟨b₁, hb₁_w, hb₁_h⟩ := hs d a hd₁ hd₂ hd₃ ha.1
        obtain ⟨b₂, hb₂_w, hb₂_h⟩ := ht d a hd₁ hd₂ hd₃ ha.2
        rw [DirectedOn] at hd₂
        obtain ⟨c, hc_w, hc_h⟩ := hd₂ b₁ hb₁_w b₂ hb₂_w
        refine ⟨c, hc_w, ?_⟩
        . calc
            Ici c ∩ d ⊆ (Ici b₁ ∩ Ici b₂) ∩ d := by
            { apply inter_subset_inter_left d
              apply subset_inter (Ici_subset_Ici.mpr hc_h.1) (Ici_subset_Ici.mpr hc_h.2) }
            _ = (Ici b₁ ∩ d) ∩ (Ici b₂ ∩ d) := by rw [inter_inter_distrib_right]
            _ ⊆ s ∩ t := inter_subset_inter hb₁_h hb₂_h
      isOpen_unionₛ := by
        intros s h d a hd₁ hd₂ hd₃ ha
        rw [mem_unionₛ] at ha
        obtain ⟨s₀, hs₀_w, hs₀_h⟩ := ha
        obtain ⟨b, hb_w, hb_h⟩ := h s₀ hs₀_w d a hd₁ hd₂ hd₃ hs₀_h
        use b
        constructor
        . exact hb_w
        . exact Set.subset_unionₛ_of_subset s s₀ hb_h hs₀_w
      })

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

variable [TopologicalSpace α] [ScottTopology α]

variable (α)

lemma topology_eq : ‹_› = ScottTopology' := topology_eq_ScottTopology

variable {α}

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScottTopology α`.
-/
def withScottTopologyHomeomorph : WithScottTopology α ≃ₜ α :=
  WithScottTopology.ofScott.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

lemma isOpen_eq_upper_and_LUB_mem_implies_tail_subset (u : Set α) : IsOpen u
= (IsUpperSet u ∧ ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → a ∈ u
  → ∃ b ∈ d, Ici b ∩ d ⊆ u) := by erw [topology_eq α]; rfl

lemma isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty (u : Set α) :
IsOpen u ↔ (IsUpperSet u ∧ ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a →
a ∈ u → (d ∩ u).Nonempty) := by
  rw [isOpen_eq_upper_and_LUB_mem_implies_tail_subset]
  constructor
  . refine' And.imp_right _
    intros h d a d₁ d₂ d₃ ha
    obtain ⟨b, h_1_w, h_1_h⟩ := h d a d₁ d₂ d₃ ha
    rw [inter_nonempty_iff_exists_left]
    use b
    constructor
    . exact h_1_w
    . apply mem_of_subset_of_mem h_1_h
      rw [mem_inter_iff]
      constructor
      . exact left_mem_Ici
      . exact h_1_w
  . intros h
    constructor
    . exact h.1
    . intros d a d₁ d₂ d₃ ha
      have e1 : (d ∩ u).Nonempty := h.2 d a d₁ d₂ d₃ ha
      rw [inter_nonempty_iff_exists_left] at e1
      obtain ⟨b, e1_h_w, e1_h_h⟩ := e1
      use b
      constructor
      . exact e1_h_w
      . exact Subset.trans (inter_subset_left (Ici b) d) (h.1.Ici_subset e1_h_h)

lemma isClosed_eq_lower_and_subset_implies_LUB_mem (s : Set α) : IsClosed s
  = (IsLowerSet s ∧
  ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → d ⊆ s → a ∈ s ) := by
  rw [← isOpen_compl_iff, isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty,
    isLowerSet_compl.symm, compl_compl]
  refine' let_value_eq (And (IsLowerSet s)) _
  rw [eq_iff_iff]
  constructor
  . intros h d a d₁ d₂ d₃ d₄
    by_contra h'
    rw [← mem_compl_iff] at h'
    have c1: (d ∩ sᶜ).Nonempty := h d a d₁ d₂ d₃ h'
    have c2: (d ∩ sᶜ) =  ∅ := by
      rw [← subset_empty_iff, ← inter_compl_self s]
      exact inter_subset_inter_left _ d₄
    rw [c2] at c1
    simp only [Set.not_nonempty_empty] at c1
  . intros h d a d₁ d₂ d₃ d₄
    rw [inter_compl_nonempty_iff]
    by_contra h'
    have c1: a ∈ s := h d a d₁ d₂ d₃ h'
    contradiction

lemma isOpen_isUpperSet {s : Set α} : IsOpen s → IsUpperSet s := by
  intros h
  rw [isOpen_eq_upper_and_LUB_mem_implies_tail_subset] at h
  exact h.1

lemma isClosed_isLower {s : Set α} : IsClosed s → IsLowerSet s := by
  intro h
  rw [isClosed_eq_lower_and_subset_implies_LUB_mem] at h
  exact h.1

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
(-∞,a].
-/
@[simp] lemma closure_singleton (a : α) : closure {a} = Iic a := by
  rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
  refine' subset_antisymm _ _
  . apply closure_minimal subset_lowerClosure
    rw [isClosed_eq_lower_and_subset_implies_LUB_mem]
    constructor
    . exact (lowerClosure {a}).lower
    . rw [lowerClosure_singleton]
      intros d b _ _ d₃ d₄
      rw [LowerSet.coe_Iic, mem_Iic]
      exact (isLUB_le_iff d₃).mpr d₄
  . exact lowerClosure_min subset_closure (isClosed_isLower isClosed_closure)

variable [Preorder β] [TopologicalSpace β] [ScottTopology β]

lemma continuous_monotone {f : α → β}
  (hf : Continuous f) : Monotone f := by
  rw [Monotone]
  intros a b hab
  let u := (Iic (f b))ᶜ
  by_contra h
  have s1 : IsOpen u
  { rw [isOpen_compl_iff, ← closure_singleton]
    exact isClosed_closure }
  have u3 : b ∈ (f⁻¹'  u) :=
    isUpperSet_iff_forall_le.mp (isOpen_isUpperSet (IsOpen.preimage hf s1)) hab h
  have c1 : f b ∈ (Iic (f b))ᶜ := by
    simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1

lemma continuous_iff_scottContinuous (f : α → β) : Continuous f ↔ ScottContinuous f := by
  constructor
  . intros hf d d₁ d₂ a d₃
    rw [IsLUB]
    constructor
    . apply Monotone.mem_upperBounds_image (continuous_monotone hf)
      rw [← isLUB_le_iff]
      exact d₃
    . rw [lowerBounds, mem_setOf_eq]
      intros b hb
      let u := (Iic b)ᶜ
      by_contra h
      have s1 : IsOpen u := by
        rw [isOpen_compl_iff, ← closure_singleton]
        exact isClosed_closure
      have s2 : IsOpen (f⁻¹'  u) := IsOpen.preimage hf s1
      rw [isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty] at s2
      obtain ⟨c, h_1_left, h_1_right⟩ := s2.2 d a d₁ d₂ d₃ h
      simp at h_1_right
      rw [upperBounds] at hb
      simp at hb
      have c1: f c ≤ b := hb _ h_1_left
      contradiction
  . intro h
    rw [continuous_def]
    intros u hu
    rw [isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty]
    constructor
    . exact IsUpperSet.preimage (isOpen_isUpperSet hu) h.monotone
    . intros d a hd₁ hd₂ hd₃ ha
      rw [isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty] at hu
      exact image_inter_nonempty_iff.mp $ hu.2 _ _ (hd₁.image f)
          (directedOn_image.mpr (hd₂.mono (by simp only [Order.Preimage]; apply h.monotone)))
          (h hd₁ hd₂ hd₃) ha

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

lemma isOpen_eq_upper_and_sup_mem_implies_tail_subset
(u : Set α) : IsOpen u =
(IsUpperSet u ∧
  ∀ (d : Set α), d.Nonempty → DirectedOn (· ≤ ·) d → supₛ d ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u) := by
  rw [ScottTopology.isOpen_eq_upper_and_LUB_mem_implies_tail_subset]
  refine' let_value_eq (And (IsUpperSet u)) _
  rw [eq_iff_iff]
  constructor
  . intros h d hd₁ hd₂ hd₃
    exact h d (supₛ d) hd₁ hd₂ (isLUB_supₛ d) hd₃
  . intros h d a hd₁ hd₂ hd₃ ha
    apply h d hd₁ hd₂
    rw [(IsLUB.supₛ_eq hd₃)]
    exact ha

lemma isOpen_eq_upper_and_sup_mem_implies_inter_nonempty
(u : Set α) : IsOpen u =
(IsUpperSet u ∧  ∀ (d : Set α), d.Nonempty → DirectedOn (· ≤ ·) d → supₛ d ∈ u →
(d∩u).Nonempty) := by
  rw [ScottTopology.isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty]
  refine' let_value_eq (And (IsUpperSet u)) _
  rw [eq_iff_iff]
  constructor
  . intros h d hd₁ hd₂ hd₃
    exact h d (supₛ d) hd₁ hd₂ (isLUB_supₛ d) hd₃
  . intros h d a hd₁ hd₂ hd₃ ha
    apply h d hd₁ hd₂
    rw [(IsLUB.supₛ_eq hd₃)]
    exact ha

end complete_lattice
