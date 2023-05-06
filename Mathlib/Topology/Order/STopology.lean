
import Mathlib.Order.Directed
import Mathlib.Topology.Basic
import Mathlib.Order.UpperLower.Basic

open Set

variable (α : Type _)

section preorder

variable {α}

variable [Preorder α]

/--
The collection of sets satisfying "Property S" form a topology
-/
def STopology : TopologicalSpace α :=
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
    obtain ⟨c, hc_w, hc_h⟩ := hd₂ b₁ hb₁_w b₂ hb₂_w
    refine ⟨c, hc_w, ?_⟩
    . calc
        Ici c ∩ d ⊆ (Ici b₁ ∩ Ici b₂) ∩ d := by
        { apply inter_subset_inter_left d
          apply subset_inter (Ici_subset_Ici.mpr hc_h.1) (Ici_subset_Ici.mpr hc_h.2) }
        _ = (Ici b₁ ∩ d) ∩ (Ici b₂ ∩ d) := by rw [inter_inter_distrib_right]
        _ ⊆ s ∩ t := inter_subset_inter hb₁_h hb₂_h,
  isOpen_unionₛ := by
    intros s h d a hd₁ hd₂ hd₃ ha
    obtain ⟨s₀, hs₀_w, hs₀_h⟩ := ha
    obtain ⟨b, hb_w, hb_h⟩ := h s₀ hs₀_w d a hd₁ hd₂ hd₃ hs₀_h
    use b
    constructor
    . exact hb_w
    . exact Set.subset_unionₛ_of_subset s s₀ hb_h hs₀_w }

lemma Lower_IsOpen (s : Set α) (h : IsLowerSet s) : STopology.IsOpen s := by
  intros d a hd _ hda ha
  obtain ⟨b, hb⟩  := hd
  use b
  constructor
  . exact hb
  . apply Subset.trans (inter_subset_right (Ici b) d)
      (fun c hc => h (mem_upperBounds.mp hda.1 _ hc) ha)

end preorder
