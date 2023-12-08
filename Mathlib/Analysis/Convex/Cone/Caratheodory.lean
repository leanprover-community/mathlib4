import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Caratheodory

open Set Function BigOperators

universe u

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

variable {s : Set E}

theorem convexCone_eq_union : (Submodule.span 𝕜≥0 s : Set E) =
    ⋃ (t : Finset E) (hss : ↑t ⊆ s) (hai : LinearIndependent 𝕜 ((↑) : t → E)),
      (Submodule.span 𝕜≥0 s : Set E) := by
  apply Set.Subset.antisymm
  · sorry
  · aesop

theorem eq_pos_convex_span_of_mem_convexCone {x : E} (hx : x ∈ (Submodule.span 𝕜≥0 s : Set E)) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (_ : Set.range z ⊆ s) (_ : LinearIndependent 𝕜 z), ∑ i, z i = x := by
  simp
  rw [convexCone_eq_union] at hx
  simp at hx
  obtain ⟨i, h₁, h₂, h₃⟩ := hx
  use i, Finset.fintypeCoeSort i
  use Subtype.val
  use h₁
  constructor
  · simp_rw [Subtype.range_coe_subtype, Finset.setOf_mem, h₂]
  · unfold Submodule.span at h₃
    unfold sInf at h₃
    sorry
