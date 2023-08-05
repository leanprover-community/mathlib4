/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Topology.StoneCech

#align_import topology.extremally_disconnected from "leanprover-community/mathlib"@"7e281deff072232a3c5b3e90034bd65dde396312"

/-!
# Extremally disconnected spaces

An extremally disconnected topological space is a space in which the closure of every open set is
open. Such spaces are also called Stonean spaces. They are the projective objects in the category of
compact Hausdorff spaces.

## Main declarations

* `ExtremallyDisconnected`: Predicate for a space to be extremally disconnected.
* `CompactT2.Projective`: Predicate for a topological space to be a projective object in the
  category of compact Hausdorff spaces.
* `CompactT2.Projective.extremallyDisconnected`: Compact Hausdorff spaces that are
  projective are extremally disconnected.

# TODO

Prove the converse to `CompactT2.Projective.extremallyDisconnected`, namely that a compact,
Hausdorff, extremally disconnected space is a projective object in the category of compact Hausdorff
spaces.

## References

[Gleason, *Projective topological spaces*][gleason1958]
-/


open Set

open Classical

universe u v w

variable (X : Type u) [TopologicalSpace X]

open Function

/-- An extremally disconnected topological space is a space
in which the closure of every open set is open. -/
class ExtremallyDisconnected : Prop where
  open_closure : ∀ U : Set X, IsOpen U → IsOpen (closure U)
#align extremally_disconnected ExtremallyDisconnected

section TotallySeparated

/-- Extremally disconnected spaces are totally separated. -/
instance [ExtremallyDisconnected X] [T2Space X] : TotallySeparatedSpace X :=
{ isTotallySeparated_univ := by
    intro x _ y _ hxy
    obtain ⟨U, V, hUV⟩ := T2Space.t2 x y hxy
    use closure U
    use (closure U)ᶜ
    refine ⟨ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    simp only [Set.mem_compl_iff]
    rw [mem_closure_iff]
    push_neg
    refine' ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, _⟩⟩
    rw [Set.nonempty_iff_ne_empty]
    simp only [not_not]
    rw [← Set.disjoint_iff_inter_eq_empty, disjoint_comm]
    exact hUV.2.2.2.2 }

end TotallySeparated

section

/-- The assertion `CompactT2.Projective` states that given continuous maps
`f : X → Z` and `g : Y → Z` with `g` surjective between `t_2`, compact topological spaces,
there exists a continuous lift `h : X → Y`, such that `f = g ∘ h`. -/
def CompactT2.Projective : Prop :=
  ∀ {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    ∀ [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      ∀ {f : X → Z} {g : Y → Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        ∃ h : X → Y, Continuous h ∧ g ∘ h = f
#align compact_t2.projective CompactT2.Projective

end

variable {X}

theorem StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCech X) := by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
  let s : Z → Y := fun z => Classical.choose <| g_sur z
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  let t := s ∘ f ∘ stoneCechUnit
  have ht : Continuous t := continuous_of_discreteTopology
  let h : StoneCech X → Y := stoneCechExtend ht
  have hh : Continuous h := continuous_stoneCechExtend ht
  refine' ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf _⟩
  rw [comp.assoc, stoneCechExtend_extends ht, ← comp.assoc, hs, comp.left_id]
#align stone_cech.projective StoneCech.projective

protected theorem CompactT2.Projective.extremallyDisconnected [CompactSpace X] [T2Space X]
    (h : CompactT2.Projective X) : ExtremallyDisconnected X := by
  refine' { open_closure := fun U hU => _ }
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  let Z : Set (X × Bool) := Z₁ ∪ Z₂
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  let f : Z → X := Prod.fst ∘ Subtype.val
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, Set.mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, Set.mem_singleton _⟩⟩, rfl⟩
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  let φ := Subtype.val ∘ g
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  have hφ₁ : ∀ x, (φ x).1 = x := congr_fun g_sec
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this, Set.preimage_comp, ← isClosed_compl_iff, ← preimage_compl, ←
      preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine' (closure_minimal _ <| hZ₂.preimage hφ).antisymm fun x hx => _
  · intro x hx
    have : φ x ∈ Z₁ ∪ Z₂ := (g x).2
    -- Porting note: Originally `simpa [hx, hφ₁] using this`
    cases' this with hφ hφ
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
    · exact hφ
  · rw [← hφ₁ x]
    exact hx.1
#align compact_t2.projective.extremally_disconnected CompactT2.Projective.extremallyDisconnected

-- Note: It might be possible to use Gleason for this instead
/-- The sigma-type of extremally disconneted spaces is extremally disconnected -/
instance instExtremallyDisconnected
    {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [h₀ : ∀ i, ExtremallyDisconnected (π i)] :
    ExtremallyDisconnected (Σi, π i) := by
  constructor
  intro s hs
  rw [isOpen_sigma_iff] at hs ⊢
  intro i
  rcases h₀ i with ⟨h₀⟩
  have h₁ : IsOpen (closure (Sigma.mk i ⁻¹' s))
  · apply h₀
    exact hs i
  suffices h₂ : Sigma.mk i ⁻¹' closure s = closure (Sigma.mk i ⁻¹' s)
  · rwa [h₂]
  apply IsOpenMap.preimage_closure_eq_closure_preimage
  intro U _
  · rw [isOpen_sigma_iff]
    intro j
    by_cases ij : i = j
    · rw [← ij]
      rw [sigma_mk_preimage_image_eq_self]
      assumption
    · rw [sigma_mk_preimage_image' ij]
      apply isOpen_empty
  · continuity
