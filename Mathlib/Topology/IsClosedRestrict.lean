/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Topology.Maps.Proper.Basic

/-! # Restriction of a closed compact set in a product space to a set of coordinates

We show that the image of a compact closed set `s` in a product `Π i : ι, α i` by
the restriction to a subset of coordinates `S : Set ι` is a closed set.

The idea of the proof is to use `isClosedMap_snd_of_compactSpace`, which is the fact that if
`X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map.

We remark that `s` is included in the set `Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)`, and we build
a homeomorphism `Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) ≃ₜ Sᶜ.restrict '' s × Π i : S, α i`.
`Sᶜ.restrict '' s` is a compact space since `s` is compact, and the lemma applies,
with `X = Sᶜ.restrict '' s` and `Y = Π i : S, α i`.

-/

open Set

variable {ι : Type*} {α : ι → Type*} {s : Set (Π i, α i)} {i : ι} {S : Set ι}

namespace Topology

open Classical in
/-- Given a set in a product space `s : Set (Π j, α j)` and a set of coordinates `S : Set ι`,
`Sᶜ.restrict '' s × (Π i : S, α i)` is the set of functions that coincide with an element of `s`
on `Sᶜ` and are arbitrary on `S`.
`reorderRestrictProd` sends a term of that type to `Π j, α j` by looking for the value at `j`
in one part of the product or the other depending on whether `j` is in `S` or not. -/
noncomputable def reorderRestrictProd (S : Set ι) (s : Set (Π j, α j))
    (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    Π j, α j :=
  fun j ↦ if h : j ∈ S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩

@[simp]
lemma reorderRestrictProd_of_mem (p : Sᶜ.restrict '' s × (Π i : S, α i)) (j : S) :
    reorderRestrictProd S s p j = (p.2 : Π j : ↑(S : Set ι), α j) j := by
  have hj : ↑j ∈ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]
lemma reorderRestrictProd_of_compl (p : Sᶜ.restrict '' s × (Π i : S, α i)) (j : (Sᶜ : Set ι)) :
    reorderRestrictProd S s p j = (p.1 : Π j : ↑(Sᶜ : Set ι), α j) j := by
  have hj : ↑j ∉ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]
lemma restrict_compl_reorderRestrictProd (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    Sᶜ.restrict (reorderRestrictProd S s p) = p.1 := by ext; simp

lemma continuous_reorderRestrictProd [∀ i, TopologicalSpace (α i)] :
    Continuous (reorderRestrictProd S s) := by
  refine continuous_pi fun j ↦ ?_
  simp only [reorderRestrictProd]
  split_ifs with h
  · fun_prop
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst

lemma reorderRestrictProd_mem_preimage_image_restrict (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    reorderRestrictProd S s p ∈ Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) := by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (restrict_compl_reorderRestrictProd p).symm⟩

@[simp]
lemma reorderRestrictProd_restrict_compl (x : Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)) :
    reorderRestrictProd S s ⟨⟨Sᶜ.restrict x, x.2⟩, fun i ↦ (x : Π j, α j) i⟩ = (x : Π j, α j) := by
  ext; simp [reorderRestrictProd]

/-- Homeomorphism between the set of functions that coincide with a given set of functions away
from a given set `S`, and dependent functions away from `S` times any value on `S`. -/
noncomputable
def _root_.Homeomorph.preimageImageRestrict (α : ι → Type*) [∀ i, TopologicalSpace (α i)]
    (S : Set ι) (s : Set (Π j, α j)) :
    Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) ≃ₜ Sᶜ.restrict '' s × (Π i : S, α i) where
  toFun x := ⟨⟨Sᶜ.restrict x, x.2⟩, fun i ↦ (x : Π j, α j) i⟩
  invFun p := ⟨reorderRestrictProd S s p, reorderRestrictProd_mem_preimage_image_restrict p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact ((Pi.continuous_restrict _).comp continuous_subtype_val).subtype_mk _
    · rw [continuous_pi_iff]
      exact fun _ ↦ (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := continuous_reorderRestrictProd.subtype_mk _

/-- The image by `preimageImageRestrict α S s` of `s` seen as a set of
`Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)` is a set of `Sᶜ.restrict '' s × (Π i : S, α i)`, and the
image of that set by `Prod.snd` is `S.restrict '' s`.

Used in `IsCompact.isClosed_image_restrict` to prove that the restriction of a compact closed set
in a product space to a set of coordinates is closed. -/
lemma image_snd_preimageImageRestrict [∀ i, TopologicalSpace (α i)] :
    Prod.snd '' (Homeomorph.preimageImageRestrict α S s ''
        ((fun (x : Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)) ↦ (x : Π j, α j)) ⁻¹' s))
      = S.restrict '' s := by
  ext x
  simp only [Homeomorph.preimageImageRestrict, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    mem_image, mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq,
    exists_and_right, exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨Sᶜ.restrict z, mem_image_of_mem Sᶜ.restrict hz_mem, z, hz_mem,
      ⟨⟨⟨z, hz_mem, rfl⟩, rfl⟩, hzx⟩⟩

end Topology

section IsClosed

variable [∀ i, TopologicalSpace (α i)]

/-- The restriction of a compact closed set in a product space to a set of coordinates is closed. -/
theorem IsCompact.isClosed_image_restrict (S : Set ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed (S.restrict '' s) := by
  rw [← Topology.image_snd_preimageImageRestrict]
  have : CompactSpace (Sᶜ.restrict '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image (Pi.continuous_restrict _))
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_subtype_val

lemma isClosedMap_restrict_of_compactSpace [∀ i, CompactSpace (α i)] :
    IsClosedMap (S.restrict : (Π i, α i) → _) := fun s hs ↦ by
  classical
  have : S.restrict (π := α) = Prod.fst ∘ (Homeomorph.piEquivPiSubtypeProd S α) := rfl
  rw [this, image_comp]
  exact isClosedMap_fst_of_compactSpace _ <| (Homeomorph.isClosed_image _).mpr hs

lemma IsClosed.isClosed_image_eval (i : ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed ((fun x ↦ x i) '' s) := by
  suffices IsClosed (Set.restrict {i} '' s) by
    have : Homeomorph.piUnique _ ∘ Set.restrict {i} = fun (x : Π j, α j) ↦ x i := rfl
    rwa [← this, image_comp, Homeomorph.isClosed_image (Homeomorph.piUnique _)]
  exact hs_compact.isClosed_image_restrict {i} hs_closed

end IsClosed
