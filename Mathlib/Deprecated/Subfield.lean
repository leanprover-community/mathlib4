/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow

! This file was ported from Lean 3 source module deprecated.subfield
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Deprecated.Subring

/-!
# Unbundled subfields (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subfields. Instead of using this file, please use
`subfield`, defined in `field_theory.subfield`, for subfields of fields.

## Main definitions

`is_subfield (S : set F) : Prop` : the predicate that `S` is the underlying set of a subfield
of the field `F`. The bundled variant `subfield F` should be used in preference to this.

## Tags

is_subfield
-/


variable {F : Type _} [Field F] (S : Set F)

/-- `is_subfield (S : set F)` is the predicate saying that a given subset of a field is
the set underlying a subfield. This structure is deprecated; use the bundled variant
`subfield F` to model subfields of a field. -/
structure IsSubfield extends IsSubring S : Prop where
  inv_mem : ∀ {x : F}, x ∈ S → x⁻¹ ∈ S
#align is_subfield IsSubfield

theorem IsSubfield.div_mem {S : Set F} (hS : IsSubfield S) {x y : F} (hx : x ∈ S) (hy : y ∈ S) :
    x / y ∈ S := by
  rw [div_eq_mul_inv]
  exact hS.to_is_subring.to_is_submonoid.mul_mem hx (hS.inv_mem hy)
#align is_subfield.div_mem IsSubfield.div_mem

theorem IsSubfield.pow_mem {a : F} {n : ℤ} {s : Set F} (hs : IsSubfield s) (h : a ∈ s) :
    a ^ n ∈ s := by
  cases n
  · rw [zpow_ofNat]
    exact hs.to_is_subring.to_is_submonoid.pow_mem h
  · rw [zpow_negSucc]
    exact hs.inv_mem (hs.to_is_subring.to_is_submonoid.pow_mem h)
#align is_subfield.pow_mem IsSubfield.pow_mem

theorem Univ.is_subfield : IsSubfield (@Set.univ F) :=
  { Univ.is_submonoid, IsAddSubgroup.univ_add_subgroup with inv_mem := by intros <;> trivial }
#align univ.is_subfield Univ.is_subfield

theorem Preimage.is_subfield {K : Type _} [Field K] (f : F →+* K) {s : Set K} (hs : IsSubfield s) :
    IsSubfield (f ⁻¹' s) :=
  { f.is_subring_preimage hs.to_is_subring with
    inv_mem := fun a (ha : f a ∈ s) =>
      show f a⁻¹ ∈ s by
        rw [map_inv₀]
        exact hs.inv_mem ha }
#align preimage.is_subfield Preimage.is_subfield

theorem Image.is_subfield {K : Type _} [Field K] (f : F →+* K) {s : Set F} (hs : IsSubfield s) :
    IsSubfield (f '' s) :=
  { f.is_subring_image hs.to_is_subring with
    inv_mem := fun a ⟨x, xmem, ha⟩ => ⟨x⁻¹, hs.inv_mem xmem, ha ▸ map_inv₀ f _⟩ }
#align image.is_subfield Image.is_subfield

theorem Range.is_subfield {K : Type _} [Field K] (f : F →+* K) : IsSubfield (Set.range f) :=
  by
  rw [← Set.image_univ]
  apply Image.is_subfield _ Univ.is_subfield
#align range.is_subfield Range.is_subfield

namespace Field

/-- `field.closure s` is the minimal subfield that includes `s`. -/
def closure : Set F :=
  { x | ∃ y ∈ Ring.closure S, ∃ z ∈ Ring.closure S, y / z = x }
#align field.closure Field.closure

variable {S}

theorem ring_closure_subset : Ring.closure S ⊆ closure S := fun x hx =>
  ⟨x, hx, 1, Ring.closure.is_subring.to_is_submonoid.one_mem, div_one x⟩
#align field.ring_closure_subset Field.ring_closure_subset

theorem closure.is_submonoid : IsSubmonoid (closure S) :=
  { mul_mem := by
      rintro _ _ ⟨p, hp, q, hq, hq0, rfl⟩ ⟨r, hr, s, hs, hs0, rfl⟩ <;>
        exact
          ⟨p * r, IsSubmonoid.mul_mem ring.closure.is_subring.to_is_submonoid hp hr, q * s,
            IsSubmonoid.mul_mem ring.closure.is_subring.to_is_submonoid hq hs,
            (div_mul_div_comm _ _ _ _).symm⟩
    one_mem := ring_closure_subset <| IsSubmonoid.one_mem Ring.closure.is_subring.to_is_submonoid }
#align field.closure.is_submonoid Field.closure.is_submonoid

theorem closure.is_subfield : IsSubfield (closure S) :=
  have h0 : (0 : F) ∈ closure S :=
    ring_closure_subset <| Ring.closure.is_subring.to_is_add_subgroup.to_is_add_submonoid.zero_mem
  {
    closure.is_submonoid with
    add_mem := by
      intro a b ha hb
      rcases id ha with ⟨p, hp, q, hq, rfl⟩
      rcases id hb with ⟨r, hr, s, hs, rfl⟩
      classical
        by_cases hq0 : q = 0
        · simp [hb, hq0]
        by_cases hs0 : s = 0
        · simp [ha, hs0]
        exact
          ⟨p * s + q * r,
            IsAddSubmonoid.add_mem ring.closure.is_subring.to_is_add_subgroup.to_is_add_submonoid
              (ring.closure.is_subring.to_is_submonoid.mul_mem hp hs)
              (ring.closure.is_subring.to_is_submonoid.mul_mem hq hr),
            q * s, ring.closure.is_subring.to_is_submonoid.mul_mem hq hs,
            (div_add_div p r hq0 hs0).symm⟩
    zero_mem := h0
    neg_mem := by
      rintro _ ⟨p, hp, q, hq, rfl⟩
      exact ⟨-p, ring.closure.is_subring.to_is_add_subgroup.neg_mem hp, q, hq, neg_div q p⟩
    inv_mem := by
      rintro _ ⟨p, hp, q, hq, rfl⟩
      exact ⟨q, hq, p, hp, (inv_div _ _).symm⟩ }
#align field.closure.is_subfield Field.closure.is_subfield

theorem mem_closure {a : F} (ha : a ∈ S) : a ∈ closure S :=
  ring_closure_subset <| Ring.mem_closure ha
#align field.mem_closure Field.mem_closure

theorem subset_closure : S ⊆ closure S := fun _ => mem_closure
#align field.subset_closure Field.subset_closure

theorem closure_subset {T : Set F} (hT : IsSubfield T) (H : S ⊆ T) : closure S ⊆ T := by
  rintro _ ⟨p, hp, q, hq, hq0, rfl⟩ <;>
    exact
      hT.div_mem (Ring.closure_subset hT.to_is_subring H hp)
        (Ring.closure_subset hT.to_is_subring H hq)
#align field.closure_subset Field.closure_subset

theorem closure_subset_iff {s t : Set F} (ht : IsSubfield t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, closure_subset ht⟩
#align field.closure_subset_iff Field.closure_subset_iff

theorem closure_mono {s t : Set F} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.is_subfield <| Set.Subset.trans H subset_closure
#align field.closure_mono Field.closure_mono

end Field

theorem is_subfield_Union_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set F}
    (hs : ∀ i, IsSubfield (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubfield (⋃ i, s i) :=
  { inv_mem := fun x hx =>
      let ⟨i, hi⟩ := Set.mem_unionᵢ.1 hx
      Set.mem_unionᵢ.2 ⟨i, (hs i).inv_mem hi⟩
    to_is_subring := is_subring_Union_of_directed (fun i => (hs i).to_is_subring) Directed }
#align is_subfield_Union_of_directed is_subfield_Union_of_directed

theorem IsSubfield.inter {S₁ S₂ : Set F} (hS₁ : IsSubfield S₁) (hS₂ : IsSubfield S₂) :
    IsSubfield (S₁ ∩ S₂) :=
  { IsSubring.inter hS₁.to_is_subring hS₂.to_is_subring with
    inv_mem := fun x hx => ⟨hS₁.inv_mem hx.1, hS₂.inv_mem hx.2⟩ }
#align is_subfield.inter IsSubfield.inter

theorem IsSubfield.Inter {ι : Sort _} {S : ι → Set F} (h : ∀ y : ι, IsSubfield (S y)) :
    IsSubfield (Set.interᵢ S) :=
  { IsSubring.Inter fun y => (h y).to_is_subring with
    inv_mem := fun x hx => Set.mem_interᵢ.2 fun y => (h y).inv_mem <| Set.mem_interᵢ.1 hx y }
#align is_subfield.Inter IsSubfield.Inter

