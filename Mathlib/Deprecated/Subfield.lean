/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Deprecated.Subring

#align_import deprecated.subfield from "leanprover-community/mathlib"@"bd9851ca476957ea4549eb19b40e7b5ade9428cc"

/-!
# Unbundled subfields (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subfields. Instead of using this file, please use
`Subfield`, defined in `FieldTheory.Subfield`, for subfields of fields.

## Main definitions

`IsSubfield (S : Set F) : Prop` : the predicate that `S` is the underlying set of a subfield
of the field `F`. The bundled variant `Subfield F` should be used in preference to this.

## Tags

IsSubfield, subfield
-/


variable {F : Type*} [Field F] (S : Set F)

/-- `IsSubfield (S : Set F)` is the predicate saying that a given subset of a field is
the set underlying a subfield. This structure is deprecated; use the bundled variant
`Subfield F` to model subfields of a field. -/
structure IsSubfield extends IsSubring S : Prop where
  inv_mem : ∀ {x : F}, x ∈ S → x⁻¹ ∈ S
#align is_subfield IsSubfield

theorem IsSubfield.div_mem {S : Set F} (hS : IsSubfield S) {x y : F} (hx : x ∈ S) (hy : y ∈ S) :
    x / y ∈ S := by
  rw [div_eq_mul_inv]
  exact hS.toIsSubring.toIsSubmonoid.mul_mem hx (hS.inv_mem hy)
#align is_subfield.div_mem IsSubfield.div_mem

theorem IsSubfield.pow_mem {a : F} {n : ℤ} {s : Set F} (hs : IsSubfield s) (h : a ∈ s) :
    a ^ n ∈ s := by
  cases' n with n n
  · suffices a ^ (n : ℤ) ∈ s by exact this
    rw [zpow_natCast]
    exact hs.toIsSubring.toIsSubmonoid.pow_mem h
  · rw [zpow_negSucc]
    exact hs.inv_mem (hs.toIsSubring.toIsSubmonoid.pow_mem h)
#align is_subfield.pow_mem IsSubfield.pow_mem

theorem Univ.isSubfield : IsSubfield (@Set.univ F) :=
  { Univ.isSubmonoid, IsAddSubgroup.univ_addSubgroup with
    inv_mem := fun _ ↦ trivial }
#align univ.is_subfield Univ.isSubfield

theorem Preimage.isSubfield {K : Type*} [Field K] (f : F →+* K) {s : Set K} (hs : IsSubfield s) :
    IsSubfield (f ⁻¹' s) :=
  { f.isSubring_preimage hs.toIsSubring with
    inv_mem := fun {a} (ha : f a ∈ s) ↦ show f a⁻¹ ∈ s by
      rw [map_inv₀]
      exact hs.inv_mem ha }
#align preimage.is_subfield Preimage.isSubfield

theorem Image.isSubfield {K : Type*} [Field K] (f : F →+* K) {s : Set F} (hs : IsSubfield s) :
    IsSubfield (f '' s) :=
  { f.isSubring_image hs.toIsSubring with
    inv_mem := fun ⟨x, xmem, ha⟩ ↦ ⟨x⁻¹, hs.inv_mem xmem, ha ▸ map_inv₀ f x⟩ }
#align image.is_subfield Image.isSubfield

theorem Range.isSubfield {K : Type*} [Field K] (f : F →+* K) : IsSubfield (Set.range f) := by
  rw [← Set.image_univ]
  apply Image.isSubfield _ Univ.isSubfield
#align range.is_subfield Range.isSubfield

namespace Field

/-- `Field.closure s` is the minimal subfield that includes `s`. -/
def closure : Set F :=
  { x | ∃ y ∈ Ring.closure S, ∃ z ∈ Ring.closure S, y / z = x }
#align field.closure Field.closure

variable {S}

theorem ring_closure_subset : Ring.closure S ⊆ closure S :=
  fun x hx ↦ ⟨x, hx, 1, Ring.closure.isSubring.toIsSubmonoid.one_mem, div_one x⟩
#align field.ring_closure_subset Field.ring_closure_subset

theorem closure.isSubmonoid : IsSubmonoid (closure S) :=
  { mul_mem := by
      rintro _ _ ⟨p, hp, q, hq, hq0, rfl⟩ ⟨r, hr, s, hs, hs0, rfl⟩
      exact ⟨p * r, IsSubmonoid.mul_mem Ring.closure.isSubring.toIsSubmonoid hp hr, q * s,
        IsSubmonoid.mul_mem Ring.closure.isSubring.toIsSubmonoid hq hs,
        (div_mul_div_comm _ _ _ _).symm⟩
    one_mem := ring_closure_subset <| IsSubmonoid.one_mem Ring.closure.isSubring.toIsSubmonoid }
#align field.closure.is_submonoid Field.closure.isSubmonoid

theorem closure.isSubfield : IsSubfield (closure S) :=
  { closure.isSubmonoid with
    add_mem := by
      intro a b ha hb
      rcases id ha with ⟨p, hp, q, hq, rfl⟩
      rcases id hb with ⟨r, hr, s, hs, rfl⟩
      by_cases hq0 : q = 0
      · rwa [hq0, div_zero, zero_add]
      by_cases hs0 : s = 0
      · rwa [hs0, div_zero, add_zero]
      exact ⟨p * s + q * r,
        IsAddSubmonoid.add_mem Ring.closure.isSubring.toIsAddSubgroup.toIsAddSubmonoid
          (Ring.closure.isSubring.toIsSubmonoid.mul_mem hp hs)
          (Ring.closure.isSubring.toIsSubmonoid.mul_mem hq hr),
        q * s, Ring.closure.isSubring.toIsSubmonoid.mul_mem hq hs, (div_add_div p r hq0 hs0).symm⟩
    zero_mem := ring_closure_subset Ring.closure.isSubring.toIsAddSubgroup.toIsAddSubmonoid.zero_mem
    neg_mem := by
      rintro _ ⟨p, hp, q, hq, rfl⟩
      exact ⟨-p, Ring.closure.isSubring.toIsAddSubgroup.neg_mem hp, q, hq, neg_div q p⟩
    inv_mem := by
      rintro _ ⟨p, hp, q, hq, rfl⟩
      exact ⟨q, hq, p, hp, (inv_div _ _).symm⟩ }
#align field.closure.is_subfield Field.closure.isSubfield

theorem mem_closure {a : F} (ha : a ∈ S) : a ∈ closure S :=
  ring_closure_subset <| Ring.mem_closure ha
#align field.mem_closure Field.mem_closure

theorem subset_closure : S ⊆ closure S :=
  fun _ ↦ mem_closure
#align field.subset_closure Field.subset_closure

theorem closure_subset {T : Set F} (hT : IsSubfield T) (H : S ⊆ T) : closure S ⊆ T := by
  rintro _ ⟨p, hp, q, hq, hq0, rfl⟩
  exact hT.div_mem (Ring.closure_subset hT.toIsSubring H hp)
    (Ring.closure_subset hT.toIsSubring H hq)
#align field.closure_subset Field.closure_subset

theorem closure_subset_iff {s t : Set F} (ht : IsSubfield t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, closure_subset ht⟩
#align field.closure_subset_iff Field.closure_subset_iff

theorem closure_mono {s t : Set F} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.isSubfield <| Set.Subset.trans H subset_closure
#align field.closure_mono Field.closure_mono

end Field

theorem isSubfield_iUnion_of_directed {ι : Type*} [Nonempty ι] {s : ι → Set F}
    (hs : ∀ i, IsSubfield (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubfield (⋃ i, s i) :=
  { inv_mem := fun hx ↦
      let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      Set.mem_iUnion.2 ⟨i, (hs i).inv_mem hi⟩
    toIsSubring := isSubring_iUnion_of_directed (fun i ↦ (hs i).toIsSubring) directed }
#align is_subfield_Union_of_directed isSubfield_iUnion_of_directed

theorem IsSubfield.inter {S₁ S₂ : Set F} (hS₁ : IsSubfield S₁) (hS₂ : IsSubfield S₂) :
    IsSubfield (S₁ ∩ S₂) :=
  { IsSubring.inter hS₁.toIsSubring hS₂.toIsSubring with
    inv_mem := fun hx ↦ ⟨hS₁.inv_mem hx.1, hS₂.inv_mem hx.2⟩ }
#align is_subfield.inter IsSubfield.inter

theorem IsSubfield.iInter {ι : Sort*} {S : ι → Set F} (h : ∀ y : ι, IsSubfield (S y)) :
    IsSubfield (Set.iInter S) :=
  { IsSubring.iInter fun y ↦ (h y).toIsSubring with
    inv_mem := fun hx ↦ Set.mem_iInter.2 fun y ↦ (h y).inv_mem <| Set.mem_iInter.1 hx y }
#align is_subfield.Inter IsSubfield.iInter
