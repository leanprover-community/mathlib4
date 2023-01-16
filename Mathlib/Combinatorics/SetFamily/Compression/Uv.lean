/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.set_family.compression.uv
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Card

/-!
# UV-compressions

This file defines UV-compression. It is an operation on a set family that reduces its shadow.

UV-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

UV-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `uv.compress`: `compress u v a` is `a` compressed along `u` and `v`.
* `uv.compression`: `compression u v s` is the compression of the set family `s` along `u` and `v`.
  It is the compressions of the elements of `s` whose compression is not already in `s` along with
  the element whose compression is already in `s`. This way of splitting into what moves and what
  does not ensures the compression doesn't squash the set family, which is proved by
  `uv.card_compress`.

## Notation

`𝓒` (typed with `\MCC`) is notation for `uv.compression` in locale `finset_family`.

## Notes

Even though our emphasis is on `finset α`, we define UV-compressions more generally in a generalized
boolean algebra, so that one can use it for `set α`.

## TODO

Prove that compressing reduces the size of shadow. This result and some more already exist on the
branch `combinatorics`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/


open Finset

variable {α : Type _}

/-- UV-compression is injective on the elements it moves. See `uv.compress`. -/
theorem sup_sdiff_inj_on [GeneralizedBooleanAlgebra α] (u v : α) :
    { x | Disjoint u x ∧ v ≤ x }.InjOn fun x => (x ⊔ u) \ v :=
  by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v :=
    by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h
#align sup_sdiff_inj_on sup_sdiff_inj_on

-- The namespace is here to distinguish from other compressions.
namespace Uv

/-! ### UV-compression in generalized boolean algebras -/


section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableRel (@Disjoint α _ _)]
  [DecidableRel ((· ≤ ·) : α → α → Prop)] {s : Finset α} {u v a b : α}

attribute [local instance] decidableEqOfDecidableLe

/-- To UV-compress `a`, if it doesn't touch `U` and does contain `V`, we remove `V` and
put `U` in. We'll only really use this when `|U| = |V|` and `U ∩ V = ∅`. -/
def compress (u v a : α) : α :=
  if Disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a
#align uv.compress Uv.compress

/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
def compression (u v : α) (s : Finset α) :=
  (s.filter fun a => compress u v a ∈ s) ∪ (s.image <| compress u v).filter fun a => a ∉ s
#align uv.compression Uv.compression

-- mathport name: uv.compression
scoped[FinsetFamily] notation "𝓒 " => Uv.compression

/-- `is_compressed u v s` expresses that `s` is UV-compressed. -/
def IsCompressed (u v : α) (s : Finset α) :=
  𝓒 u v s = s
#align uv.is_compressed Uv.IsCompressed

theorem compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v ≤ a) :
    compress u v a = (a ⊔ u) \ v :=
  if_pos ⟨hua, hva⟩
#align uv.compress_of_disjoint_of_le Uv.compress_of_disjoint_of_le

/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
theorem mem_compression :
    a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a := by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm' (a ∉ s)]
#align uv.mem_compression Uv.mem_compression

@[simp]
theorem compress_self (u a : α) : compress u u a = a :=
  by
  unfold compress
  split_ifs
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl
#align uv.compress_self Uv.compress_self

@[simp]
theorem compression_self (u : α) (s : Finset α) : 𝓒 u u s = s :=
  by
  unfold compression
  convert union_empty s
  · ext a
    rw [mem_filter, compress_self, and_self_iff]
  · refine' eq_empty_of_forall_not_mem fun a ha => _
    simp_rw [mem_filter, mem_image, compress_self] at ha
    obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := ha
    exact hb' hb
#align uv.compression_self Uv.compression_self

/-- Any family is compressed along two identical elements. -/
theorem is_compressed_self (u : α) (s : Finset α) : IsCompressed u u s :=
  compression_self u s
#align uv.is_compressed_self Uv.is_compressed_self

theorem compress_disjoint (u v : α) :
    Disjoint (s.filter fun a => compress u v a ∈ s)
      ((s.image <| compress u v).filter fun a => a ∉ s) :=
  disjoint_left.2 fun a ha₁ ha₂ => (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1
#align uv.compress_disjoint Uv.compress_disjoint

/-- Compressing an element is idempotent. -/
@[simp]
theorem compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a :=
  by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_iff.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl
#align uv.compress_idem Uv.compress_idem

theorem compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s :=
  by
  rw [mem_compression]
  by_cases compress u v a ∈ s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩
#align uv.compress_mem_compression Uv.compress_mem_compression

-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
theorem compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) : compress u v a ∈ 𝓒 u v s :=
  by
  rw [mem_compression] at ha⊢
  simp only [compress_idem, exists_prop]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩
#align uv.compress_mem_compression_of_mem_compression Uv.compress_mem_compression_of_mem_compression

/-- Compressing a family is idempotent. -/
@[simp]
theorem compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s :=
  by
  have h : filter (fun a => compress u v a ∉ 𝓒 u v s) (𝓒 u v s) = ∅ :=
    filter_false_of_mem fun a ha h => h <| compress_mem_compression_of_mem_compression ha
  rw [compression, image_filter, h, image_empty, ← h]
  exact filter_union_filter_neg_eq _ (compression u v s)
#align uv.compression_idem Uv.compression_idem

/-- Compressing a family doesn't change its size. -/
theorem card_compression (u v : α) (s : Finset α) : (𝓒 u v s).card = s.card :=
  by
  rw [compression, card_disjoint_union (compress_disjoint _ _), image_filter, card_image_of_inj_on,
    ← card_disjoint_union, filter_union_filter_neg_eq]
  · rw [disjoint_iff_inter_eq_empty]
    exact filter_inter_filter_neg_eq _ _ _
  intro a ha b hb hab
  dsimp at hab
  rw [mem_coe, mem_filter, Function.comp_apply] at ha hb
  rw [compress] at ha hab
  split_ifs  at ha hab with has
  · rw [compress] at hb hab
    split_ifs  at hb hab with hbs
    · exact sup_sdiff_inj_on u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim
#align uv.card_compression Uv.card_compression

/-- If `a` is in the family compression and can be compressed, then its compression is in the
original family. -/
theorem sup_sdiff_mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hua : Disjoint u a) :
    (a ⊔ u) \ v ∈ s :=
  by
  rw [mem_compression, compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ :=
    by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine' hua.mono_right _
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact sdiff_le_sdiff_right le_sup_right
  have hv : v = ⊥ := by
    rw [← disjoint_self]
    apply Disjoint.mono_right hva
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact disjoint_sdiff_self_right
  rwa [hu, hv, compress_self, sup_bot_eq, sdiff_bot]
#align uv.sup_sdiff_mem_of_mem_compression Uv.sup_sdiff_mem_of_mem_compression

/-- If `a` is in the `u, v`-compression but `v ≤ a`, then `a` must have been in the original
family. -/
theorem mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hvu : v = ⊥ → u = ⊥) : a ∈ s :=
  by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs  at h
  · rw [← h, le_sdiff_iff] at hva
    rw [hvu hva, hva, sup_bot_eq, sdiff_bot] at h
    rwa [← h]
  · rwa [← h]
#align uv.mem_of_mem_compression Uv.mem_of_mem_compression

end GeneralizedBooleanAlgebra

/-! ### UV-compression on finsets -/


open FinsetFamily

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {U V A : Finset α}

/-- Compressing a finset doesn't change its size. -/
theorem card_compress (hUV : U.card = V.card) (A : Finset α) : (compress U V A).card = A.card :=
  by
  unfold compress
  split_ifs
  ·
    rw [card_sdiff (h.2.trans le_sup_left), sup_eq_union, card_disjoint_union h.1.symm, hUV,
      add_tsub_cancel_right]
  · rfl
#align uv.card_compress Uv.card_compress

end Uv

