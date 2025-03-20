/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Inv

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `Fintype`s.

# Main definitions

 - `Function.Embedding.toEquivRange`: computably turn an embedding of a
   fintype into an `Equiv` of the domain to its range
 - `Equiv.Perm.viaFintypeEmbedding : Perm α → (α ↪ β) → Perm β` extends the domain of
   a permutation, fixing everything outside the range of the embedding

# Implementation details

 - `Function.Embedding.toEquivRange` uses a computable inverse, but one that has poor
   computational performance, since it operates by exhaustive search over the input `Fintype`s.
-/

assert_not_exists Equiv.Perm.sign

section Fintype

variable {α β : Type*} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)

/-- Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ Set.range f`,
if `α` is a `Fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known, use `Equiv.ofLeftInverse'` or
`Equiv.ofLeftInverse` instead. This is the computable version of `Equiv.ofInjective`.
-/
def Function.Embedding.toEquivRange : α ≃ Set.range f :=
  ⟨fun a => ⟨f a, Set.mem_range_self a⟩, f.invOfMemRange, fun _ => by simp, fun _ => by simp⟩

@[simp]
theorem Function.Embedding.toEquivRange_apply (a : α) :
    f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩ :=
  rfl

@[simp]
theorem Function.Embedding.toEquivRange_symm_apply_self (a : α) :
    f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a := by simp [Equiv.symm_apply_eq]

theorem Function.Embedding.toEquivRange_eq_ofInjective :
    f.toEquivRange = Equiv.ofInjective f f.injective := by
  ext
  simp

/-- Extend the domain of `e : Equiv.Perm α`, mapping it through `f : α ↪ β`.
Everything outside of `Set.range f` is kept fixed. Has poor computational performance,
due to exhaustive searching in constructed inverse due to using `Function.Embedding.toEquivRange`.
When a better `α ≃ Set.range f` is known, use `Equiv.Perm.viaSetRange`.
When `[Fintype α]` is not available, a noncomputable version is available as
`Equiv.Perm.viaEmbedding`.
-/
def Equiv.Perm.viaFintypeEmbedding : Equiv.Perm β :=
  e.extendDomain f.toEquivRange

@[simp]
theorem Equiv.Perm.viaFintypeEmbedding_apply_image (a : α) :
    e.viaFintypeEmbedding f (f a) = f (e a) := by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert Equiv.Perm.extendDomain_apply_image e (Function.Embedding.toEquivRange f) a

theorem Equiv.Perm.viaFintypeEmbedding_apply_mem_range {b : β} (h : b ∈ Set.range f) :
    e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩)) := by
  simp only [viaFintypeEmbedding, Function.Embedding.invOfMemRange]
  rw [Equiv.Perm.extendDomain_apply_subtype]
  congr

theorem Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range {b : β} (h : b ∉ Set.range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]

end Fintype

namespace Equiv

variable {α β : Type*} [Finite α]

/-- If `e` is an equivalence between two subtypes of a finite type `α`, `e.toCompl`
is an equivalence between the complement of those subtypes.

See also `Equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known. -/
noncomputable def toCompl {p q : α → Prop} (e : { x // p x } ≃ { x // q x }) :
    { x // ¬p x } ≃ { x // ¬q x } := by
  apply Classical.choice
  cases nonempty_fintype α
  classical
  exact Fintype.card_eq.mp <| Fintype.card_compl_eq_card_compl _ _ <| Fintype.card_congr e

variable {p q : α → Prop} [DecidablePred p] [DecidablePred q]

/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.extendSubtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbitrary outside.

Note that when `p = q`, `Equiv.Perm.subtypeCongr e (Equiv.refl _)` can be used instead. -/
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl

theorem extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    e.extendSubtype x = e ⟨x, hx⟩ := by
  dsimp only [extendSubtype]
  simp only [subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [sumCompl_symm_apply_of_pos hx, Sum.map_inl, sumCompl_apply_inl]

theorem extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    q (e.extendSubtype x) := by
  convert (e ⟨x, hx⟩).2
  rw [e.extendSubtype_apply_of_mem _ hx]

theorem extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ := by
  dsimp only [extendSubtype]
  simp only [subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [sumCompl_symm_apply_of_neg hx, Sum.map_inr, sumCompl_apply_inr]

theorem extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    ¬q (e.extendSubtype x) := by
  convert (e.toCompl ⟨x, hx⟩).2
  rw [e.extendSubtype_apply_of_not_mem _ hx]

end Equiv
