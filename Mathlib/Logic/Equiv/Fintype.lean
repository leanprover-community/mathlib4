/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Inv

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `Fintype`s.

## Main definitions

- `Function.Embedding.toEquivRange`: computably turn an embedding of a
  fintype into an `Equiv` of the domain to its range
- `Equiv.Perm.viaFintypeEmbedding : Perm α → (α ↪ β) → Perm β` extends the domain of
  a permutation, fixing everything outside the range of the embedding

## Implementation details

- `Function.Embedding.toEquivRange` uses a computable inverse, but one that has poor
  computational performance, since it operates by exhaustive search over the input `Fintype`s.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists Equiv.Perm.sign

section Fintype

variable {α β : Type*} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)

/-- Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ Set.range f`,
if `α` is a `Fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known, use `Equiv.ofLeftInverse'` or
`Equiv.ofLeftInverse` instead. This is the computable version of `Equiv.ofInjective`.
-/
def Function.Embedding.toEquivRange : α ≃ Set.range f where
  toFun := fun a => ⟨f a, Set.mem_range_self a⟩
  invFun := f.invOfMemRange
  left_inv := fun _ => by simp
  right_inv := fun _ => by simp

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
  rw [Equiv.Perm.extendDomain_apply_subtype _ _ h]
  congr

theorem Equiv.Perm.viaFintypeEmbedding_apply_notMem_range {b : β} (h : b ∉ Set.range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]

end Fintype

namespace Equiv

variable {α β : Type*}

/-- If two sets have the same finite cardinality, their set differences are equivalent. -/
noncomputable def setDiffEquiv {s t : Set α} [Fintype s] [Fintype t]
    (h : Fintype.card s = Fintype.card t) : (s \ t : Set α) ≃ (t \ s : Set α) := by
  classical
  let fs : Finset α := Finset.univ.map (Function.Embedding.subtype (· ∈ s))
  let ft : Finset α := Finset.univ.map (Function.Embedding.subtype (· ∈ t))
  have hs (x : α) : x ∈ fs ↔ x ∈ s := by simp [fs]
  have ht (x : α) : x ∈ ft ↔ x ∈ t := by simp [ft]
  have hst (x : α) : x ∈ fs \ ft ↔ x ∈ s \ t := by simp [hs, ht]
  have hts (x : α) : x ∈ ft \ fs ↔ x ∈ t \ s := by simp [hs, ht]
  have hc : fs.card = ft.card := by
    rw [← Fintype.subtype_card fs hs, ← Fintype.subtype_card ft ht]; convert h
  replace hc := Finset.card_sdiff_comm hc
  rw [← Fintype.subtype_card (fs \ ft) hst, ← Fintype.subtype_card (ft \ fs) hts] at hc
  exact ((Fintype.card_eq (_F := (_)) (_G := (_))).mp hc).some

open Classical in
/-- If `e` is an equivalence between two subtypes of a type `α`, `e.toCompl`
is an equivalence between the complement of those subtypes.

See also `Equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known. -/
noncomputable def toCompl {p q : α → Prop} [Finite {x | p x}]
    (e : { x | p x } ≃ { x | q x }) : { x | ¬p x } ≃ { x | ¬q x } :=
  let sp : Set α := {x | p x}
  let sq : Set α := {x | q x}
  letI : Fintype sp := Fintype.ofFinite sp
  letI : Fintype sq := Fintype.ofEquiv sp e
  have h := setDiffEquiv (Fintype.card_congr e)
  have hpc : spᶜ = (sq \ sp) ∪ (sp ∪ sq)ᶜ := by ext; simp; tauto
  have hqc : sqᶜ = (sp \ sq) ∪ (sp ∪ sq)ᶜ := by ext; simp; tauto
  let epc := (Equiv.setCongr hpc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  let eqc := (Equiv.setCongr hqc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  epc.trans <| .trans (h.symm.sumCongr <| .refl _) eqc.symm

variable {p q : α → Prop} [DecidablePred p] [DecidablePred q] [Finite {x | p x}]

/-- If `e` is an equivalence between two subtypes of a type `α`, `e.extendSubtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbitrary outside.

Note that when `p = q`, `Equiv.Perm.subtypeCongr e (Equiv.refl _)` can be used instead. -/
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl

theorem extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    e.extendSubtype x = e ⟨x, hx⟩ := by
  simp [extendSubtype, subtypeCongr, sumCompl_symm_apply_of_pos hx]

theorem extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    q (e.extendSubtype x) :=
  (e.extendSubtype_apply_of_mem _ hx).symm ▸ (e ⟨x, hx⟩).2

theorem extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ := by
  simp only [extendSubtype, subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply,
    sumCompl_symm_apply_of_neg hx, Sum.map_inr, sumCompl_apply_inr]
  rfl

theorem extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    ¬q (e.extendSubtype x) :=
  e.extendSubtype_apply_of_not_mem _ hx ▸ (e.toCompl ⟨x, hx⟩).2

/-- Given two injective functions `f` and `g` from a finite type `α` to any type `β`,
there exists a permutation of `β` that maps `f` to `g`. -/
theorem Perm.exists_extending_pair [Finite α]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Perm β, ∀ a, σ (f a) = g a := by
  classical
  have : Finite {x | x ∈ Set.range f} := .of_surjective _ (Set.codRestrict_range_surjective f)
  refine ⟨((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).extendSubtype, ?_⟩
  simp [Equiv.extendSubtype_apply_of_mem]

/-- Any two same-cardinality finsets are related by a permutation. -/
theorem Perm.exists_map_finset_eq
    (s t : Finset β) (h : s.card = t.card) :
    ∃ σ : Perm β, s.map σ.toEmbedding = t := by
  classical
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair
    (fun x : s => (x : β)) (fun x : s => ((s.equivOfCardEq h) x : β))
    Subtype.val_injective (Subtype.val_injective.comp (s.equivOfCardEq h).injective)
  refine ⟨σ, Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [h])⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  exact (hσ ⟨a, ha⟩) ▸ ((s.equivOfCardEq h) ⟨a, ha⟩).2

end Equiv
