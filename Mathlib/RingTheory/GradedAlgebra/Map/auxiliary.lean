import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Ring.Submonoid.Pointwise

open Pointwise in
/-- A lemma that exists for `Submodule`s in Mathlib but not for `AddSubmonoid`s: -/
lemma AddSubmonoid.one_le {A : Type*} [AddMonoidWithOne A] {P : AddSubmonoid A} :
  (1 : AddSubmonoid A) ≤ P ↔ (1 : A) ∈ P := by
  rw [AddSubmonoid.one_eq_closure, AddSubmonoid.closure_le, Set.singleton_subset_iff]
  rfl

open DirectSum in
/-- An additional _of lemma for an iso already present in Mathlib -/
@[simp] lemma DirectSum.sigmaCurry_of
    {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, DecidableEq (α i)]
    {M : (i : ι) → α i → Type*} [∀ i : ι, ∀ j : α i, AddCommMonoid (M i j)]
    (ij : (i : ι) × α i) (m : M ij.fst ij.snd) :
    (sigmaCurryEquiv) ((of (fun ij' ↦ M ij'.fst ij'.snd) ij ) m)
    = (of (fun i' ↦ ⨁ (j' : α i'), M i' j') ij.fst) ((of (fun j' ↦ M ij.fst j') ij.snd ) m)
  := by
  exact DFinsupp.sigmaCurry_single ij m

@[simp]
/- An additional _of lemma for an iso already present in Mathlib -/
lemma DirectSum.equivCongrLeft_of
    {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
    {κ : Type*} [DecidableEq κ] (h : ι ≃ κ) (k : κ) (m : M (h.symm k)) :
    (equivCongrLeft h) ((of M (h.symm k)) m) = (of (fun k ↦ M (h.symm k)) k) m
  := by
  exact DFinsupp.comapDomain'_single (⇑h.symm) h.right_inv k m
