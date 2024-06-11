/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.Reflection

/-!
# Comparison of two definitions of root pairing

This file contains a proof that two definitions of root pairing are equivalent.
-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The old definition of root pairing. -/
structure RootPairingOld extends PerfectPairing R M N :=
  /-- An indexed family of roots. -/
  root : ι ↪ M
  /-- An indexed family of coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  mapsTo_preReflection_root :
    ∀ i, MapsTo (preReflection (root i) (toLin.flip (coroot i))) (range root) (range root)
  mapsTo_preReflection_coroot :
    ∀ i, MapsTo (preReflection (coroot i) (toLin (root i))) (range coroot) (range coroot)

/-- The new definition of root pairing. -/
structure RootPairingNew extends PerfectPairing R M N :=
  /-- An indexed family of roots. -/
  root : ι ↪ M
  /-- An indexed family of coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  /-- An indexed family of permutations of the indexing set, induced by reflections. -/
  reflection_perm : ι → (ι ≃ ι)
  reflection_perm_root : ∀ i j,
    (preReflection (root i) (toLin.flip (coroot i))) (root j) = root ((reflection_perm i) j)
  reflection_perm_coroot : ∀ i j,
    (preReflection (coroot i) (toLin (root i))) (coroot j) = coroot ((reflection_perm i) j)

end

namespace RootPairingOld

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- We produce an old-style root pairing from a new-style root pairing. -/
def old_from_new (P : RootPairingNew ι R M N) : RootPairingOld ι R M N where
  toLin := P.toLin
  bijectiveLeft := P.bijectiveLeft
  bijectiveRight := P.bijectiveRight
  root := P.root
  coroot := P.coroot
  root_coroot_two := P.root_coroot_two
  mapsTo_preReflection_root i := by
    intro x hx
    obtain ⟨j, hj⟩ := hx
    simp only [mem_range]
    use P.reflection_perm i j
    rw [← P.reflection_perm_root i j, ← hj]
  mapsTo_preReflection_coroot i := by
    intro x hx
    obtain ⟨j, hj⟩ := hx
    simp only [mem_range]
    use P.reflection_perm i j
    rw [← P.reflection_perm_coroot i j, ← hj]

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
protected def flip (P : RootPairingOld ι R M N) : RootPairingOld ι R N M :=
  { P.toPerfectPairing.flip with
    root := P.coroot
    coroot := P.root
    root_coroot_two := P.root_coroot_two
    mapsTo_preReflection_root := P.mapsTo_preReflection_coroot
    mapsTo_preReflection_coroot := P.mapsTo_preReflection_root }

/-- The reflection associated to a root. -/
def reflection (P : RootPairingOld ι R M N) (i : ι) : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

lemma coroot_root_two (P : RootPairingOld ι R M N) (i : ι) :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp [P.root_coroot_two i]

theorem reflection_mapsto_root (P : RootPairingOld ι R M N) (i : ι) :
    MapsTo (P.reflection i) (range P.root) (range P.root) :=
  P.mapsTo_preReflection_root i

theorem exist_root_reflection (P : RootPairingOld ι R M N) (i j : ι) :
    ∃ k, (P.reflection i) (P.root j) = P.root k := by
  refine exists_range_iff.mp <| exists_eq_right'.mpr ?_
  have h := P.reflection_mapsto_root i
  simp_all only [mapsTo_range_iff, mem_range]

theorem root_reflection_comp_self (P : RootPairingOld ι R M N) (i j : ι) :
    (P.exist_root_reflection i (P.exist_root_reflection i j).choose).choose = j := by
  refine (Embedding.injective P.root) ?_
  rw [← (P.exist_root_reflection i _).choose_spec, ← (P.exist_root_reflection i j).choose_spec]
  exact (LinearEquiv.eq_symm_apply (P.reflection i)).mp rfl

/-- The bijection on the indexing set induced by reflection. -/
@[simps]
def reflection_in (P : RootPairingOld ι R M N) (i : ι) : ι ≃ ι where
  toFun j := (P.exist_root_reflection i j).choose
  invFun j := (P.exist_root_reflection i j).choose
  left_inv j := by
    exact root_reflection_comp_self P i j
  right_inv j := by
    exact root_reflection_comp_self P i j

/-- The reflection associated to a coroot. -/
def coreflection (P : RootPairingOld ι R M N) (i : ι) : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

lemma coreflection_eq_flip_reflection (P : RootPairingOld ι R M N) (i : ι) (f : N) :
    P.coreflection i f = P.flip.reflection i f :=
  rfl

/-!
lemma reflection_invOn_self (P : RootPairingOld ι R M N) (i : ι) :
    InvOn (P.reflection i) (P.reflection i) (range P.root) (range P.root) := by
  constructor <;>
    exact fun x _ => Module.involutive_reflection (P.coroot_root_two i) x

lemma bijOn_reflection_root (P : RootPairingOld ι R M N) (i : ι) :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
  InvOn.bijOn (reflection_invOn_self P i)
    (mapsTo_preReflection_root P i) (mapsTo_preReflection_root P i)

lemma exist_section_of_mapsTo {α β γ : Type*} (f₁ : ι ↪ β) (f₂ : γ → α) (g : α → β)
    (h : MapsTo g (range f₂) (range f₁))
    (a : γ) : ∃ j, f₁ j = g (f₂ a) := by
  simp_all only [mapsTo_range_iff, mem_range]

lemma mapsTo_of_bijOn {α β : Type*} (s : Set α) (t : Set β) (g : α → β) (h : BijOn g s t) :
    MapsTo g s t := by
  exact BijOn.mapsTo h

lemma injective_of_embed {α β : Type*} (f : α ↪ β) : Injective f := by
  exact Embedding.injective f


def equiv_of_bijOn_of_embed {α β γ : Type*} (f : ι ↪ α) (g : α → α)
    (h : BijOn g (range f) (range f)) : ι ≃ ι where
  toFun i := (exist_section_of_mapsTo f f g (BijOn.mapsTo h) i).choose
  invFun := (exist_section_of_mapsTo f f g (BijOn.mapsTo h) i).choose

--try Function.Embedding.toEquivRange (Mathlib.Logic.Equiv.Fintype) or
-- Equiv.ofInjective (Mathlib.Logic.Equiv.Set)
-- Set.rangeSplitting f x chooses an element of f⁻¹' x.
-- Set.apply_rangeSplitting says applying f yields x


def new_from_old (P : RootPairingOld ι R M N) : RootPairingNew ι R M N where
  toLin := P.toLin
  bijectiveLeft := P.bijectiveLeft
  bijectiveRight := P.bijectiveRight
  root := P.root
  coroot := P.coroot
  root_coroot_two := P.root_coroot_two
  reflection_perm i := P.reflection_in i
  reflection_perm_root i j := by
    simp only [reflection_in_apply]
    rw [preReflection_apply, ← (P.exist_root_reflection i j).choose_spec]
    exact rfl
  reflection_perm_coroot i j := by
    simp only [reflection_in_apply]
    rw [preReflection_apply]


    sorry
-/
