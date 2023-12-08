/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.RootSystem.Symmetries

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.

## Main definitions / results:
 * `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with finite
   indexing set `ι` is the data of an `ι`-indexed subset of `M` ("the roots") and an `ι`-indexed
   subset of `N` ("the coroots") satisfying the axioms familiar from the traditional theory of root
   systems / data.
 * `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
   finitely-generated free Abelian groups.
 * `RootSystem`: A root system is a root pairing for which the roots span their ambient module and
   the perfect pairing is the canonical one between `M` and `Dual R M`.
 * `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
   between a root and coroot is always an integer.
 * `RootPairing.IsReduced`: A root pairing is said to be reduced if it never contains the double of
   a root.
 * `RootPairing.ext`: In characteristic zero if there is no torsion, the correspondence between
   roots and coroots is unique.
 * `RootSystem.ext`: In characteristic zero if there is no torsion, a root system is determined
   entirely by its roots.
 * `RootSystem.mk'`: In characteristic zero if there is no torsion, to check that a collection of
   roots form a root system, we do not need to check that the coroots are stable under reflections
   since this follows from the corresponding property for the roots.

## Implementation details

TODO write, as this was fairly tricky to get into good state, potential points to mention:
 * Concept of `RootPairing`
 * Reason for `ι`-indexing to solve DTT hell
 * Various extensionality issues
 * Data-bearing or `Prop`-valued
 * `⊆ roots` or `= roots`
 * Roots / coroots as subsets or injections
 * Junk-value pattern for bijection to avoid DTT hell
 * etc.

-/

open Set Function Module
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι : Type*) [Finite ι] {R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [IsReflexive R M] (p : N ≃ₗ[R] Dual R M)

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with finite indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots") and an `ι`-indexed subset of `N`
("the coroots") satisfying the axioms familiar from the traditional theory of root systems / data.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
structure RootPairing :=
  root : ι ↪ M
  coroot : ι ↪ N
  coroot_root_two : ∀ i, p (coroot i) (root i) = 2
  symmetry_image_root_eq : ∀ i, toPreSymmetry (root i) (p (coroot i)) '' (range root) ⊆ range root
  symmetry_image_coroot_eq : ∀ i,
    toPreSymmetry (coroot i) (p.flip (root i)) '' (range coroot) ⊆ range coroot

attribute [nolint docBlame] RootPairing.root
attribute [nolint docBlame] RootPairing.coroot

/-- A root datum is a root pairing for which the roots and coroots take values in finitely-generated
free Abelian groups. -/
abbrev RootDatum {X₁ X₂ : Type*}
    [AddCommGroup X₁] [Free ℤ X₁] [Finite ℤ X₁]
    [AddCommGroup X₂]
    (p : X₂ ≃+ Dual ℤ X₁) :=
  RootPairing ι p.toIntLinearEquiv

variable (R M) in
/-- A root system is a root pairing for which the roots span their ambient module and the perfect
pairing is the canonical one between `M` and `Dual R M`. -/
structure RootSystem extends RootPairing ι (LinearEquiv.refl R (Dual R M)) :=
  span_eq_top : span R (range root) = ⊤

namespace RootPairing

variable {p ι}
variable (rp : RootPairing ι p) (i : ι)

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer.-/
def IsCrystallographic : Prop :=
  ∀ i, p (rp.coroot i) '' (range rp.root) ⊆ (zmultiples (1 : R) : Set R)

-- TODO: automatically crystallographic when `R` is `ℤ`

/-- A root pairing is said to be reduced if it never contains the double of a root.-/
def IsReduced : Prop :=
  ∀ i, 2 • rp.root i ∉ range rp.root

lemma ne_zero [CharZero R] : (rp.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h] using rp.coroot_root_two i

lemma ne_zero' [CharZero R] : (rp.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using rp.coroot_root_two i

lemma root_coroot_two :
    (p.flip (rp.root i)) (rp.coroot i) = 2 := by
  simpa only [LinearEquiv.flip_apply] using rp.coroot_root_two i

/-- The symmetry associated to a root. -/
def symmetryOfRoot : M ≃ₗ[R] M :=
  toSymmetry (rp.coroot_root_two i)

lemma symmetryOfRoot_apply (x : M) :
    rp.symmetryOfRoot i x = x - (p (rp.coroot i) x) • rp.root i :=
  rfl

/-- The symmetry associated to a coroot. -/
def symmetryOfCoroot : N ≃ₗ[R] N :=
  toSymmetry (rp.root_coroot_two i)

lemma symmetryOfCoroot_apply (f : N) :
    rp.symmetryOfCoroot i f = f - (p.flip (rp.root i) f) • rp.coroot i :=
  rfl

@[simp]
lemma symmetry_image_eq :
    rp.symmetryOfRoot i '' (range rp.root) = range rp.root := by
  change (rp.symmetryOfRoot i).toEquiv '' (range rp.root) = range rp.root
  rw [(finite_range rp.root).equiv_image_eq_iff_subset]
  exact rp.symmetry_image_root_eq i

@[simp]
lemma symmetry_image_eq' :
    rp.symmetryOfCoroot i '' (range rp.coroot) = range rp.coroot := by
  change (rp.symmetryOfCoroot i).toEquiv '' (range rp.coroot) = range rp.coroot
  rw [(finite_range rp.coroot).equiv_image_eq_iff_subset]
  exact rp.symmetry_image_coroot_eq i

lemma symmetryOfRoot_dualMap_eq_symmetryOfCoroot :
    p.trans (rp.symmetryOfRoot i).dualMap = (rp.symmetryOfCoroot i).trans p := by
  ext n m
  simp [symmetryOfCoroot_apply, symmetryOfRoot_apply, mul_comm (p n (rp.root i)), p.map_sub]

-- This proof is horrendous (partly as a result of surviving several refactors of the base
-- definitions). Once I fix it I am confident I can drop the `maxHeartbeats` bump. TODO do this!
set_option maxHeartbeats 800000 in
/-- Even though the coroots may not span, roots are distinguished by their pairing with the
coroots. The proof depends crucially on the fact that there are finitely-many roots.

Modulo trivial generalisations, this statement is exactly Lemma 1.1.4 on page 87 of SGA 3 XXI.
See also `RootPairing.injOn_dualMap_subtype_span_roots_coroots` for a more useful restatement. -/
lemma eq_of_forall_coroot_of_root_eq [NoZeroSMulDivisors ℤ M] (i j : ι)
    (h : ∀ k, p (rp.coroot i) (rp.root k) = p (rp.coroot j) (rp.root k)) :
    i = j := by
  let α := rp.root i
  let β := rp.root j
  let sα : M ≃ₗ[R] M := rp.symmetryOfRoot i
  let sβ : M ≃ₗ[R] M := rp.symmetryOfRoot j
  have hα : sα β = β - (2 : R) • α := by rw [rp.symmetryOfRoot_apply, h j, rp.coroot_root_two j]
  have hβ : sβ α = α - (2 : R) • β := by rw [rp.symmetryOfRoot_apply, ← h i, rp.coroot_root_two i]
  let sαβ : M ≃ₗ[R] M := sα * sβ
  have key : ∀ n : ℕ, (sαβ^[n]) β = β + (2 * n : ℤ) • (α - β) := by
    intro n
    induction' n with n ih; simp
    simp only [iterate_succ', ih, comp_apply, Nat.cast_succ, zsmul_sub, zsmul_sub, map_add, map_sub,
      map_zsmul]
    change sα (sβ β) + (_ • sα (sβ _) - _ • sα (sβ _)) = _
    erw [toSymmetry_apply_self]
    rw [hβ, map_sub, map_smul, map_neg, hα]
    erw [toSymmetry_apply_self]
    simp only [two_smul, neg_sub, zsmul_sub, smul_neg, smul_add, mul_add, mul_one, add_smul]
    abel
  replace key : ∀ n : ℕ, (β : M) + (2 * n : ℤ) • (α - β) ∈ range rp.root := by
    intros n
    have hsαβ : (sαβ : M → M) '' (range rp.root) = (range rp.root) := by
      change (sα : M → M) ∘ (sβ : M → M) '' (range rp.root) = (range rp.root)
      simp only [image_comp, rp.symmetry_image_eq]
    replace hsαβ : (sαβ^[n]) '' (range rp.root) = (range rp.root) := by
      rw [← IsFixedPt, image_iterate]
      exact IsFixedPt.iterate hsαβ n
    conv_rhs => rw [← hsαβ]
    rw [← key]
    exact mem_image_of_mem _ (mem_range_self j)
  let f : ℕ → range rp.root := fun n ↦ ⟨β + (2 * n : ℤ) • (α - β), key n⟩
  have : ¬ Injective f := by
    have : Finite (range rp.root) := Finite.Set.finite_range rp.root
    exact not_injective_infinite_finite f
  contrapose! this
  replace this : α ≠ β := by contrapose! this; exact rp.root.injective this
  intros n m hnm
  rw [Subtype.mk_eq_mk, add_right_inj, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero,
    sub_eq_zero] at hnm
  linarith [hnm.resolve_right this]

lemma injOn_dualMap_subtype_span_roots_coroots [NoZeroSMulDivisors ℤ M] :
    InjOn ((span R (range rp.root)).subtype.dualMap ∘ₗ p) (range rp.coroot) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  refine rp.eq_of_forall_coroot_of_root_eq i j fun k ↦ ?_
  simpa using LinearMap.congr_fun hij ⟨rp.root k, Submodule.subset_span (mem_range_self k)⟩

/-- In characteristic zero if there is no torsion, the correspondence between roots and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the coroot mappings. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {rp₁ rp₂ : RootPairing ι p}
    (hr : rp₁.root = rp₂.root)
    (hc : range rp₁.coroot = range rp₂.coroot) :
    rp₁ = rp₂ := by
  suffices rp₁.coroot = rp₂.coroot by cases rp₁; cases rp₂; congr
  have := NoZeroSMulDivisors.IntOfCharZero R M
  ext i
  apply rp₁.injOn_dualMap_subtype_span_roots_coroots (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply]
  apply eq_of_toPreSymmetry_image_eq' (rp₁.ne_zero i) (finite_range rp₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact rp₁.coroot_root_two i
  · exact rp₁.symmetry_image_eq i
  · exact hr ▸ rp₂.coroot_root_two i
  · exact hr ▸ rp₂.symmetry_image_eq i

end RootPairing

namespace RootSystem

/-- In characteristic zero if there is no torsion, a root system is determined entirely by its
roots. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {rp₁ rp₂ : RootSystem ι R M}
    (hr : rp₁.root = rp₂.root) :
    rp₁ = rp₂ := by
  suffices ∀ (rp₁ rp₂ : RootSystem ι R M) (_hr : rp₁.root = rp₂.root),
      range rp₁.coroot ⊆ range rp₂.coroot by
    have h₁ := this rp₁ rp₂ hr
    have h₂ := this rp₂ rp₁ hr.symm
    cases' rp₁ with rp₁
    cases' rp₂ with rp₂
    congr
    exact RootPairing.ext hr (le_antisymm h₁ h₂)
  clear! rp₁ rp₂
  rintro rp₁ rp₂ hr - ⟨i, rfl⟩
  use i
  apply (LinearEquiv.refl R (Dual R M)).injective
  apply eq_of_toPreSymmetry_image_eq (rp₁.ne_zero i) (finite_range rp₁.root) rp₁.span_eq_top
  · rw [hr]
    exact rp₂.coroot_root_two i
  · rw [hr]
    exact rp₂.symmetry_image_eq i
  · exact rp₁.coroot_root_two i
  · exact rp₁.symmetry_image_eq i

variable {ι p}

-- TODO (1) sensible name (should I state this without using `p`?)
-- TODO (2) make another version of this lemma, stated for coroots in a true `RootSystem`
lemma mk_aux [CharZero R] [NoZeroSMulDivisors R M]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (coroot i) (root i) = 2)
    (hs : ∀ i, toPreSymmetry (root i) (p (coroot i)) '' (range root) = range root)
    (hsp : span R (range root) = ⊤) {i j k : ι}
    (hk : root k = toPreSymmetry (root i) (p (coroot i)) (root j)) :
    coroot k = toPreSymmetry (coroot i) (p.flip (root i)) (coroot j) := by
  apply p.injective
  have hk₀ : root k ≠ 0 := fun h ↦ by simpa [h] using hp k
  set si := toPreSymmetry (root i) (p (coroot i))
  set sj := toPreSymmetry (root j) (p (coroot j))
  have hij : toPreSymmetry (toPreSymmetry (root i) (p (coroot i)) (root j))
        (p <| toPreSymmetry (coroot i) (p.flip (root i)) (coroot j)) = si * sj * si := by
    ext
    simp [← toPreSymmetry_toPreSymmetry (root i) (root j) (p (coroot i)) (p (coroot j)) (hp i),
      toPreSymmetry_apply, p.map_sub]
  apply eq_of_toPreSymmetry_image_eq_fixed hk₀ (finite_range root) hsp (hp k) ((hs k).symm ▸ refl _)
  · simp [hk, toPreSymmetry_apply, hp i, hp j, mul_two, mul_comm (p (coroot i) (root j)), p.map_sub]
  · rw [hk, hij]
    change (si ∘ sj ∘ si) '' _ ⊆ _
    rw [← comp.assoc, image_comp, hs i, image_comp, hs j, hs i]

/-- In characteristic zero if there is no torsion, to check that a collection of roots form a root
system, we do not need to check that the coroots are stable under reflections since this follows
from the corresponding property for the roots. -/
def mk' [CharZero R] [NoZeroSMulDivisors R M]
    (root : ι ↪ M)
    (coroot : ι ↪ Dual R M)
    (hp : ∀ i, (coroot i) (root i) = 2)
    (hs : ∀ i, toPreSymmetry (root i) (coroot i) '' (range root) = range root) -- TODO ⊆
    (hsp : span R (range root) = ⊤) :
    RootSystem ι R M where
  root := root
  coroot := coroot
  coroot_root_two := hp
  symmetry_image_root_eq := fun i ↦ by rw [LinearEquiv.refl_apply, hs i]
  span_eq_top := hsp
  symmetry_image_coroot_eq := by
    intro i f hf
    simp only [mem_image, mem_range, exists_exists_eq_and] at hf
    obtain ⟨j, rfl⟩ := hf
    obtain ⟨k : ι, hk : root k = toPreSymmetry (root i) (coroot i) (root j)⟩ :=
      (hs i) ▸ mem_image_of_mem _ (mem_range_self j)
    exact ⟨k, mk_aux root coroot hp (by simp [hs]) hsp hk⟩

end RootSystem
