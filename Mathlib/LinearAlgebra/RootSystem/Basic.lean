/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.RootSystem.Reflection

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

A root datum is sometimes defined as collections of roots and coroots together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique.
For root systems, things are even more extreme: the coroots are uniquely determined by the roots.
Furthermore a root system induces a canonical non-degenerate bilinear form on the ambient space and
many informal accounts include this form as part of the data.

We have opted for a design in which some of the uniquely-determined data is actually included (e.g.,
the coroots are part of the data of a root system). Empirically this seems to be by far the most
convenient design and by providing extensionality lemmas expressing the uniqueness we expect to get
the best of both worlds.

A final point is that we require roots and coroots to be injections from a base indexing type `ι`
rather than subsets of their codomains. This design was chosen to avoid the bijection between roots
and coroots being a dependently-typed object. A third option would be to have the roots and coroots
be subsets but to avoid having a dependently-typed bijection by defining it globally with junk value
(say `0`) outside of the roots and coroots. This would work but lacks the convenient symmetry that
the chosen design enjoys: by introducing the indexing type `ι`, one does not have to pick a
direction (`roots → coroots` or `coroots → roots`) for the forward direction of the bijection.

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι : Type*) [Finite ι] {R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [IsReflexive R M] (e : N ≃ₗ[R] Dual R M)

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with finite indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots") and an `ι`-indexed subset of `N`
("the coroots") satisfying the axioms familiar from the traditional theory of root systems / data.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
structure RootPairing :=
  root : ι ↪ M
  coroot : ι ↪ N
  coroot_root_two : ∀ i, e (coroot i) (root i) = 2
  image_root_subset : ∀ i, preReflection (root i) (e (coroot i)) '' (range root) ⊆ range root
  image_coroot_subset :
    ∀ i, preReflection (coroot i) (e.flip (root i)) '' (range coroot) ⊆ range coroot

attribute [nolint docBlame] RootPairing.root
attribute [nolint docBlame] RootPairing.coroot

/-- A root datum is a root pairing for which the roots and coroots take values in finitely-generated
free Abelian groups. -/
abbrev RootDatum {X₁ X₂ : Type*}
    [AddCommGroup X₁] [Free ℤ X₁] [Finite ℤ X₁]
    [AddCommGroup X₂]
    (e : X₂ ≃+ Dual ℤ X₁) :=
  RootPairing ι e.toIntLinearEquiv

variable (R M) in
/-- A root system is a root pairing for which the roots span their ambient module and the perfect
pairing is the canonical one between `M` and `Dual R M`. -/
structure RootSystem extends RootPairing ι (LinearEquiv.refl R (Dual R M)) :=
  span_eq_top : span R (range root) = ⊤

namespace RootPairing

variable {e ι}
variable (P : RootPairing ι e) (i : ι)

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer.-/
def IsCrystallographic : Prop :=
  ∀ i, e (P.coroot i) '' (range P.root) ⊆ zmultiples (1 : R)

/-- A root pairing is said to be reduced if it never contains the double of a root.-/
def IsReduced : Prop :=
  ∀ i, 2 • P.root i ∉ range P.root

lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h] using P.coroot_root_two i

lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.coroot_root_two i

lemma root_coroot_two :
    (e.flip (P.root i)) (P.coroot i) = 2 := by
  simpa only [LinearEquiv.flip_apply] using P.coroot_root_two i

/-- The reflection associated to a root. -/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.coroot_root_two i)

lemma reflection_apply (x : M) :
    P.reflection i x = x - (e (P.coroot i) x) • P.root i :=
  rfl

@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

/-- The reflection associated to a coroot. -/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (e.flip (P.root i) f) • P.coroot i :=
  rfl

@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  ((finite_range P.root).equiv_image_eq_iff_subset (P.reflection i) _).mpr <|
    P.image_root_subset i

@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  ((finite_range P.coroot).equiv_image_eq_iff_subset (P.coreflection i) _).mpr <|
    P.image_coroot_subset i

lemma reflection_dualMap_eq_coreflection :
    e.trans (P.reflection i).dualMap = (P.coreflection i).trans e := by
  ext n m
  simp [coreflection_apply, reflection_apply, mul_comm (e n (P.root i)), e.map_sub]

/-- Even though the roots may not span, coroots are distinguished by their pairing with the
roots. The proof depends crucially on the fact that there are finitely-many roots.

Modulo trivial generalisations, this statement is exactly Lemma 1.1.4 on page 87 of SGA 3 XXI.
See also `RootPairing.injOn_dualMap_subtype_span_root_coroot` for a more useful restatement. -/
lemma eq_of_forall_coroot_root_eq [NoZeroSMulDivisors ℤ M] (i j : ι)
    (h : ∀ k, e (P.coroot i) (P.root k) = e (P.coroot j) (P.root k)) :
    i = j := by
  set α := P.root i
  set β := P.root j
  set sα : M ≃ₗ[R] M := P.reflection i
  set sβ : M ≃ₗ[R] M := P.reflection j
  set sαβ : M ≃ₗ[R] M := sβ.trans sα
  have hα : sα β = β - (2 : R) • α := by rw [P.reflection_apply, h j, P.coroot_root_two j]
  have hβ : sβ α = α - (2 : R) • β := by rw [P.reflection_apply, ← h i, P.coroot_root_two i]
  have hsαβ : (sαβ : M → M) '' (range P.root) = range P.root := by
    change (sα : M → M) ∘ (sβ : M → M) '' (range P.root) = range P.root
    rw [image_comp, P.reflection_image_eq, P.reflection_image_eq]
  set f : ℕ → M := fun n ↦ β + (2 * n : ℤ) • (α - β)
  have hf : ∀ n : ℕ, (sαβ^[n]) β = f n := by
    intro n
    induction' n with n ih; simp
    simp only [iterate_succ', ih, hα, hβ, two_smul, smul_add, mul_add, add_smul, comp_apply,
      map_zsmul, zsmul_sub, map_add, neg_sub, map_neg, smul_neg, map_sub, Nat.cast_succ, mul_one,
      LinearEquiv.trans_apply, reflection_apply_self]
    abel
  set f' : ℕ → range P.root := fun n ↦ ⟨f n, by
    rw [← iterate_image_eq_of_image_eq hsαβ n, ← hf]; exact mem_image_of_mem _ (mem_range_self j)⟩
  have : ¬ Injective f' := not_injective_infinite_finite f'
  contrapose! this
  intros n m hnm
  rw [Subtype.mk_eq_mk, add_right_inj, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero,
    sub_eq_zero] at hnm
  linarith [hnm.resolve_right (P.root.injective.ne this)]

lemma injOn_dualMap_subtype_span_root_coroot [NoZeroSMulDivisors ℤ M] :
    InjOn ((span R (range P.root)).subtype.dualMap ∘ₗ e) (range P.coroot) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  refine P.eq_of_forall_coroot_root_eq i j fun k ↦ ?_
  simpa using LinearMap.congr_fun hij ⟨P.root k, Submodule.subset_span (mem_range_self k)⟩

/-- In characteristic zero if there is no torsion, the correspondence between roots and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the coroot mappings. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {P₁ P₂ : RootPairing ι e}
    (hr : P₁.root = P₂.root)
    (hc : range P₁.coroot = range P₂.coroot) :
    P₁ = P₂ := by
  suffices P₁.coroot = P₂.coroot by cases P₁; cases P₂; congr
  have := NoZeroSMulDivisors.IntOfCharZero R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply]
  apply eq_of_preReflection_image_eq' (P₁.ne_zero i) (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.reflection_image_eq i
  · exact hr ▸ P₂.coroot_root_two i
  · exact hr ▸ P₂.reflection_image_eq i

/-- This lemma exists to support the definition `RootSystem.mk'` and usually should not be used
directly. The lemma `RootPairing.coroot_eq_coreflection_of_root_eq_of_span_eq_top` or even
`RootSystem.coroot_eq_coreflection_of_root_eq` will usually be more convenient. -/
lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top' [CharZero R] [NoZeroSMulDivisors R M]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, e (coroot i) (root i) = 2)
    (hs : ∀ i, preReflection (root i) (e (coroot i)) '' (range root) ⊆ range root)
    (hsp : span R (range root) = ⊤)
    {i j k : ι} (hk : root k = preReflection (root i) (e (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (e.flip (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (e α')
  set sβ := preReflection β (e β')
  let sα' := preReflection α' (e.flip α)
  have hij : preReflection (sα β) (e (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext; simp [← preReflection_preReflection β (e β') (hp i), preReflection_apply, e.map_sub]
  have hk₀ : root k ≠ 0 := fun h ↦ by simpa [h] using hp k
  apply e.injective
  apply eq_of_preReflection_image_eq_fixed hk₀ (finite_range root) hsp (hp k) (hs k)
  · simp [hk, preReflection_apply, hp i, hp j, mul_two, mul_comm (e α' β), e.map_sub]
  · rw [hk, hij, LinearMap.coe_comp, LinearMap.coe_comp, image_comp, image_comp]
    exact subset_trans (image_mono (image_mono (hs i))) (subset_trans (image_mono (hs j)) (hs i))

/-- In characteristic zero if there is no torsion and the roots span, if the `i`th reflection of the
`j`th root is the `k`th root, then the corresponding relationship holds for coroots. See also
`RootSystem.coroot_eq_coreflection_of_root_eq`. -/
lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top [CharZero R] [NoZeroSMulDivisors R M]
    (hsp : span R (range P.root) = ⊤)
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) :=
  coroot_eq_coreflection_of_root_eq_of_span_eq_top' P.root P.coroot P.coroot_root_two
    P.image_root_subset hsp hk

end RootPairing

namespace RootSystem

open RootPairing

variable {ι}
variable (P : RootSystem ι R M)

/-- In characteristic zero if there is no torsion, a root system is determined entirely by its
roots. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {P₁ P₂ : RootSystem ι R M}
    (hr : P₁.root = P₂.root) :
    P₁ = P₂ := by
  suffices ∀ P₁ P₂ : RootSystem ι R M, P₁.root = P₂.root → range P₁.coroot ⊆ range P₂.coroot by
    have h₁ := this P₁ P₂ hr
    have h₂ := this P₂ P₁ hr.symm
    cases' P₁ with P₁
    cases' P₂ with P₂
    congr
    exact RootPairing.ext hr (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ hr - ⟨i, rfl⟩
  use i
  apply (LinearEquiv.refl R (Dual R M)).injective
  apply eq_of_preReflection_image_eq (P₁.ne_zero i) (finite_range P₁.root) P₁.span_eq_top
  · exact hr ▸ P₂.coroot_root_two i
  · exact hr ▸ P₂.reflection_image_eq i
  · exact P₁.coroot_root_two i
  · exact P₁.reflection_image_eq i

/-- In characteristic zero if there is no torsion, to check that a collection of roots form a root
system, we do not need to check that the coroots are stable under reflections since this follows
from the corresponding property for the roots. -/
def mk' [CharZero R] [NoZeroSMulDivisors R M]
    (root : ι ↪ M)
    (coroot : ι ↪ Dual R M)
    (hp : ∀ i, (coroot i) (root i) = 2)
    (hs : ∀ i, preReflection (root i) (coroot i) '' (range root) ⊆ range root)
    (hsp : span R (range root) = ⊤) :
    RootSystem ι R M where
  root := root
  coroot := coroot
  coroot_root_two := hp
  image_root_subset := hs
  span_eq_top := hsp
  image_coroot_subset := by
    rintro i - ⟨-, ⟨j, rfl⟩, rfl⟩
    obtain ⟨k, h⟩ := (hs i) <| mem_image_of_mem _ (mem_range_self j)
    refine ⟨k, coroot_eq_coreflection_of_root_eq_of_span_eq_top' root coroot hp ?_ hsp h⟩
    exact hs

/-- In characteristic zero if there is no torsion, if the `i`th reflection of the `j`th root is the
`k`th root, then the corresponding relationship holds for coroots. -/
lemma coroot_eq_coreflection_of_root_eq [CharZero R] [NoZeroSMulDivisors R M]
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) :=
  P.coroot_eq_coreflection_of_root_eq_of_span_eq_top P.span_eq_top hk

end RootSystem
