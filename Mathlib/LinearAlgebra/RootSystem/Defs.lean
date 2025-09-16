/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Reflection

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.

## Main definitions:

* `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N` (over some commutative ring
  `R`) a root pairing with indexing set `ι` is the data of an `ι`-indexed subset of `M`
  ("the roots") an `ι`-indexed subset of `N` ("the coroots"), and an `ι`-indexed set of
  permutations of `ι` such that each root-coroot pair evaluates to `2`, and the permutation
  attached to each element of `ι` is compatible with the reflections on the corresponding roots and
  coroots.
* `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
  finitely-generated free Abelian groups.
* `RootSystem`: A root system is a root pairing for which the roots span their ambient module.

## Implementation details

A root datum is sometimes defined as two subsets: roots and coroots, together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique and
so the question arises of whether this bijection should be part of the data of a root datum or
whether one should merely assert its existence. For root systems, things are even more extreme: the
coroots are uniquely determined by the roots. Furthermore a root system induces a canonical
non-degenerate bilinear form on the ambient space and many informal accounts even include this form
as part of the data.

We have opted for a design in which some of the uniquely-determined data is included: the bijection
between roots and coroots is (implicitly) included and the coroots are included for root systems.
Empirically this seems to be by far the most convenient design and by providing extensionality
lemmas expressing the uniqueness we expect to get the best of both worlds.

Furthermore, we require roots and coroots to be injections from a base indexing type `ι` rather than
subsets of their codomains. This design was chosen to avoid the bijection between roots and coroots
being a dependently-typed object. A third option would be to have the roots and coroots be subsets
but to avoid having a dependently-typed bijection by defining it globally with junk value `0`
outside of the roots and coroots. This would work but lacks the convenient symmetry that the chosen
design enjoys: by introducing the indexing type `ι`, one does not have to pick a direction
(`roots → coroots` or `coroots → roots`) for the forward direction of the bijection. Besides,
providing the user with the additional definitional power to specify an indexing type `ι` is a
benefit and the junk-value pattern is a cost.

As a final point of divergence from the classical literature, we make the reflection permutation on
roots and coroots explicit, rather than specifying only that reflection preserves the sets of roots
and coroots. This is necessary when working with infinite root systems, where the coroots are not
uniquely determined by the roots, because without it, the reflection permutations on roots and
coroots may not correspond. For this purpose, we define a map from `ι` to permutations on `ι`, and
require that it is compatible with reflections and coreflections.

-/

open Set Function
open Module hiding reflection
open Submodule (span span_image)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots"), an `ι`-indexed subset of `N`
("the coroots"), and an `ι`-indexed set of permutations of `ι`, such that each root-coroot pair
evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
reflections on the corresponding roots and coroots.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
structure RootPairing extends M →ₗ[R] N →ₗ[R] R where
  [isPerfPair_toLinearMap : toLinearMap.IsPerfPair]
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLinearMap (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflections. This corresponds to the
  classical requirement that the symmetry attached to each root (later defined in
  `RootPairing.reflection`) leave the whole set of roots stable: as explained above, we
  formalize this stability by fixing the image of the roots through each reflection (whence the
  permutation); and similarly for coroots. -/
  reflectionPerm : ι → (ι ≃ ι)
  reflectionPerm_root : ∀ i j,
    root j - toLinearMap (root j) (coroot i) • root i = root (reflectionPerm i j)
  reflectionPerm_coroot : ∀ i j,
    coroot j - toLinearMap (root i) (coroot j) • coroot i = coroot (reflectionPerm i j)

attribute [instance] RootPairing.isPerfPair_toLinearMap

/-- A root datum is a root pairing with coefficients in the integers and for which the root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Finite ℤ X₁] [Finite ℤ X₂]` should be supplied as mixins, and
that freeness follows automatically since two finitely-generated Abelian groups in perfect pairing
are necessarily free. Moreover Lean knows this, e.g., via `PerfectPairing.reflexive_left`,
`Module.instNoZeroSMulDivisorsOfIsDomain`, `Module.free_of_finite_type_torsion_free'`. -/
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂

/-- A root system is a root pairing for which the roots and coroots span their ambient modules.

Note that this is slightly more general than the usual definition in the sense that `N` is not
required to be the dual of `M`. -/
structure RootSystem extends RootPairing ι R M N where
  span_root_eq_top : span R (range root) = ⊤
  span_coroot_eq_top : span R (range coroot) = ⊤

attribute [simp] RootSystem.span_root_eq_top
attribute [simp] RootSystem.span_coroot_eq_top

namespace RootPairing

variable {ι R M N}
variable (P : RootPairing ι R M N) (i j : ι)

@[deprecated "Now a syntactic equality" (since := "2025-07-05"), nolint synTaut]
lemma toLinearMap_eq_toPerfectPairing (x : M) (y : N) :
    P.toLinearMap x y = P.toLinearMap x y := rfl

@[deprecated (since := "2025-04-20"), nolint synTaut]
alias toLin_toPerfectPairing := toLinearMap_eq_toPerfectPairing

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
@[simps!, simps toLinearMap]
protected def flip : RootPairing ι R N M where
  toLinearMap := P.toLinearMap.flip
  root := P.coroot
  coroot := P.root
  root_coroot_two := P.root_coroot_two
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root := P.reflectionPerm_coroot
  reflectionPerm_coroot := P.reflectionPerm_root

@[simp]
lemma flip_flip : P.flip.flip = P :=
  rfl

variable (ι R M N) in
/-- `RootPairing.flip` as an equivalence. -/
@[simps] def flipEquiv : RootPairing ι R N M ≃ RootPairing ι R M N where
  toFun P := P.flip
  invFun P := P.flip

/-- If we interchange the roles of `M` and `N`, we still have a root system. -/
protected def _root_.RootSystem.flip (P : RootSystem ι R M N) : RootSystem ι R N M :=
  { toRootPairing := P.toRootPairing.flip
    span_root_eq_top := P.span_coroot_eq_top
    span_coroot_eq_top := P.span_root_eq_top }

@[simp]
protected lemma _root_.RootSystem.flip_flip (P : RootSystem ι R M N) :
    P.flip.flip = P :=
  rfl

variable (ι R M N) in
/-- `RootSystem.flip` as an equivalence. -/
@[simps] def _root_.RootSystem.flipEquiv : RootSystem ι R N M ≃ RootSystem ι R M N where
  toFun P := P.flip
  invFun P := P.flip

lemma ne_zero [NeZero (2 : R)] : (P.root i : M) ≠ 0 :=
  fun h ↦ NeZero.ne' (2 : R) <| by simpa [h] using P.root_coroot_two i

lemma ne_zero' [NeZero (2 : R)] : (P.coroot i : N) ≠ 0 :=
  P.flip.ne_zero i

lemma zero_notMem_range_root [NeZero (2 : R)] : 0 ∉ range P.root := by
  simpa only [mem_range, not_exists] using fun i ↦ P.ne_zero i

@[deprecated (since := "2025-05-24")] alias zero_nmem_range_root := zero_notMem_range_root

lemma zero_notMem_range_coroot [NeZero (2 : R)] : 0 ∉ range P.coroot :=
  P.flip.zero_notMem_range_root

@[deprecated (since := "2025-05-24")] alias zero_nmem_range_coroot := zero_notMem_range_coroot

lemma exists_ne_zero [Nonempty ι] [NeZero (2 : R)] : ∃ i, P.root i ≠ 0 := by
  obtain ⟨i⟩ := inferInstanceAs (Nonempty ι)
  exact ⟨i, P.ne_zero i⟩

lemma exists_ne_zero' [Nonempty ι] [NeZero (2 : R)] : ∃ i, P.coroot i ≠ 0 :=
  P.flip.exists_ne_zero

include P in
protected lemma nontrivial [Nonempty ι] [NeZero (2 : R)] : Nontrivial M := by
  obtain ⟨i, hi⟩ := P.exists_ne_zero
  exact ⟨P.root i, 0, hi⟩

include P in
protected lemma nontrivial' [Nonempty ι] [NeZero (2 : R)] : Nontrivial N :=
  P.flip.nontrivial

/-- Roots written as functionals on the coweight space. -/
abbrev root' (i : ι) : Dual R N := P.toLinearMap (P.root i)

/-- Coroots written as functionals on the weight space. -/
abbrev coroot' (i : ι) : Dual R M := P.toLinearMap.flip (P.coroot i)

/-- This is the pairing between roots and coroots. -/
def pairing : R := P.root' i (P.coroot j)

@[simp]
lemma root_coroot_eq_pairing : P.toLinearMap (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
lemma root'_coroot_eq_pairing : P.root' i (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
lemma root_coroot'_eq_pairing : P.coroot' i (P.root j) = P.pairing j i :=
  rfl

lemma coroot_root_eq_pairing : P.toLinearMap.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

variable {P} in
lemma pairing_eq_add_of_root_eq_add {i j k l : ι} (h : P.root k = P.root i + P.root j) :
    P.pairing k l = P.pairing i l + P.pairing j l := by
  simp only [← root_coroot_eq_pairing, h, map_add, LinearMap.add_apply]

variable {P} in
lemma pairing_eq_add_of_root_eq_smul_add_smul
    {i j k l : ι} {x y : R} (h : P.root k = x • P.root i + y • P.root l) :
    P.pairing k j = x • P.pairing i j + y • P.pairing l j := by
  simp only [← root_coroot_eq_pairing, h, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]

lemma coroot_root_two :
    P.toLinearMap.flip (P.coroot i) (P.root i) = 2 := by
  simp

/-- The reflection associated to a root. -/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
lemma root_reflectionPerm (j : ι) :
    P.root (P.reflectionPerm i j) = (P.reflection i) (P.root j) :=
  (P.reflectionPerm_root i j).symm

@[deprecated (since := "2025-05-28")] alias root_reflection_perm := root_reflectionPerm

theorem mapsTo_reflection_root :
    MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.coroot' i x) • P.root i :=
  rfl

lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
lemma reflection_same (x : M) :
    P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

@[simp]
lemma reflection_inv :
    (P.reflection i)⁻¹ = P.reflection i :=
  rfl

@[simp]
lemma reflection_sq : P.reflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

@[simp]
lemma reflectionPerm_sq : P.reflectionPerm i ^ 2 = 1 := by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflectionPerm, reflection_same, Equiv.Perm.one_apply]

@[deprecated (since := "2025-05-28")] alias reflection_perm_sq := reflectionPerm_sq

@[simp]
lemma reflectionPerm_inv : (P.reflectionPerm i)⁻¹ = P.reflectionPerm i :=
  (mul_eq_one_iff_eq_inv.mp <| P.reflectionPerm_sq i).symm

@[deprecated (since := "2025-05-28")] alias reflection_perm_inv := reflectionPerm_inv

@[simp]
lemma reflectionPerm_self : P.reflectionPerm i (P.reflectionPerm i j) = j := by
  apply P.root.injective
  simp only [root_reflectionPerm, reflection_same]

@[deprecated (since := "2025-05-28")] alias reflection_perm_self := reflectionPerm_self

lemma reflectionPerm_involutive : Involutive (P.reflectionPerm i) :=
  involutive_iff_iter_2_eq_id.mpr (by ext; simp)

@[deprecated (since := "2025-05-28")] alias reflection_perm_involutive := reflectionPerm_involutive

@[simp]
lemma reflectionPerm_symm : (P.reflectionPerm i).symm = P.reflectionPerm i :=
  Involutive.symm_eq_self_of_involutive (P.reflectionPerm i) <| P.reflectionPerm_involutive i

@[deprecated (since := "2025-05-28")] alias reflection_perm_symm := reflectionPerm_symm

lemma bijOn_reflection_root :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
  Module.bijOn_reflection_of_mapsTo _ <| P.mapsTo_reflection_root i

@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

/-- The reflection associated to a coroot. -/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

@[simp]
lemma coroot_reflectionPerm (j : ι) :
    P.coroot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflectionPerm_coroot i j).symm

@[deprecated (since := "2025-05-28")] alias coroot_reflection_perm := coroot_reflectionPerm

theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.root' i) f • P.coroot i :=
  rfl

lemma coreflection_apply_coroot :
    P.coreflection i (P.coroot j) = P.coroot j - (P.pairing i j) • P.coroot i :=
  rfl

@[simp]
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]
lemma coreflection_same (x : N) :
    P.coreflection i (P.coreflection i x) = x :=
  Module.involutive_reflection (P.flip.coroot_root_two i) x

@[simp]
lemma coreflection_inv :
    (P.coreflection i)⁻¹ = P.coreflection i :=
  rfl

@[simp]
lemma coreflection_sq :
    P.coreflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq

lemma coreflection_eq_flip_reflection :
    P.coreflection i = P.flip.reflection i :=
  rfl

lemma reflection_reflectionPerm {i j : ι} :
    P.reflection (P.reflectionPerm j i) = P.reflection j * P.reflection i * P.reflection j := by
  ext x; simp [reflection_apply, coreflection_apply]; module

lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLinearMap.flip = P.toLinearMap.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toLinearMap m (P.coroot i))]

lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflectionPerm, EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflectionPerm, hk]

lemma coroot'_reflectionPerm {i j : ι} :
    P.coroot' (P.reflectionPerm i j) = P.coroot' j ∘ₗ P.reflection i := by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]

@[deprecated (since := "2025-05-28")] alias coroot'_reflection_perm := coroot'_reflectionPerm

lemma coroot'_reflection {i j : ι} (y : M) :
    P.coroot' j (P.reflection i y) = P.coroot' (P.reflectionPerm i j) y :=
  (LinearMap.congr_fun P.coroot'_reflectionPerm y).symm

lemma pairing_reflectionPerm (i j k : ι) :
    P.pairing j (P.reflectionPerm i k) = P.pairing (P.reflectionPerm i j) k := by
  simp only [pairing, root', coroot_reflectionPerm, root_reflectionPerm]
  simp [coreflection_apply_coroot, reflection_apply_root, mul_comm]

@[deprecated (since := "2025-05-28")] alias pairing_reflection_perm := pairing_reflectionPerm

@[simp]
lemma toPerfPair_conj_reflection :
    P.toPerfPair.conj (P.reflection i) = (P.coreflection i).toLinearMap.dualMap := by
  ext f n
  simp [LinearEquiv.conj_apply, reflection_apply, coreflection_apply, mul_comm (f <| P.coroot i)]

@[simp]
lemma toPerfPair_flip_conj_coreflection :
    P.toLinearMap.flip.toPerfPair.conj (P.coreflection i) = (P.reflection i).toLinearMap.dualMap :=
  P.flip.toPerfPair_conj_reflection i

@[simp]
lemma pairing_reflectionPerm_self_left (P : RootPairing ι R M N) (i j : ι) :
    P.pairing (P.reflectionPerm i i) j = - P.pairing i j := by
  rw [pairing, root', ← reflectionPerm_root, root'_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, LinearMap.map_neg₂, root'_coroot_eq_pairing]

@[deprecated (since := "2025-05-28")]
alias pairing_reflection_perm_self_left := pairing_reflectionPerm_self_left

@[simp]
lemma pairing_reflectionPerm_self_right (i j : ι) :
    P.pairing i (P.reflectionPerm j j) = - P.pairing i j := by
  rw [pairing, ← reflectionPerm_coroot, root_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, map_neg, root_coroot_eq_pairing]

@[deprecated (since := "2025-05-28")]
alias pairing_reflection_perm_self_right := pairing_reflectionPerm_self_right

/-- The indexing set of a root pairing carries an involutive negation, corresponding to the negation
of a root / coroot. -/
@[simps] def indexNeg : InvolutiveNeg ι where
  neg i := P.reflectionPerm i i
  neg_neg i := by
    apply P.root.injective
    simp only [root_reflectionPerm, reflection_apply, LinearMap.flip_apply, root_coroot_eq_pairing,
      pairing_same, map_sub, coroot_reflectionPerm, coreflection_apply_self, map_neg, neg_smul,
      sub_neg_eq_add, map_smul, smul_add]
    module

lemma ne_neg [NeZero (2 : R)] [IsDomain R] :
    letI := P.indexNeg
    i ≠ -i := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  intro contra
  replace contra : P.root i = -P.root i := by simpa using congr_arg P.root contra
  simp [eq_neg_iff_add_eq_zero, ← two_smul R, NeZero.out, P.ne_zero i] at contra

variable {i j} in
@[simp]
lemma root_eq_neg_iff :
    P.root i = - P.root j ↔ i = P.reflectionPerm j j := by
  refine ⟨fun h ↦ P.root.injective ?_, fun h ↦ by simp [h]⟩
  rw [root_reflectionPerm, reflection_apply_self, h]

variable {i j} in
@[simp]
lemma coroot_eq_neg_iff :
    P.coroot i = - P.coroot j ↔ i = P.reflectionPerm j j :=
  P.flip.root_eq_neg_iff

lemma neg_mem_range_root_iff {x : M} :
    -x ∈ range P.root ↔ x ∈ range P.root := by
  suffices ∀ x : M, -x ∈ range P.root → x ∈ range P.root by
    refine ⟨this x, fun h ↦ ?_⟩
    rw [← neg_neg x] at h
    exact this (-x) h
  intro y ⟨i, hi⟩
  exact ⟨P.reflectionPerm i i, by simp [neg_eq_iff_eq_neg.mpr hi]⟩

lemma neg_mem_range_coroot_iff {x : N} :
    -x ∈ range P.coroot ↔ x ∈ range P.coroot :=
  P.flip.neg_mem_range_root_iff

lemma neg_root_mem :
    - P.root i ∈ range P.root :=
  ⟨P.reflectionPerm i i, by simp⟩

lemma neg_coroot_mem :
    - P.coroot i ∈ range P.coroot :=
  P.flip.neg_root_mem i

variable {P} in
lemma smul_coroot_eq_of_root_eq_smul [Finite ι] [NoZeroSMulDivisors ℤ N] (i j : ι) (t : R)
    (h : P.root j = t • P.root i) :
    t • P.coroot j = P.coroot i := by
  have hij : t * P.pairing i j = 2 := by simpa using ((P.coroot' j).congr_arg h).symm
  refine Module.eq_of_mapsTo_reflection_of_mem (f := P.root' i) (g := P.root' i)
    (finite_range P.coroot) (by simp [hij]) (by simp) (by simp [hij]) (by simp) ?_
    (P.mapsTo_coreflection_coroot i) (mem_range_self i)
  convert P.mapsTo_coreflection_coroot j
  ext x
  replace h : P.root' j = t • P.root' i := by ext; simp [h, root']
  simp [Module.preReflection_apply, coreflection_apply, h, smul_comm _ t, mul_smul]

variable {P} in
@[simp] lemma coroot_eq_smul_coroot_iff [Finite ι] [NoZeroSMulDivisors ℤ M] [NoZeroSMulDivisors ℤ N]
    {i j : ι} {t : R} :
    P.coroot i = t • P.coroot j ↔ P.root j = t • P.root i :=
  ⟨fun h ↦ (P.flip.smul_coroot_eq_of_root_eq_smul j i t h).symm,
    fun h ↦ (P.smul_coroot_eq_of_root_eq_smul i j t h).symm⟩

lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
    {r : M ≃ₗ[R] M} {α : M} (hr : r ∈ range P.reflection) (hα : α ∈ range P.root) :
    r • α ∈ range P.root := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩

lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
    {r : N ≃ₗ[R] N} {α : N} (hr : r ∈ range P.coreflection) (hα : α ∈ range P.coroot) :
    r • α ∈ range P.coroot := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.coroot_reflectionPerm i j⟩

lemma pairing_smul_root_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j) :
    P.pairing k i • P.root i = P.pairing k j • P.root j := by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflectionPerm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h

lemma pairing_smul_coroot_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j) :
    P.pairing i k • P.coroot i = P.pairing j k • P.coroot j := by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflectionPerm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h

lemma two_nsmul_reflection_eq_of_perm_eq (hij : P.reflectionPerm i = P.reflectionPerm j) :
    2 • ⇑(P.reflection i) = 2 • P.reflection j := by
  ext x
  suffices
      2 • P.toLinearMap x (P.coroot i) • P.root i = 2 • P.toLinearMap x (P.coroot j) • P.root j by
    simpa [reflection_apply, smul_sub]
  calc 2 • P.toLinearMap x (P.coroot i) • P.root i
      = P.toLinearMap x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLinearMap x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLinearMap x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLinearMap x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLinearMap x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]

lemma reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular (h2 : IsSMulRegular M 2) :
    P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M → M) 2 := IsSMulRegular.pi fun _ ↦ h2
  exact h2 <| P.two_nsmul_reflection_eq_of_perm_eq i j h

@[deprecated (since := "2025-05-28")]
alias reflection_perm_eq_reflection_perm_iff_of_isSMulRegular :=
  reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular

lemma reflectionPerm_eq_reflectionPerm_iff_of_span :
    P.reflectionPerm i = P.reflectionPerm j ↔
    ∀ x ∈ span R (range P.root), P.reflection i x = P.reflection j x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflectionPerm, h]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]

@[deprecated (since := "2025-05-28")]
alias reflection_perm_eq_reflection_perm_iff_of_span := reflectionPerm_eq_reflectionPerm_iff_of_span

lemma _root_.RootSystem.reflectionPerm_eq_reflectionPerm_iff (P : RootSystem ι R M N) (i j : ι) :
    P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  ext x
  exact (P.reflectionPerm_eq_reflectionPerm_iff_of_span i j).mp h x <| by simp

@[deprecated (since := "2025-05-28")]
alias _root_.RootSystem.reflection_perm_eq_reflection_perm_iff :=
  _root_.RootSystem.reflectionPerm_eq_reflectionPerm_iff

@[simp] lemma toPerfPair_comp_root : P.toPerfPair ∘ P.root = P.root' := rfl

@[simp] lemma toPerfPair_flip_comp_coroot :
    P.toLinearMap.flip.toPerfPair ∘ P.coroot = P.coroot' := rfl

/-- The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, when it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperplanes. -/
def coxeterWeight : R := pairing P i j * pairing P j i

lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

/-- Two roots are orthogonal when they are fixed by each others' reflections. -/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0

lemma isOrthogonal_symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [commute_iff_eq]
  ext v
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  erw [Module.End.mul_apply, Module.End.mul_apply]
  simp only [LinearEquiv.coe_coe, reflection_apply, LinearMap.flip_apply, map_sub, map_smul,
    root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel

variable {P i j}

lemma IsOrthogonal.flip (h : IsOrthogonal P i j) : IsOrthogonal P.flip i j := ⟨h.2, h.1⟩

lemma IsOrthogonal.symm (h : IsOrthogonal P i j) : IsOrthogonal P j i := ⟨h.2, h.1⟩

lemma IsOrthogonal.reflection_apply_left (h : IsOrthogonal P i j) :
    P.reflection j (P.root i) = P.root i := by
  simp [reflection_apply, h.1]

lemma IsOrthogonal.reflection_apply_right (h : IsOrthogonal P j i) :
    P.reflection j (P.root i) = P.root i :=
  h.symm.reflection_apply_left

lemma IsOrthogonal.coreflection_apply_left (h : IsOrthogonal P i j) :
    P.coreflection j (P.coroot i) = P.coroot i :=
  h.flip.reflection_apply_left

lemma IsOrthogonal.coreflection_apply_right (h : IsOrthogonal P j i) :
    P.coreflection j (P.coroot i) = P.coroot i :=
  h.flip.reflection_apply_right

lemma isFixedPt_reflection_of_isOrthogonal {s : Set ι} (hj : ∀ i ∈ s, P.IsOrthogonal j i)
    {x : M} (hx : x ∈ span R (P.root '' s)) :
    IsFixedPt (P.reflection j) x := by
  rw [IsFixedPt]
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero]
  | add u v hu hv hu' hv' => rw [map_add, hu', hv']
  | smul t u hu hu' => rw [map_smul, hu']
  | mem u hu =>
      obtain ⟨i, his, rfl⟩ := hu
      exact IsOrthogonal.reflection_apply_right <| hj i his

lemma reflectionPerm_eq_of_pairing_eq_zero (h : P.pairing j i = 0) :
    P.reflectionPerm i j = j :=
  P.root.injective <| by simp [reflection_apply, h]

@[deprecated (since := "2025-05-28")]
alias reflection_perm_eq_of_pairing_eq_zero := reflectionPerm_eq_of_pairing_eq_zero

lemma reflectionPerm_eq_of_pairing_eq_zero' (h : P.pairing i j = 0) :
    P.reflectionPerm i j = j :=
  P.flip.reflectionPerm_eq_of_pairing_eq_zero h

@[deprecated (since := "2025-05-28")]
alias reflection_perm_eq_of_pairing_eq_zero' := reflectionPerm_eq_of_pairing_eq_zero'

lemma reflectionPerm_eq_iff_smul_root :
    P.reflectionPerm i j = j ↔ P.pairing j i • P.root i = 0 :=
  ⟨fun h ↦ by simpa [h] using P.reflectionPerm_root i j,
    fun h ↦ P.root.injective <| by simp [reflection_apply, h]⟩

@[deprecated (since := "2025-05-28")]
alias reflection_perm_eq_iff_smul_root := reflectionPerm_eq_iff_smul_root

lemma reflectionPerm_eq_iff_smul_coroot :
    P.reflectionPerm i j = j ↔ P.pairing i j • P.coroot i = 0 :=
  P.flip.reflectionPerm_eq_iff_smul_root

@[deprecated (since := "2025-05-28")]
alias reflection_perm_eq_iff_smul_coroot := reflectionPerm_eq_iff_smul_coroot

lemma pairing_eq_zero_iff [NeZero (2 : R)] [NoZeroSMulDivisors R M] :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  suffices ∀ {i j : ι}, P.pairing i j = 0 → P.pairing j i = 0 from ⟨this, this⟩
  intro i j h
  simpa [P.ne_zero i, reflectionPerm_eq_iff_smul_root] using
    P.reflectionPerm_eq_of_pairing_eq_zero' h

lemma pairing_eq_zero_iff' [NeZero (2 : R)] [IsDomain R] :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  exact pairing_eq_zero_iff

lemma coxeterWeight_zero_iff_isOrthogonal [NeZero (2 : R)] [IsDomain R] :
    P.coxeterWeight i j = 0 ↔ P.IsOrthogonal i j := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [coxeterWeight, IsOrthogonal, P.pairing_eq_zero_iff (i := i) (j := j)]

lemma isOrthogonal_iff_pairing_eq_zero [NeZero (2 : R)] [NoZeroSMulDivisors R M] :
    P.IsOrthogonal i j ↔ P.pairing i j = 0 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, pairing_eq_zero_iff.mp h⟩⟩

lemma isFixedPt_reflectionPerm_iff [NeZero (2 : R)] [NoZeroSMulDivisors R M] :
    IsFixedPt (P.reflectionPerm i) j ↔ P.pairing i j = 0 := by
  refine ⟨fun h ↦ ?_, P.reflectionPerm_eq_of_pairing_eq_zero'⟩
  simpa [P.ne_zero i, pairing_eq_zero_iff, IsFixedPt, reflectionPerm_eq_iff_smul_root] using h

@[deprecated (since := "2025-05-28")]
alias isFixedPt_reflection_perm_iff := isFixedPt_reflectionPerm_iff

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

/-- Push forward a root pairing along linear equivalences, also reindexing the (co)roots. -/
protected def map (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    RootPairing ι₂ R M₂ N₂ where
  __ := (f.symm.trans P.toPerfPair).trans g.symm.dualMap
  isPerfPair_toLinearMap := by
    have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
    have : IsReflexive R N₂ := equiv g
    infer_instance
  root := (e.symm.toEmbedding.trans P.root).trans f.toEmbedding
  coroot := (e.symm.toEmbedding.trans P.coroot).trans g.toEmbedding
  root_coroot_two i := by simp
  reflectionPerm i := e.symm.trans <| (P.reflectionPerm (e.symm i)).trans e
  reflectionPerm_root i j := by simp [reflection_apply]
  reflectionPerm_coroot i j := by simp [coreflection_apply]

/-- Push forward a root system along linear equivalences, also reindexing the (co)roots. -/
protected def _root_.RootSystem.map {P : RootSystem ι R M N}
    (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    RootSystem ι₂ R M₂ N₂ where
  __ := P.toRootPairing.map e f g
  span_root_eq_top := by simp [Embedding.coe_trans, range_comp, span_image, RootPairing.map]
  span_coroot_eq_top := by simp [Embedding.coe_trans, range_comp, span_image, RootPairing.map]

end Map

end RootPairing
