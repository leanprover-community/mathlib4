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
 * `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
   between a root and coroot is always an integer.
 * `RootPairing.IsReduced`: A root pairing is said to be reduced if two linearly dependent roots are
   always related by a sign.
 * `RootPairing.weylGroup`: The group of linear isomorphisms on `M` generated by reflections.
 * `RootPairing.weylGroupToPerm`: The permutation representation of the Weyl group on `ι`.

## TODO

 * Base change of root pairings (may need flatness; perhaps should go in a different file).
 * Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
   `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

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
open Submodule (span)
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
structure RootPairing extends PerfectPairing R M N where
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflections. This corresponds to the
      classical requirement that the symmetry attached to each root (later defined in
      `RootPairing.reflection`) leave the whole set of roots stable: as explained above, we
      formalize this stability by fixing the image of the roots through each reflection (whence the
      permutation); and similarly for coroots. -/
  reflection_perm : ι → (ι ≃ ι)
  reflection_perm_root : ∀ i j,
    root j - toPerfectPairing (root j) (coroot i) • root i = root (reflection_perm i j)
  reflection_perm_coroot : ∀ i j,
    coroot j - toPerfectPairing (root i) (coroot j) • coroot i = coroot (reflection_perm i j)

/-- A root datum is a root pairing with coefficients in the integers and for which the root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Free ℤ X₁] [Finite ℤ X₁] [Free ℤ X₂] [Finite ℤ X₂]` should be
supplied as mixins. -/
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

lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h, map_zero] using P.root_coroot_two i

lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

@[simp]
lemma toLin_toPerfectPairing (x : M) (y : N) : P.toLin x y = P.toPerfectPairing x y :=
  rfl

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
protected def flip : RootPairing ι R N M :=
  { P.toPerfectPairing.flip with
    root := P.coroot
    coroot := P.root
    root_coroot_two := P.root_coroot_two
    reflection_perm := P.reflection_perm
    reflection_perm_root := P.reflection_perm_coroot
    reflection_perm_coroot := P.reflection_perm_root }

@[simp]
lemma flip_flip : P.flip.flip = P :=
  rfl

variable (ι R M N) in
/-- `RootPairing.flip` as an equivalence. -/
@[simps] def flipEquiv : RootPairing ι R N M ≃ RootPairing ι R M N where
  toFun P := P.flip
  invFun P := P.flip
  left_inv _ := rfl
  right_inv _ := rfl

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
  left_inv _ := rfl
  right_inv _ := rfl

/-- Roots written as functionals on the coweight space. -/
abbrev root' (i : ι) : Dual R N := P.toPerfectPairing (P.root i)

/-- Coroots written as functionals on the weight space. -/
abbrev coroot' (i : ι) : Dual R M := P.toPerfectPairing.flip (P.coroot i)

/-- This is the pairing between roots and coroots. -/
def pairing : R := P.root' i (P.coroot j)

@[simp]
lemma root_coroot_eq_pairing : P.toPerfectPairing (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
lemma root'_coroot_eq_pairing : P.root' i (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
lemma root_coroot'_eq_pairing : P.coroot' i (P.root j) = P.pairing j i :=
  rfl

lemma coroot_root_eq_pairing : P.toLin.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

lemma coroot_root_two :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp

/-- The reflection associated to a root. -/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
lemma root_reflection_perm (j : ι) :
    P.root (P.reflection_perm i j) = (P.reflection i) (P.root j) :=
  (P.reflection_perm_root i j).symm

theorem mapsTo_reflection_root :
    MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)

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
lemma reflection_sq :
    P.reflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

@[simp]
lemma reflection_perm_sq :
    P.reflection_perm i ^ 2 = 1 := by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflection_perm, reflection_same, Equiv.Perm.one_apply]

@[simp]
lemma reflection_perm_inv :
    (P.reflection_perm i)⁻¹ = P.reflection_perm i :=
  (mul_eq_one_iff_eq_inv.mp <| P.reflection_perm_sq i).symm

@[simp]
lemma reflection_perm_self : P.reflection_perm i (P.reflection_perm i j) = j := by
  apply P.root.injective
  simp only [root_reflection_perm, reflection_same]

lemma reflection_perm_involutive : Involutive (P.reflection_perm i) :=
  involutive_iff_iter_2_eq_id.mpr (by ext; simp)

@[simp]
lemma reflection_perm_symm : (P.reflection_perm i).symm = P.reflection_perm i :=
  Involutive.symm_eq_self_of_involutive (P.reflection_perm i) <| P.reflection_perm_involutive i

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
lemma coroot_reflection_perm (j : ι) :
    P.coroot (P.reflection_perm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflection_perm_coroot i j).symm

theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)

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

lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLin.flip = P.toLin.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toPerfectPairing m (P.coroot i))]

lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflection_perm, EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflection_perm, hk]

lemma coroot'_reflection_perm {i j : ι} :
    P.coroot' (P.reflection_perm i j) = P.coroot' j ∘ₗ P.reflection i := by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]

lemma coroot'_reflection {i j : ι} (y : M) :
    P.coroot' j (P.reflection i y) = P.coroot' (P.reflection_perm i j) y :=
  (LinearMap.congr_fun P.coroot'_reflection_perm y).symm

lemma pairing_reflection_perm (i j k : ι) :
    P.pairing j (P.reflection_perm i k) = P.pairing (P.reflection_perm i j) k := by
  simp only [pairing, root', coroot_reflection_perm, root_reflection_perm]
  simp only [coreflection_apply_coroot, map_sub, map_smul, smul_eq_mul,
    reflection_apply_root]
  simp only [← toLin_toPerfectPairing, map_smul, LinearMap.smul_apply, map_sub, map_smul,
    LinearMap.sub_apply, smul_eq_mul]
  simp only [PerfectPairing.toLin_apply, root'_coroot_eq_pairing, sub_right_inj, mul_comm]

@[simp]
lemma pairing_reflection_perm_self_left (P : RootPairing ι R M N) (i j : ι) :
    P.pairing (P.reflection_perm i i) j = - P.pairing i j := by
  rw [pairing, root', ← reflection_perm_root, root'_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, ← toLin_toPerfectPairing, LinearMap.map_neg₂, toLin_toPerfectPairing,
    root'_coroot_eq_pairing]

@[simp]
lemma pairing_reflection_perm_self_right (i j : ι) :
    P.pairing i (P.reflection_perm j j) = - P.pairing i j := by
  rw [pairing, ← reflection_perm_coroot, root_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, ← toLin_toPerfectPairing, map_neg, toLin_toPerfectPairing,
    root_coroot_eq_pairing]

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer. -/
class IsCrystallographic : Prop where
  exists_int : ∀ i j, ∃ z : ℤ, z = P.pairing i j

protected lemma exists_int [P.IsCrystallographic] (i j : ι) :
    ∃ z : ℤ, z = P.pairing i j :=
  IsCrystallographic.exists_int i j

lemma isCrystallographic_iff :
    P.IsCrystallographic ↔ ∀ i j, ∃ z : ℤ, z = P.pairing i j :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

instance [P.IsCrystallographic] : P.flip.IsCrystallographic := by
  rw [isCrystallographic_iff, forall_comm]
  exact P.exists_int

lemma IsCrystallographic.mem_range_algebraMap [P.IsCrystallographic]
    (S : Type*) [CommRing S] [Algebra S R] (i j : ι) :
    P.pairing i j ∈ (algebraMap S R).range := by
  obtain ⟨k, hk⟩ := P.exists_int i j
  simp only [RingHom.mem_range]
  exact ⟨k, by simpa⟩

/-- A root pairing is said to be reduced if any linearly dependent pair of roots is related by a
sign. -/
def IsReduced : Prop :=
  ∀ i j, ¬ LinearIndependent R ![P.root i, P.root j] → (P.root i = P.root j ∨ P.root i = - P.root j)

lemma isReduced_iff : P.IsReduced ↔ ∀ i j : ι, i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · by_cases h' : i = j
    · exact Or.inl (congrArg P.root h')
    · exact Or.inr (h i j h' hLin)

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

/-- The linear span of roots. -/
abbrev rootSpan := span R (range P.root)

/-- The linear span of coroots. -/
abbrev corootSpan := span R (range P.coroot)

lemma coe_rootSpan_dualAnnihilator_map :
    P.rootSpan.dualAnnihilator.map P.toDualRight.symm = {x | ∀ i, P.root' i x = 0} := by
  ext x
  rw [rootSpan, Submodule.map_coe, Submodule.coe_dualAnnihilator_span]
  change x ∈ P.toDualRight.toEquiv.symm '' _ ↔ _
  rw [← Equiv.setOf_apply_symm_eq_image_setOf, Equiv.symm_symm]
  simp [Set.range_subset_iff]

lemma coe_corootSpan_dualAnnihilator_map :
    P.corootSpan.dualAnnihilator.map P.toDualLeft.symm = {x | ∀ i, P.coroot' i x = 0} :=
  P.flip.coe_rootSpan_dualAnnihilator_map

lemma rootSpan_dualAnnihilator_map_eq :
    P.rootSpan.dualAnnihilator.map P.toDualRight.symm =
      (span R (range P.root')).dualCoannihilator := by
  apply SetLike.coe_injective
  rw [Submodule.coe_dualCoannihilator_span, coe_rootSpan_dualAnnihilator_map]
  simp

lemma corootSpan_dualAnnihilator_map_eq :
    P.corootSpan.dualAnnihilator.map P.toDualLeft.symm =
      (span R (range P.coroot')).dualCoannihilator :=
  P.flip.rootSpan_dualAnnihilator_map_eq

lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
    {r : M ≃ₗ[R] M} {α : M} (hr : r ∈ range P.reflection) (hα : α ∈ range P.root) :
    r • α ∈ range P.root := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflection_perm i j, P.root_reflection_perm i j⟩

lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
    {r : N ≃ₗ[R] N} {α : N} (hr : r ∈ range P.coreflection) (hα : α ∈ range P.coroot) :
    r • α ∈ range P.coroot := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflection_perm i j, P.coroot_reflection_perm i j⟩

lemma pairing_smul_root_eq (k : ι) (hij : P.reflection_perm i = P.reflection_perm j) :
    P.pairing k i • P.root i = P.pairing k j • P.root j := by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflection_perm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h

lemma pairing_smul_coroot_eq (k : ι) (hij : P.reflection_perm i = P.reflection_perm j) :
    P.pairing i k • P.coroot i = P.pairing j k • P.coroot j := by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflection_perm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h

lemma two_nsmul_reflection_eq_of_perm_eq (hij : P.reflection_perm i = P.reflection_perm j) :
    2 • ⇑(P.reflection i) = 2 • P.reflection j := by
  ext x
  suffices 2 • P.toLin x (P.coroot i) • P.root i = 2 • P.toLin x (P.coroot j) • P.root j by
    simpa [reflection_apply, smul_sub]
  calc 2 • P.toLin x (P.coroot i) • P.root i
      = P.toLin x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLin x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLin x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLin x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLin x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]

lemma reflection_perm_eq_reflection_perm_iff_of_isSMulRegular (h2 : IsSMulRegular M 2) :
    P.reflection_perm i = P.reflection_perm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M → M) 2 := IsSMulRegular.pi fun _ ↦ h2
  exact h2 <| P.two_nsmul_reflection_eq_of_perm_eq i j h

lemma reflection_perm_eq_reflection_perm_iff_of_span :
    P.reflection_perm i = P.reflection_perm j ↔
    ∀ x ∈ span R (range P.root), P.reflection i x = P.reflection j x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflection_perm, h]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]

lemma _root_.RootSystem.reflection_perm_eq_reflection_perm_iff (P : RootSystem ι R M N) (i j : ι) :
    P.reflection_perm i = P.reflection_perm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  ext x
  exact (P.reflection_perm_eq_reflection_perm_iff_of_span i j).mp h x <| by simp

/-- The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, when it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperplanes. -/
def coxeterWeight : R := pairing P i j * pairing P j i

lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

lemma exists_int_eq_coxeterWeight [P.IsCrystallographic] (i j : ι) :
    ∃ z : ℤ, P.coxeterWeight i j = z := by
  obtain ⟨a, ha⟩ := P.exists_int i j
  obtain ⟨b, hb⟩ := P.exists_int j i
  exact ⟨a * b, by simp [coxeterWeight, ha, hb]⟩

/-- Two roots are orthogonal when they are fixed by each others' reflections. -/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0

lemma isOrthogonal_symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

lemma IsOrthogonal.symm (h : IsOrthogonal P i j) : IsOrthogonal P j i :=
  ⟨h.2, h.1⟩

lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [commute_iff_eq]
  ext v
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  erw [LinearMap.mul_apply, LinearMap.mul_apply]
  simp only [LinearEquiv.coe_coe, reflection_apply, PerfectPairing.flip_apply_apply, map_sub,
    map_smul, root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel

end RootPairing
