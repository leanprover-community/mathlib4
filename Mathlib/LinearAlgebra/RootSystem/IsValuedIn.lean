/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan, Oliver Nash
-/
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root pairings taking values in a subring

This file lays out the basic theory of root pairings over a commutative ring `R`, where `R` is an
`S`-algebra, and the the pairing between roots and coroots takes values in `S`. The main application
of this theory is the theory of crystallographic root systems, where `S = ℤ`.

## Main definitions:

* `RootPairing.IsValuedIn`: Given a commutative ring `S` and an `S`-algebra `R`, a root pairing
  over `R` is valued in `S` if all root-coroot pairings lie in the image of `algebraMap S R`.
* `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
  between a root and coroot is always an integer.
* `RootPairing.pairingIn`: The `S`-valued pairing between roots and coroots.
* `RootPairing.coxeterWeightIn`: The product of `pairingIn i j` and `pairingIn j i`.

-/

open Set Function
open Submodule (span)
open Module


noncomputable section

namespace RootPairing

variable {ι R S M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (i j : ι)

/-- If `R` is an `S`-algebra, a root pairing over `R` is said to be valued in `S` if the pairing
between a root and coroot always belongs to `S`.

Of particular interest is the case `S = ℤ`. See `RootPairing.IsCrystallographic`. -/
@[mk_iff]
class IsValuedIn (S : Type*) [CommRing S] [Algebra S R] : Prop where
  exists_value : ∀ i j, ∃ s, algebraMap S R s = P.pairing i j

protected alias exists_value := IsValuedIn.exists_value

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer. -/
abbrev IsCrystallographic := P.IsValuedIn ℤ

instance : P.IsValuedIn R where
  exists_value i j := by simp

variable (S : Type*) [CommRing S] [Algebra S R]

variable {S} in
lemma isValuedIn_iff_mem_range :
    P.IsValuedIn S ↔ ∀ i j, P.pairing i j ∈ range (algebraMap S R) := by
  simp only [isValuedIn_iff, mem_range]

instance [P.IsValuedIn S] : P.flip.IsValuedIn S := by
  rw [isValuedIn_iff, forall_comm]
  exact P.exists_value

/-- A variant of `RootPairing.pairing` for root pairings which are valued in a smaller set of
coefficients.

Note that it is uniquely-defined only when the map `S → R` is injective, i.e., when we have
`[FaithfulSMul S R]`. -/
def pairingIn [P.IsValuedIn S] (i j : ι) : S :=
  (P.exists_value i j).choose

@[simp]
lemma algebraMap_pairingIn [P.IsValuedIn S] (i j : ι) :
    algebraMap S R (P.pairingIn S i j) = P.pairing i j :=
  (P.exists_value i j).choose_spec

@[simp]
lemma pairingIn_same [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    P.pairingIn S i i = 2 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [map_ofNat]

variable {P S} in
lemma pairingIn_eq_add_of_root_eq_add [FaithfulSMul S R] [P.IsValuedIn S]
    {i j k l : ι} (h : P.root k = P.root i + P.root l) :
    P.pairingIn S k j = P.pairingIn S i j + P.pairingIn S l j := by
  apply FaithfulSMul.algebraMap_injective S R
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using pairing_eq_add_of_root_eq_add h

variable {P S} in
lemma pairingIn_eq_add_of_root_eq_smul_add_smul
    [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsScalarTower S R M]
    {i j k l : ι} {x y : S} (h : P.root k = x • P.root i + y • P.root l) :
    P.pairingIn S k j = x • P.pairingIn S i j + y • P.pairingIn S l j := by
  apply FaithfulSMul.algebraMap_injective S R
  replace h : P.root k = (algebraMap S R x) • P.root i + (algebraMap S R y) • P.root l := by simpa
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using
    pairing_eq_add_of_root_eq_smul_add_smul h

lemma pairingIn_reflectionPerm [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
    P.pairingIn S j (P.reflectionPerm i k) = P.pairingIn S (P.reflectionPerm i j) k := by
  simp only [← (FaithfulSMul.algebraMap_injective S R).eq_iff, algebraMap_pairingIn]
  exact pairing_reflectionPerm P i j k

@[deprecated (since := "2025-05-28")] alias pairingIn_reflection_perm := pairingIn_reflectionPerm

@[simp]
lemma pairingIn_reflectionPerm_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S (P.reflectionPerm i i) j = - P.pairingIn S i j := by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

@[deprecated (since := "2025-05-28")]
alias pairingIn_reflection_perm_self_left := pairingIn_reflectionPerm_self_left

@[simp]
lemma pairingIn_reflectionPerm_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S i (P.reflectionPerm j j) = - P.pairingIn S i j := by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

@[deprecated (since := "2025-05-28")]
alias pairingIn_reflection_perm_self_right := pairingIn_reflectionPerm_self_right

lemma IsValuedIn.trans (T : Type*) [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R]
    [P.IsValuedIn T] :
    P.IsValuedIn S where
  exists_value i j := by
    use algebraMap T S (P.pairingIn T i j)
    simp [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq T S R]

lemma coroot'_apply_apply_mem_of_mem_span [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]
    {x : M} (hx : x ∈ span S (range P.root)) (i : ι) :
    P.coroot' i x ∈ range (algebraMap S R) := by
  rw [show range (algebraMap S R) = LinearMap.range (Algebra.linearMap S R) by ext; simp]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    simpa using RootPairing.exists_value k i
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul t x _ hx => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ t hx

lemma root'_apply_apply_mem_of_mem_span [Module S N] [IsScalarTower S R N] [P.IsValuedIn S]
    {x : N} (hx : x ∈ span S (range P.coroot)) (i : ι) :
    P.root' i x ∈ LinearMap.range (Algebra.linearMap S R) :=
  P.flip.coroot'_apply_apply_mem_of_mem_span S hx i

/-- The `S`-span of roots. -/
abbrev rootSpan [Module S M] := span S (range P.root)

/-- The `S`-span of coroots. -/
abbrev corootSpan [Module S N] := span S (range P.coroot)

instance [Module S M] [Finite ι] :
    Module.Finite S <| P.rootSpan S :=
  Finite.span_of_finite S <| finite_range _

instance [Module S N] [Finite ι] :
    Module.Finite S <| P.corootSpan S :=
  Finite.span_of_finite S <| finite_range _

/-- A root, seen as an element of the span of roots. -/
abbrev rootSpanMem [Module S M] (i : ι) : P.rootSpan S :=
  ⟨P.root i, Submodule.subset_span (mem_range_self i)⟩

/-- A coroot, seen as an element of the span of coroots. -/
abbrev corootSpanMem [Module S N] (i : ι) : P.corootSpan S :=
  ⟨P.coroot i, Submodule.subset_span (mem_range_self i)⟩

omit [Algebra S R] in
lemma rootSpanMem_reflectionPerm_self [Module S M] (i : ι) :
    P.rootSpanMem S (P.reflectionPerm i i) = - P.rootSpanMem S i := by
  ext; simp

@[deprecated (since := "2025-05-28")]
alias rootSpanMem_reflection_perm_self := rootSpanMem_reflectionPerm_self

omit [Algebra S R] in
lemma corootSpanMem_reflectionPerm_self [Module S N] (i : ι) :
    P.corootSpanMem S (P.reflectionPerm i i) = - P.corootSpanMem S i := by
  ext; simp

@[deprecated (since := "2025-05-28")]
alias corootSpanMem_reflection_perm_self := corootSpanMem_reflectionPerm_self

/-- The `S`-linear map on the span of coroots given by evaluating at a root. -/
def root'In [Module S N] [IsScalarTower S R N] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    Dual S (P.corootSpan S) :=
  LinearMap.restrictScalarsRange (P.corootSpan S).subtype (Algebra.linearMap S R)
    (FaithfulSMul.algebraMap_injective S R) (P.root' i)
    (fun m ↦ P.root'_apply_apply_mem_of_mem_span S m.2 i)

@[simp]
lemma algebraMap_root'In_apply [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
    [P.IsValuedIn S] (i : ι) (x : P.corootSpan S) :
    algebraMap S R (P.root'In S i x) = P.root' i x := by
  rw [root'In, ← Algebra.linearMap_apply, LinearMap.restrictScalarsRange_apply,
    Submodule.subtype_apply]

@[simp]
lemma root'In_corootSpanMem_eq_pairingIn [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
    [P.IsValuedIn S] :
    P.root'In S i (P.corootSpanMem S j) = P.pairingIn S i j :=
  rfl

/-- The `S`-linear map on the span of roots given by evaluating at a coroot. -/
def coroot'In [Module S M] [IsScalarTower S R M] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    Dual S (P.rootSpan S) :=
  P.flip.root'In S i

@[simp]
lemma algebraMap_coroot'In_apply [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
    [P.IsValuedIn S] (i : ι) (x : P.rootSpan S) :
    algebraMap S R (P.coroot'In S i x) = P.coroot' i x :=
  P.flip.algebraMap_root'In_apply S i x

@[simp]
lemma coroot'In_rootSpanMem_eq_pairingIn [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
    [P.IsValuedIn S] :
    P.coroot'In S i (P.rootSpanMem S j) = P.pairingIn S j i :=
  rfl

omit [Algebra S R] in
lemma rootSpan_ne_bot [Module S M] [Nonempty ι] [NeZero (2 : R)] : P.rootSpan S ≠ ⊥ := by
  simpa [rootSpan] using P.exists_ne_zero

omit [Algebra S R] in
lemma corootSpan_ne_bot [Module S N] [Nonempty ι] [NeZero (2 : R)] : P.corootSpan S ≠ ⊥ :=
  P.flip.rootSpan_ne_bot S

lemma rootSpan_mem_invtSubmodule_reflection (i : ι) :
    P.rootSpan R ∈ Module.End.invtSubmodule (P.reflection i) := by
  rw [Module.End.mem_invtSubmodule, rootSpan]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply_root]
    apply Submodule.sub_mem
    · exact Submodule.subset_span <| mem_range_self j
    · exact Submodule.smul_mem _ _ <| Submodule.subset_span <| mem_range_self i
  | zero => simp
  | add y z hy hz hy' hz' => simpa using Submodule.add_mem _ hy' hz'
  | smul y t hy hy' => simpa using Submodule.smul_mem _ _ hy'

lemma corootSpan_mem_invtSubmodule_coreflection (i : ι) :
    P.corootSpan R ∈ Module.End.invtSubmodule (P.coreflection i) :=
  P.flip.rootSpan_mem_invtSubmodule_reflection i

lemma rootSpan_dualAnnihilator_map_eq_iInf_ker_root' :
    (P.rootSpan R).dualAnnihilator.map P.toDualRight.symm = ⨅ i, LinearMap.ker (P.root' i) := by
  suffices (P.rootSpan R).dualAnnihilator.map P.toDualRight.symm = {x | ∀ i, P.root' i x = 0} from
    SetLike.coe_injective <| by ext; simp [this]
  ext x
  rw [rootSpan, Submodule.map_coe, Submodule.coe_dualAnnihilator_span,
    ← LinearEquiv.coe_symm_toEquiv, ← Equiv.setOf_apply_symm_eq_image_setOf, Equiv.symm_symm]
  simp [Set.range_subset_iff]

lemma corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot' :
    (P.corootSpan R).dualAnnihilator.map P.toDualLeft.symm = ⨅ i, LinearMap.ker (P.coroot' i) :=
  P.flip.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'

lemma rootSpan_dualAnnihilator_map_eq :
    (P.rootSpan R).dualAnnihilator.map P.toDualRight.symm =
      (span R (range P.root')).dualCoannihilator :=
  SetLike.coe_injective <| by ext; simp [P.rootSpan_dualAnnihilator_map_eq_iInf_ker_root']

lemma corootSpan_dualAnnihilator_map_eq :
    (P.corootSpan R).dualAnnihilator.map P.toDualLeft.symm =
      (span R (range P.coroot')).dualCoannihilator :=
  P.flip.rootSpan_dualAnnihilator_map_eq

lemma iInf_ker_root'_eq :
    ⨅ i, LinearMap.ker (P.root' i) = (span R (range P.root')).dualCoannihilator := by
  rw [← rootSpan_dualAnnihilator_map_eq, rootSpan_dualAnnihilator_map_eq_iInf_ker_root']

lemma iInf_ker_coroot'_eq :
    ⨅ i, LinearMap.ker (P.coroot' i) = (span R (range P.coroot')).dualCoannihilator :=
  P.flip.iInf_ker_root'_eq

@[simp] lemma rootSpan_map_toDualLeft :
    (P.rootSpan R).map P.toDualLeft = span R (range P.root') := by
  rw [rootSpan, Submodule.map_span, ← image_univ, ← image_comp, image_univ, toDualLeft_comp_root]

@[simp] lemma corootSpan_map_toDualRight :
    (P.corootSpan R).map P.toDualRight = span R (range P.coroot') :=
  P.flip.rootSpan_map_toDualLeft

@[simp] lemma span_root'_eq_top (P : RootSystem ι R M N) :
    span R (range P.root') = ⊤ := by
  simp [← rootSpan_map_toDualLeft]

@[simp] lemma span_coroot'_eq_top (P : RootSystem ι R M N) :
    span R (range P.coroot') = ⊤ :=
  span_root'_eq_top P.flip

lemma pairingIn_eq_zero_iff {S : Type*} [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [P.IsValuedIn S] [NoZeroSMulDivisors R M] [NeZero (2 : R)] {i j : ι} :
    P.pairingIn S i j = 0 ↔ P.pairingIn S j i = 0 := by
  simpa only [← FaithfulSMul.algebraMap_eq_zero_iff S R, algebraMap_pairingIn] using
    P.pairing_eq_zero_iff

variable {P i j} in
lemma reflection_apply_root' (S : Type*) [CommRing S] [Algebra S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] :
    P.reflection i (P.root j) = P.root j - (P.pairingIn S j i) • P.root i := by
  rw [reflection_apply_root, ← P.algebraMap_pairingIn S, algebraMap_smul]

/-- A variant of `RootPairing.coxeterWeight` for root pairings which are valued in a smaller set of
coefficients.

Note that it is uniquely-defined only when the map `S → R` is injective, i.e., when we have
`[FaithfulSMul S R]`. -/
def coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] (i j : ι) : S :=
  P.pairingIn S i j * P.pairingIn S j i

@[simp] lemma algebraMap_coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S]
    (i j : ι) :
    algebraMap S R (P.coxeterWeightIn S i j) = P.coxeterWeight i j := by
  simp [coxeterWeightIn, coxeterWeight]

end RootPairing
