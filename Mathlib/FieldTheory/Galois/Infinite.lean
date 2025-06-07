/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
/-!

# The Fundamental Theorem of Infinite Galois Theory

In this file, we prove the fundamental theorem of infinite Galois theory and the special case for
open subgroups and normal subgroups. We first verify that `IntermediateField.fixingSubgroup` and
`IntermediateField.fixedField` are inverses of each other between intermediate fields and
closed subgroups of the Galois group.

# Main definitions and results

In `K/k`, for any intermediate field `L` :

* `fixingSubgroup_isClosed` : the subgroup fixing `L` (`Gal(K/L)`) is closed.

* `fixedField_fixingSubgroup` : the field fixed by the
  subgroup fixing `L` is equal to `L` itself.

For any subgroup `H` of `Gal(K/k)` :

* `restrict_fixedField` : For a Galois intermediate field `M`, the fixed field of the image of `H`
  restricted to `M` is equal to the fixed field of `H` intersected with `M`.
* `fixingSubgroup_fixedField` : If `H` is closed, the fixing subgroup of the fixed field of `H`
  is equal to `H` itself.

The fundamental theorem of infinite Galois theory :

* `IntermediateFieldEquivClosedSubgroup` : The order equivalence is given by mapping any
  intermediate field `L` to the subgroup fixing `L`, and the inverse maps any
  closed subgroup of `Gal(K/k)` `H` to the fixed field of `H`. The composition is equal to
  the identity as described in the lemmas above, and compatibility with the order follows easily.

Special cases :

* `isOpen_iff_finite` : The fixing subgroup of an intermediate field `L` is open if and only if
  `L` is finite-dimensional.

* `normal_iff_isGalois` : The fixing subgroup of an intermediate field `L` is normal if and only if
  `L` is Galois.

-/

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

open Pointwise FiniteGaloisIntermediateField AlgEquiv
--Note: The `adjoin`s below are `FiniteGaloisIntermediateField.adjoin`

lemma fixingSubgroup_isClosed (L : IntermediateField k K) [IsGalois k K] :
    IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ h => by
    apply mem_nhds_iff.mpr
    rcases Set.not_subset.mp ((mem_fixingSubgroup_iff (K ≃ₐ[k] K)).not.mp h) with ⟨y, yL, ne⟩
    use σ • ((adjoin k {y}).1.fixingSubgroup : Set (K ≃ₐ[k] K))
    constructor
    · intro f hf
      rcases (Set.mem_smul_set.mp hf) with ⟨g, hg, eq⟩
      simp only [Set.mem_compl_iff, SetLike.mem_coe, ← eq]
      apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).not.mpr
      push_neg
      use y
      simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
      have : g y = y := (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp hg y <|
        adjoin_simple_le_iff.mp le_rfl
      simpa only [this, ne_eq, AlgEquiv.smul_def] using ne
    · simp only [(IntermediateField.fixingSubgroup_isOpen (adjoin k {y}).1).smul σ, true_and]
      use 1
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true, Subgroup.one_mem]

lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
    IntermediateField.fixedField L.fixingSubgroup = L := by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have mem : x ∈ (adjoin L {x}).1 := subset_adjoin _ _ rfl
    have : IntermediateField.fixedField (⊤ : Subgroup ((adjoin L {x}) ≃ₐ[L] (adjoin L {x}))) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ ∈ (⊥ : IntermediateField L (adjoin L {x})) := by
      rw [← this, IntermediateField.mem_fixedField_iff]
      intro f _
      rcases restrictNormalHom_surjective K f with ⟨σ,hσ⟩
      apply Subtype.val_injective
      rw [← hσ, restrictNormalHom_apply (adjoin L {x}).1 σ ⟨x, mem⟩]
      have := hx ((IntermediateField.fixingSubgroupEquiv L).symm σ)
      simpa only [SetLike.coe_mem, true_implies]
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr le_rfl

lemma fixedField_bot [IsGalois k K] :
    IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) = ⊥ := by
  rw [← IntermediateField.fixingSubgroup_bot, fixedField_fixingSubgroup]

open IntermediateField in
/-- For a subgroup `H` of `Gal(K/k)`, the fixed field of the image of `H` under the restriction to
a normal intermediate field `E` is equal to the fixed field of `H` in `K` intersecting with `E`. -/
lemma restrict_fixedField (H : Subgroup (K ≃ₐ[k] K)) (L : IntermediateField k K) [Normal k L] :
    fixedField H ⊓ L = lift (fixedField (Subgroup.map (restrictNormalHom L) H)) := by
  apply SetLike.ext'
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have xL := h.out.2
    apply (mem_lift (⟨x, xL⟩ : L)).mpr
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro σ hσ
    apply Subtype.val_injective
    dsimp only
    nth_rw 2 [← (h.out.1 ⟨σ, hσ⟩)]
    exact AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
  · have xL := lift_le _ h
    apply (mem_lift (⟨x, xL⟩ : L)).mp at h
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    simp only [coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_fixedField_iff, xL, and_true]
    intro σ hσ
    have : ((restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by rw [h σ hσ]
    nth_rw 2 [← this]
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm

open IntermediateField in
lemma fixingSubgroup_fixedField (H : ClosedSubgroup (K ≃ₐ[k] K)) [IsGalois k K] :
    (IntermediateField.fixedField H).fixingSubgroup = H.1 := by
  apply le_antisymm _ ((IntermediateField.le_iff_le H.toSubgroup
    (IntermediateField.fixedField H.toSubgroup)).mp le_rfl)
  intro σ hσ
  by_contra h
  have nhds : H.carrierᶜ ∈ nhds σ := H.isClosed'.isOpen_compl.mem_nhds h
  rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhds
  rcases nhds with ⟨b, ⟨gp, ⟨L, hL, eq'⟩, eq⟩, sub⟩
  rw [← eq'] at eq
  have := hL.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k L K with
    finiteDimensional := normalClosure.is_finiteDimensional k L K
    isGalois := IsGalois.normalClosure k L K }
  have compl : σ • L'.1.fixingSubgroup.carrier ⊆ H.carrierᶜ := by
    rintro φ ⟨τ, hτ, muleq⟩
    have sub' : σ • b ⊆ H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
    apply sub'
    simp only [← muleq, ← eq]
    apply Set.smul_mem_smul_set
    exact (L.fixingSubgroup_le (IntermediateField.le_normalClosure L) hτ)
  have fix : ∀ x ∈ IntermediateField.fixedField H.toSubgroup ⊓ ↑L', σ x = x :=
    fun x hx ↦ ((mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp hσ) x hx.1
  rw [restrict_fixedField H.1 L'.1] at fix
  have : (restrictNormalHom L') σ ∈ (Subgroup.map (restrictNormalHom L') H.1) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.map (restrictNormalHom L') H.1)]
    apply (mem_fixingSubgroup_iff (L' ≃ₐ[k] L')).mpr
    intro y hy
    apply Subtype.val_injective
    simp only [AlgEquiv.smul_def, restrictNormalHom_apply L'.1 σ y,
      fix y.1 ((IntermediateField.mem_lift y).mpr hy)]
  rcases this with ⟨h, mem, eq⟩
  have : h ∈ σ • L'.1.fixingSubgroup.carrier := by
    use σ⁻¹ * h
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
      smul_eq_mul, mul_inv_cancel_left, and_true]
    apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mpr
    intro y hy
    simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
    have : ((restrictNormalHom L') h ⟨y,hy⟩).1 = ((restrictNormalHom L') σ ⟨y,hy⟩).1 := by rw [eq]
    rw [restrictNormalHom_apply L'.1 h ⟨y, hy⟩, restrictNormalHom_apply L'.1 σ ⟨y, hy⟩] at this
    simp only [this, ← AlgEquiv.mul_apply, inv_mul_cancel, one_apply]
  absurd compl
  apply Set.not_subset.mpr
  use h
  simpa only [this, Set.mem_compl_iff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid, not_not, true_and] using mem

/-- The Galois correspondence from intermediate fields to closed subgroups. -/
def IntermediateFieldEquivClosedSubgroup [IsGalois k K] :
    IntermediateField k K ≃o (ClosedSubgroup (K ≃ₐ[k] K))ᵒᵈ where
  toFun L := ⟨L.fixingSubgroup, fixingSubgroup_isClosed L⟩
  invFun H := IntermediateField.fixedField H.1
  left_inv L := fixedField_fixingSubgroup L
  right_inv H := by
    simp_rw [fixingSubgroup_fixedField H]
    rfl
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L, IntermediateField.le_iff_le, fixedField_fixingSubgroup L]
    rfl

/-- The Galois correspondence as a `GaloisInsertion` -/
def GaloisInsertionIntermediateFieldClosedSubgroup [IsGalois k K] :
    GaloisInsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) ↦
      (⟨E.fixingSubgroup, fixingSubgroup_isClosed E⟩ : ClosedSubgroup (K ≃ₐ[k] K)))
      ((fun (H : ClosedSubgroup (K ≃ₐ[k] K)) ↦ IntermediateField.fixedField H) ∘
        OrderDual.toDual) :=
  OrderIso.toGaloisInsertion IntermediateFieldEquivClosedSubgroup

/-- The Galois correspondence as a `GaloisCoinsertion` -/
def GaloisCoinsertionIntermediateFieldSubgroup [IsGalois k K] :
    GaloisCoinsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) ↦ E.fixingSubgroup)
      ((fun (H : Subgroup (K ≃ₐ[k] K)) ↦ IntermediateField.fixedField H) ∘ OrderDual.toDual) where
  choice H _ := IntermediateField.fixedField H
  gc E H := (IntermediateField.le_iff_le H E).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl

open IntermediateField in
theorem isOpen_iff_finite (L : IntermediateField k K) [IsGalois k K] :
    IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k L := by
  refine ⟨fun h ↦ ?_, fun h ↦ IntermediateField.fixingSubgroup_isOpen L⟩
  have : (IntermediateFieldEquivClosedSubgroup.toFun L).carrier ∈ nhds 1 :=
    IsOpen.mem_nhds h (congrFun rfl)
  rw [GroupFilterBasis.nhds_one_eq] at this
  rcases this with ⟨S, ⟨gp, ⟨M, hM, eq'⟩, eq⟩, sub⟩
  rw [← eq, ← eq'] at sub
  have := hM.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k M K with
    finiteDimensional := normalClosure.is_finiteDimensional k M K
    isGalois := IsGalois.normalClosure k M K }
  have : L ≤ L'.1 := by
    apply le_trans _ (IntermediateField.le_normalClosure M)
    rw [←  fixedField_fixingSubgroup M, IntermediateField.le_iff_le]
    exact sub
  let _ : Algebra L L'.1 := RingHom.toAlgebra (IntermediateField.inclusion this)
  exact FiniteDimensional.left k L L'.1

theorem normal_iff_isGalois (L : IntermediateField k K) [IsGalois k K] :
    L.fixingSubgroup.Normal ↔ IsGalois k L := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let g (x : K) := L.fixingSubgroup.map (restrictNormalHom (adjoin k {x}))
    let f (x : L) : IntermediateField k K := IntermediateField.lift <|
      IntermediateField.fixedField <| g x.1
    have (x : K) : (g x).Normal :=
      Subgroup.Normal.map h (restrictNormalHom (adjoin k {x})) (restrictNormalHom_surjective K)
    have (l : L) := IsGalois.of_fixedField_normal_subgroup (g l.1)
    have (l : L) : Normal k (f l) :=
      Normal.of_algEquiv <| IntermediateField.liftAlgEquiv <| IntermediateField.fixedField (g l.1)
    have n : Normal k ↥(⨆ l : L, f l) := IntermediateField.normal_iSup k K f
    have : (⨆ l : L, f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l.1}),
          fixedField_fixingSubgroup L] using inf_le_left
      · intro l hl
        apply le_iSup f ⟨l, hl⟩
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l}),
          fixedField_fixingSubgroup L, IntermediateField.mem_inf, hl, true_and]
          using adjoin_simple_le_iff.mp le_rfl
    rw [this] at n
    let _ : Algebra.IsSeparable k L := Algebra.isSeparable_tower_bot_of_isSeparable k L K
    apply IsGalois.mk
  · simpa only [IntermediateFieldEquivClosedSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← L.restrictNormalHom_ker] using MonoidHom.normal_ker (restrictNormalHom L)

theorem isOpen_and_normal_iff_finite_and_isGalois (L : IntermediateField k K) [IsGalois k K] :
    IsOpen L.fixingSubgroup.carrier ∧ L.fixingSubgroup.Normal ↔
    FiniteDimensional k L ∧ IsGalois k L := by
  rw [isOpen_iff_finite, normal_iff_isGalois]

end InfiniteGalois
