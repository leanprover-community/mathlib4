/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Topology.Algebra.ClosedSubgroup
/-!

# The Fundamental Theorem of Infinite Galois Theory

In this file, we proved the fundamental theorem of infinite Galois theory and the special case for
open subgroups and normal subgroups. We first verify that IntermediateField.fixingSubgroup and
IntermediateField.fixedField are inverses of each other between IntermediateFields and
closed subgroups of the Galois group.

# Main definitions and results

In `K/k`, for any intermediate field `L` :

* `fixingSubgroup_isClosed` : the fixing subgroup of `L`
  (`Gal(K/L)`) is closed.

* `fixedField_fixingSubgroup` : the fixing field of the
  fixing subgroup of `L` is equal to `L` itself.

For any subgroup of `Gal(K/k)` `H` :

* `restrict_fixedField` : For a Galois intermediate field `M`, the fixed field of the image of `H`
  restricted to `M` is equal to the fixed field of `H` intersected with `M`.
* `fixingSubgroup_fixedField` : If `H` is closed, the fixing subgroup of the fixed field of `H`
  is equal to `H` itself.

The fundamental theorem of infinite galois theory :

* `IntermediateFieldEquivClosedSubgroup` : The order equivalence is given by mapping any
  intermediate field `L` to the fixing subgroup of `L`, with its inverse mapping any
  closed subgroup of `Gal(K/k)` `H` to the fixed field of `H`. The composition is equal to
  the identity as described in the lemmas above, and compatibility with the order follows easily.

Special cases :

* `OpeniffFinite` : The fixing subgroup of an intermediate field `L` is open iff
  `L` is finite-dimensional.

* `NormaliffGalois` : The fixing subgroup of an intermediate field `L` is normal iff
  `L` is Galois.

-/

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

open Pointwise FiniteGaloisIntermediateField AlgEquiv
--Note: The `adjoin`s below are `FiniteGaloisIntermediateField.adjoin`

instance : TopologicalSpace (K ≃ₐ[k] K) := inferInstance

lemma fixingSubgroup_isClosed (L : IntermediateField k K) [IsGalois k K] :
    IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) where
    isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ h => by
      apply mem_nhds_iff.mpr
      have := (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).not.mp h
      push_neg at this
      rcases this with ⟨y,yL,ne⟩
      use σ • ((adjoin k {y}).1.fixingSubgroup : Set (K ≃ₐ[k] K))
      constructor
      · intro f hf
        rcases (Set.mem_smul_set.mp hf) with ⟨g,hg,eq⟩
        simp only [Set.mem_compl_iff, SetLike.mem_coe, ← eq]
        apply (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).not.mpr
        push_neg
        use y
        simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
        have := (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp hg y <|
          adjoin_simple_le_iff.mp fun ⦃x⦄ a ↦ a
        simp only [AlgEquiv.smul_def] at this
        rw [this]
        exact ne
      · simp only [(IntermediateField.fixingSubgroup_isOpen (adjoin k {y}).1).smul σ, true_and]
        apply Set.mem_smul_set.mpr
        use 1
        simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true]
        exact congrFun rfl

lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
    IntermediateField.fixedField L.fixingSubgroup = L := by
  letI : IsGalois L K := inferInstance
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have mem : x ∈ (adjoin L {x}).1 := subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])
    have : IntermediateField.fixedField (⊤ : Subgroup ((adjoin L {x}) ≃ₐ[L] (adjoin L {x}))) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ ∈ (⊥ : IntermediateField L (adjoin L {x})) := by
      rw [← this, IntermediateField.mem_fixedField_iff]
      intro f _
      rcases restrictNormalHom_surjective K f with ⟨σ,hσ⟩
      apply Subtype.val_injective
      rw [← hσ, restrictNormalHom_apply (adjoin L {x}).1 σ ⟨x, mem⟩]
      have := hx ((IntermediateField.fixingSubgroupEquiv L).symm σ)
      simp only [SetLike.coe_mem, true_implies] at this
      exact this
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr fun ⦃x⦄ a ↦ a

lemma fixedField_bot [IsGalois k K] :
    IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) = ⊥ := by
  rw [← IntermediateField.fixingSubgroup_bot, fixedField_fixingSubgroup]

lemma restrict_fixedField (H : Subgroup (K ≃ₐ[k] K)) (L : IntermediateField k K) [IsGalois k L] :
    (IntermediateField.fixedField H) ⊓ L = IntermediateField.lift (IntermediateField.fixedField
    (Subgroup.map (restrictNormalHom (F := k) (K₁ := K) L) H)) := by
  apply SetLike.ext'
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have xL := h.out.2
    apply (IntermediateField.mem_lift (⟨x, xL⟩ : L)).mpr
    rw [IntermediateField.mem_fixedField_iff]
    simp only [Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro σ hσ
    apply Subtype.val_injective
    dsimp
    nth_rw 2 [← (h.out.1 ⟨σ, hσ⟩)]
    exact AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
  · have xL := IntermediateField.lift_le _ h
    apply (IntermediateField.mem_lift (⟨x,xL⟩ : L)).mp at h
    simp only [IntermediateField.mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    simp only [IntermediateField.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      IntermediateField.mem_fixedField_iff, xL, and_true]
    intro σ hσ
    have : ((restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by rw [h σ hσ]
    nth_rw 2 [← this]
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm

lemma fixingSubgroup_fixedField (H : ClosedSubgroup (K ≃ₐ[k] K)) [IsGalois k K] :
    (IntermediateField.fixedField H).fixingSubgroup = H.1 := by
  apply le_antisymm _ ((IntermediateField.le_iff_le H.toSubgroup
    (IntermediateField.fixedField H.toSubgroup)).mp fun ⦃x⦄ a ↦ a)
  intro σ hσ
  by_contra h
  have nhd : H.carrierᶜ ∈ nhds σ := H.isClosed'.isOpen_compl.mem_nhds h
  rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhd
  rcases nhd with ⟨b,⟨gp,⟨L,hL,eq'⟩,eq⟩,sub⟩
  rw [← eq'] at eq
  have sub : σ • b ⊆ H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
  have := hL.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k L K with
    finiteDimensional := normalClosure.is_finiteDimensional k L K
    isGalois := IsGalois.normalClosure k L K }
  have compl : σ • L'.1.fixingSubgroup.carrier ⊆ H.carrierᶜ :=
    fun ⦃a⦄ d ↦ sub ((Set.set_smul_subset_set_smul_iff.mpr <| eq ▸ (fun σ h =>
    (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mpr fun y hy => (mem_fixingSubgroup_iff (K ≃ₐ[k] K)).mp
    h y (IntermediateField.le_normalClosure L hy))) d)
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

/-- The Galois correspondence from intermediate fields to ClosedSubgroup. -/
def IntermediateFieldEquivClosedSubgroup [IsGalois k K] :
    IntermediateField k K ≃o (ClosedSubgroup (K ≃ₐ[k] K))ᵒᵈ where
  toFun := fun L =>
    { L.fixingSubgroup with
      isClosed' := fixingSubgroup_isClosed L }
  invFun := fun H => IntermediateField.fixedField H.1
  left_inv := fun L => fixedField_fixingSubgroup L
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse]
    intro H
    simp_rw [fixingSubgroup_fixedField H]
    rfl
  map_rel_iff' := by
    intro L₁ L₂
    show L₁.fixingSubgroup ≥ L₂.fixingSubgroup ↔ L₁ ≤ L₂
    rw [← fixedField_fixingSubgroup L₂, IntermediateField.le_iff_le, fixedField_fixingSubgroup L₂]

/-- The Galois correspondence as a `GaloisInsertion` -/
def GaloisInsertionIntermediateFieldSubgroup [IsGalois k K] :
    GaloisInsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) ↦
      (⟨E.fixingSubgroup, fixingSubgroup_isClosed E⟩ : ClosedSubgroup (K ≃ₐ[k] K)))
      ((fun (H : ClosedSubgroup (K ≃ₐ[k] K)) ↦ IntermediateField.fixedField H) ∘
        OrderDual.toDual) where
  choice E _ := ⟨E.fixingSubgroup, fixingSubgroup_isClosed E⟩
  gc E H := (IntermediateField.le_iff_le H.1 E).symm
  le_l_u H := by
    simp only [Function.comp_apply, fixingSubgroup_fixedField]
    rfl
  choice_eq _ _ := rfl

/-- The Galois correspondence as a `GaloisCoinsertion` -/
def GaloisCoinsertionIntermediateFieldSubgroup [IsGalois k K] :
    GaloisCoinsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) ↦
      (⟨E.fixingSubgroup, fixingSubgroup_isClosed E⟩ : ClosedSubgroup (K ≃ₐ[k] K)))
      ((fun (H : ClosedSubgroup (K ≃ₐ[k] K)) ↦ IntermediateField.fixedField H) ∘
        OrderDual.toDual) where
  choice H _ := IntermediateField.fixedField H.1
  gc E H := (IntermediateField.le_iff_le H.1 E).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl

private lemma IntermediateField.finiteDimensional_of_le {M N : IntermediateField k K}
    (le : M ≤ N) [FiniteDimensional k N] : FiniteDimensional k M := by
  let i : M →ₐ[k] N := {
    toFun := fun x => ⟨x.1, le x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }
  apply FiniteDimensional.of_injective (AlgHom.toLinearMap i)
  intro _ _ h
  apply_fun Subtype.val at h
  exact Subtype.val_injective h

theorem open_iff_finite (L : IntermediateField k K) [IsGalois k K] :
    IsOpen (IntermediateFieldEquivClosedSubgroup L).carrier ↔
    (FiniteDimensional k L) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : (IntermediateFieldEquivClosedSubgroup.toFun L).carrier ∈ nhds 1 :=
      IsOpen.mem_nhds h (congrFun rfl)
    rw [GroupFilterBasis.nhds_one_eq] at this
    rcases this with ⟨S, ⟨gp, ⟨M, hM, eq'⟩, eq⟩, sub⟩
    simp only [← eq'] at eq
    rw [← eq] at sub
    have := hM.out
    let L' : FiniteGaloisIntermediateField k K := {
      normalClosure k M K with
      finiteDimensional := normalClosure.is_finiteDimensional k M K
      isGalois := IsGalois.normalClosure k M K }
    have : L'.1.fixingSubgroup.carrier ⊆ (IntermediateFieldEquivClosedSubgroup.1.1 L).carrier := by
      have : M ≤ L'.1 := IntermediateField.le_normalClosure M
      rw [←  fixedField_fixingSubgroup L'.1, IntermediateField.le_iff_le] at this
      exact fun _ a ↦ sub (this a)
    simp only [IntermediateFieldEquivClosedSubgroup, Equiv.toFun_as_coe, Equiv.coe_fn_mk] at this
    apply IntermediateField.finiteDimensional_of_le (N := L'.1)
    rw [← fixedField_fixingSubgroup L'.1, IntermediateField.le_iff_le]
    exact this
  · exact IntermediateField.fixingSubgroup_isOpen L

theorem normal_iff_isGalois (L : IntermediateField k K) [IsGalois k K] :
    Subgroup.Normal (IntermediateFieldEquivClosedSubgroup L).1 ↔
    IsGalois k L := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let f : L → IntermediateField k K := fun x => IntermediateField.lift <|
      IntermediateField.fixedField <| Subgroup.map (restrictNormalHom
      (adjoin k {x.1})) L.fixingSubgroup
    have h' (x : K) : (Subgroup.map (restrictNormalHom
      (adjoin k {x})) L.fixingSubgroup).Normal := by
      set f := restrictNormalHom (F := k) (K₁ := K) (adjoin k {x})
      simp only [IntermediateFieldEquivClosedSubgroup, Equiv.toFun_as_coe, Equiv.coe_fn_mk] at h
      exact Subgroup.Normal.map h f (restrictNormalHom_surjective K)
    have n' (l : L) : IsGalois k (IntermediateField.fixedField <| Subgroup.map
      (restrictNormalHom (adjoin k {l.1})) L.fixingSubgroup) := by
      letI := IsGalois.of_fixedField_normal_subgroup (Subgroup.map (restrictNormalHom
        (adjoin k {l.1})) L.fixingSubgroup)
      set cH := (Subgroup.map (restrictNormalHom (adjoin k {l.1})) L.fixingSubgroup)
      exact IsGalois.of_algEquiv <| IntermediateField.liftAlgEquiv (IntermediateField.fixedField cH)
    have n : Normal k ↥(⨆ (l : L), f l):= IntermediateField.normal_iSup k K f
    have : (⨆ (l : L), f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        simp only [f, ← restrict_fixedField L.fixingSubgroup (adjoin k {l.1}),
          fixedField_fixingSubgroup L]
        exact inf_le_left
      · intro l hl
        apply le_iSup f ⟨l,hl⟩
        dsimp only [f]
        rw [← restrict_fixedField L.fixingSubgroup (adjoin k {l}), fixedField_fixingSubgroup L]
        simp only [IntermediateField.mem_inf, hl, true_and]
        exact adjoin_simple_le_iff.mp fun _ a ↦ a
    rw [this] at n
    letI : Algebra.IsSeparable k L := Algebra.isSeparable_tower_bot_of_isSeparable k L K
    apply IsGalois.mk
  · simp only [IntermediateFieldEquivClosedSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← L.restrictNormalHom_ker]
    exact MonoidHom.normal_ker (restrictNormalHom L)

end InfiniteGalois
