/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Dynamics.PeriodicPts
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Hom

#align_import group_theory.group_action.quotient from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `card_eq_sum_card_group_div_card_stabilizer'`
* Burnside's lemma `sum_card_fixedBy_eq_card_orbits_mul_card_group`
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

namespace MulAction

variable [Group α]

section QuotientAction

open Subgroup MulOpposite QuotientGroup

variable (β) [Monoid β] [MulAction β α] (H : Subgroup α)

/-- A typeclass for when a `MulAction β α` descends to the quotient `α ⧸ H`. -/
class QuotientAction : Prop where
  /-- The action fulfils a normality condition on products that lie in `H`.
    This ensures that the action descends to an action on the quotient `α ⧸ H`. -/
  inv_mul_mem : ∀ (b : β) {a a' : α}, a⁻¹ * a' ∈ H → (b • a)⁻¹ * b • a' ∈ H
#align mul_action.quotient_action MulAction.QuotientAction

/-- A typeclass for when an `AddAction β α` descends to the quotient `α ⧸ H`. -/
class _root_.AddAction.QuotientAction {α : Type u} (β : Type v) [AddGroup α] [AddMonoid β]
  [AddAction β α] (H : AddSubgroup α) : Prop where
  /-- The action fulfils a normality condition on summands that lie in `H`.
    This ensures that the action descends to an action on the quotient `α ⧸ H`. -/
  inv_mul_mem : ∀ (b : β) {a a' : α}, -a + a' ∈ H → -(b +ᵥ a) + (b +ᵥ a') ∈ H
#align add_action.quotient_action AddAction.QuotientAction

attribute [to_additive] MulAction.QuotientAction

@[to_additive]
instance left_quotientAction : QuotientAction α H :=
  ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩
#align mul_action.left_quotient_action MulAction.left_quotientAction
#align add_action.left_quotient_action AddAction.left_quotientAction

@[to_additive]
instance right_quotientAction : QuotientAction (normalizer H).op H :=
  ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩
#align mul_action.right_quotient_action MulAction.right_quotientAction
#align add_action.right_quotient_action AddAction.right_quotientAction

@[to_additive]
instance right_quotientAction' [hH : H.Normal] : QuotientAction αᵐᵒᵖ H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩
#align mul_action.right_quotient_action' MulAction.right_quotientAction'
#align add_action.right_quotient_action' AddAction.right_quotientAction'

@[to_additive]
instance quotient [QuotientAction β H] : MulAction β (α ⧸ H) where
  smul b :=
    Quotient.map' (b • ·) fun _ _ h =>
      leftRel_apply.mpr <| QuotientAction.inv_mul_mem b <| leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul β a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)
#align mul_action.quotient MulAction.quotient
#align add_action.quotient AddAction.quotient

variable {β}

@[to_additive (attr := simp)]
theorem Quotient.smul_mk [QuotientAction β H] (b : β) (a : α) :
    (b • QuotientGroup.mk a : α ⧸ H) = QuotientGroup.mk (b • a) :=
  rfl
#align mul_action.quotient.smul_mk MulAction.Quotient.smul_mk
#align add_action.quotient.vadd_mk AddAction.Quotient.vadd_mk

@[to_additive (attr := simp)]
theorem Quotient.smul_coe [QuotientAction β H] (b : β) (a : α) :
    b • (a : α ⧸ H) = (↑(b • a) : α ⧸ H) :=
  rfl
#align mul_action.quotient.smul_coe MulAction.Quotient.smul_coe
#align add_action.quotient.vadd_coe AddAction.Quotient.vadd_coe

@[to_additive (attr := simp)]
theorem Quotient.mk_smul_out' [QuotientAction β H] (b : β) (q : α ⧸ H) :
    QuotientGroup.mk (b • q.out') = b • q := by rw [← Quotient.smul_mk, QuotientGroup.out_eq']
#align mul_action.quotient.mk_smul_out' MulAction.Quotient.mk_smul_out'
#align add_action.quotient.mk_vadd_out' AddAction.Quotient.mk_vadd_out'

-- Porting note: removed simp attribute, simp can prove this
@[to_additive]
theorem Quotient.coe_smul_out' [QuotientAction β H] (b : β) (q : α ⧸ H) : ↑(b • q.out') = b • q :=
  Quotient.mk_smul_out' H b q
#align mul_action.quotient.coe_smul_out' MulAction.Quotient.coe_smul_out'
#align add_action.quotient.coe_vadd_out' AddAction.Quotient.coe_vadd_out'

theorem _root_.QuotientGroup.out'_conj_pow_minimalPeriod_mem (a : α) (q : α ⧸ H) :
    q.out'⁻¹ * a ^ Function.minimalPeriod (a • ·) q * q.out' ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq', QuotientGroup.out_eq', ← smul_eq_mul, Quotient.mk_smul_out',
    eq_comm, pow_smul_eq_iff_minimalPeriod_dvd]
#align quotient_group.out'_conj_pow_minimal_period_mem QuotientGroup.out'_conj_pow_minimalPeriod_mem

end QuotientAction

open QuotientGroup

/-- The canonical map to the left cosets. -/
def _root_.MulActionHom.toQuotient (H : Subgroup α) : α →[α] α ⧸ H where
  toFun := (↑); map_smul' := Quotient.smul_coe H
#align mul_action_hom.to_quotient MulActionHom.toQuotient

@[simp]
theorem _root_.MulActionHom.toQuotient_apply (H : Subgroup α) (g : α) :
    MulActionHom.toQuotient H g = g :=
  rfl
#align mul_action_hom.to_quotient_apply MulActionHom.toQuotient_apply

@[to_additive]
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup α) : MulAction I (α ⧸ H) :=
  MulAction.compHom (α ⧸ H) (Subgroup.subtype I)
#align mul_action.mul_left_cosets_comp_subtype_val MulAction.mulLeftCosetsCompSubtypeVal
#align add_action.add_left_cosets_comp_subtype_val AddAction.addLeftCosetsCompSubtypeVal

-- Porting note: Needed to insert [Group α] here
variable (α) [Group α] [MulAction α β] (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive "The canonical map from the quotient of the stabilizer to the set. "]
def ofQuotientStabilizer (g : α ⧸ MulAction.stabilizer α x) : β :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]
#align mul_action.of_quotient_stabilizer MulAction.ofQuotientStabilizer
#align add_action.of_quotient_stabilizer AddAction.ofQuotientStabilizer

@[to_additive (attr := simp)]
theorem ofQuotientStabilizer_mk (g : α) : ofQuotientStabilizer α x (QuotientGroup.mk g) = g • x :=
  rfl
#align mul_action.of_quotient_stabilizer_mk MulAction.ofQuotientStabilizer_mk
#align add_action.of_quotient_stabilizer_mk AddAction.ofQuotientStabilizer_mk

@[to_additive]
theorem ofQuotientStabilizer_mem_orbit (g) : ofQuotientStabilizer α x g ∈ orbit α x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩
#align mul_action.of_quotient_stabilizer_mem_orbit MulAction.ofQuotientStabilizer_mem_orbit
#align add_action.of_quotient_stabilizer_mem_orbit AddAction.ofQuotientStabilizer_mem_orbit

@[to_additive]
theorem ofQuotientStabilizer_smul (g : α) (g' : α ⧸ MulAction.stabilizer α x) :
    ofQuotientStabilizer α x (g • g') = g • ofQuotientStabilizer α x g' :=
  Quotient.inductionOn' g' fun _ => mul_smul _ _ _
#align mul_action.of_quotient_stabilizer_smul MulAction.ofQuotientStabilizer_smul
#align add_action.of_quotient_stabilizer_vadd AddAction.ofQuotientStabilizer_vadd

@[to_additive]
theorem injective_ofQuotientStabilizer : Function.Injective (ofQuotientStabilizer α x) :=
  fun y₁ y₂ =>
  Quotient.inductionOn₂' y₁ y₂ fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
    Quotient.sound' <| by
      rw [leftRel_apply]
      show (g₁⁻¹ * g₂) • x = x
      rw [mul_smul, ← H, inv_smul_smul]
#align mul_action.injective_of_quotient_stabilizer MulAction.injective_ofQuotientStabilizer
#align add_action.injective_of_quotient_stabilizer AddAction.injective_ofQuotientStabilizer

/-- **Orbit-stabilizer theorem**. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitEquivQuotientStabilizer (b : β) : orbit α b ≃ α ⧸ stabilizer α b :=
  Equiv.symm <|
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer α b g, ofQuotientStabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer α b (by convert congr_arg Subtype.val hxy),
        fun ⟨b, ⟨g, hgb⟩⟩ => ⟨g, Subtype.eq hgb⟩⟩
#align mul_action.orbit_equiv_quotient_stabilizer MulAction.orbitEquivQuotientStabilizer
#align add_action.orbit_equiv_quotient_stabilizer AddAction.orbitEquivQuotientStabilizer

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitProdStabilizerEquivGroup (b : β) : orbit α b × stabilizer α b ≃ α :=
  (Equiv.prodCongr (orbitEquivQuotientStabilizer α _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm
#align mul_action.orbit_prod_stabilizer_equiv_group MulAction.orbitProdStabilizerEquivGroup
#align add_action.orbit_sum_stabilizer_equiv_add_group AddAction.orbitSumStabilizerEquivAddGroup

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α] [Fintype <| orbit α b]
    [Fintype <| stabilizer α b] :
    Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbitProdStabilizerEquivGroup α b)]
#align mul_action.card_orbit_mul_card_stabilizer_eq_card_group MulAction.card_orbit_mul_card_stabilizer_eq_card_group
#align add_action.card_orbit_add_card_stabilizer_eq_card_add_group AddAction.card_orbit_add_card_stabilizer_eq_card_addGroup

@[to_additive (attr := simp)]
theorem orbitEquivQuotientStabilizer_symm_apply (b : β) (a : α) :
    ((orbitEquivQuotientStabilizer α b).symm a : β) = a • b :=
  rfl
#align mul_action.orbit_equiv_quotient_stabilizer_symm_apply MulAction.orbitEquivQuotientStabilizer_symm_apply
#align add_action.orbit_equiv_quotient_stabilizer_symm_apply AddAction.orbitEquivQuotientStabilizer_symm_apply

@[to_additive (attr := simp)]
theorem stabilizer_quotient {G} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext
  simp [QuotientGroup.eq]
#align mul_action.stabilizer_quotient MulAction.stabilizer_quotient
#align add_action.stabilizer_quotient AddAction.stabilizer_quotient

variable (β)

local notation "Ω" => Quotient <| orbitRel α β

/-- **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
under this action (that is, each element of the quotient of `X` by the relation `orbitRel G X`) to
an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `Quotient.out'`, so we
provide `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a special case. -/
@[to_additive
      "**Class formula** : given `G` an additive group acting on `X` and `φ` a function
      mapping each orbit of `X` under this action (that is, each element of the quotient of `X` by
      the relation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable)
      bijection between `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most
      cases you'll want `φ` to be `Quotient.out'`, so we provide
      `AddAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a special case. "]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω → β}
    (hφ : LeftInverse Quotient.mk'' φ) : β ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) :=
  calc
    β ≃ Σω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' α β
    _ ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
        (Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans <|
          orbitEquivQuotientStabilizer α (φ ω)
#align mul_action.self_equiv_sigma_orbits_quotient_stabilizer' MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
#align add_action.self_equiv_sigma_orbits_quotient_stabilizer' AddAction.selfEquivSigmaOrbitsQuotientStabilizer'

/-- **Class formula** for a finite group acting on a finite type. See
`MulAction.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`Quotient.out'`. -/
@[to_additive
      "**Class formula** for a finite group acting on a finite type. See
      `AddAction.card_eq_sum_card_addGroup_div_card_stabilizer` for a specialized version using
      `Quotient.out'`."]
theorem card_eq_sum_card_group_div_card_stabilizer' [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] {φ : Ω → β} (hφ : LeftInverse Quotient.mk'' φ) :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) := by
  classical
    have : ∀ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) =
        Fintype.card (α ⧸ stabilizer α (φ ω)) := by
      intro ω
      rw [Fintype.card_congr (@Subgroup.groupEquivQuotientProdSubgroup α _ (stabilizer α <| φ ω)),
        Fintype.card_prod, Nat.mul_div_cancel]
      exact Fintype.card_pos_iff.mpr (by infer_instance)
    simp_rw [this, ← Fintype.card_sigma,
      Fintype.card_congr (selfEquivSigmaOrbitsQuotientStabilizer' α β hφ)]
#align mul_action.card_eq_sum_card_group_div_card_stabilizer' MulAction.card_eq_sum_card_group_div_card_stabilizer'
#align add_action.card_eq_sum_card_add_group_sub_card_stabilizer' AddAction.card_eq_sum_card_addGroup_sub_card_stabilizer'

/-- **Class formula**. This is a special case of
`MulAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out'`. -/
@[to_additive
      "**Class formula**. This is a special case of
      `AddAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out'`. "]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer : β ≃ Σω : Ω, α ⧸ stabilizer α ω.out' :=
  selfEquivSigmaOrbitsQuotientStabilizer' α β Quotient.out_eq'
#align mul_action.self_equiv_sigma_orbits_quotient_stabilizer MulAction.selfEquivSigmaOrbitsQuotientStabilizer
#align add_action.self_equiv_sigma_orbits_quotient_stabilizer AddAction.selfEquivSigmaOrbitsQuotientStabilizer

/-- **Class formula** for a finite group acting on a finite type. -/
@[to_additive "**Class formula** for a finite group acting on a finite type."]
theorem card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α ω.out') :=
  card_eq_sum_card_group_div_card_stabilizer' α β Quotient.out_eq'
#align mul_action.card_eq_sum_card_group_div_card_stabilizer MulAction.card_eq_sum_card_group_div_card_stabilizer
#align add_action.card_eq_sum_card_add_group_sub_card_stabilizer AddAction.card_eq_sum_card_addGroup_sub_card_stabilizer

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
`X/G` denotes the quotient of `X` by the relation `orbitRel G X`. -/
@[to_additive
      "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
      `{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group
      acting on `X` and `X/G`denotes the quotient of `X` by the relation `orbitRel G X`. "]
noncomputable def sigmaFixedByEquivOrbitsProdGroup : (Σa : α, fixedBy β a) ≃ Ω × α :=
  calc
    (Σa : α, fixedBy β a) ≃ { ab : α × β // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : β × α // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm α β).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σb : β, stabilizer α b :=
      Equiv.subtypeProdEquivSigmaSubtype fun (b : β) a => a ∈ stabilizer α b
    _ ≃ Σωb : Σω : Ω, orbit α ω.out', stabilizer α (ωb.2 : β) :=
      (selfEquivSigmaOrbits α β).sigmaCongrLeft'
    _ ≃ Σω : Ω, Σb : orbit α ω.out', stabilizer α (b : β) :=
      Equiv.sigmaAssoc fun (ω : Ω) (b : orbit α ω.out') => stabilizer α (b : β)
    _ ≃ Σω : Ω, Σ _ : orbit α ω.out', stabilizer α ω.out' :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun ⟨_, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σω : Ω, orbit α ω.out' × stabilizer α ω.out' :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ Σ _ : Ω, α := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω.out'
    _ ≃ Ω × α := Equiv.sigmaEquivProd Ω α
#align mul_action.sigma_fixed_by_equiv_orbits_prod_group MulAction.sigmaFixedByEquivOrbitsProdGroup
#align add_action.sigma_fixed_by_equiv_orbits_sum_add_group AddAction.sigmaFixedByEquivOrbitsSumAddGroup

/-- **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
elements fixed by each `g ∈ G` is the number of orbits. -/
@[to_additive
      "**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,
      the average number of elements fixed by each `g ∈ G` is the number of orbits. "]
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group [Fintype α] [∀ a : α, Fintype <| fixedBy β a]
    [Fintype Ω] : (∑ a : α, Fintype.card (fixedBy β a)) = Fintype.card Ω * Fintype.card α := by
  rw [← Fintype.card_prod, ← Fintype.card_sigma,
    Fintype.card_congr (sigmaFixedByEquivOrbitsProdGroup α β)]
#align mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
#align add_action.sum_card_fixed_by_eq_card_orbits_add_card_add_group AddAction.sum_card_fixedBy_eq_card_orbits_add_card_addGroup

@[to_additive]
instance isPretransitive_quotient (G) [Group G] (H : Subgroup G) : IsPretransitive G (G ⧸ H) where
  exists_smul_eq := by
    { rintro ⟨x⟩ ⟨y⟩
      refine ⟨y * x⁻¹, QuotientGroup.eq.mpr ?_⟩
      simp only [smul_eq_mul, H.one_mem, mul_left_inv, inv_mul_cancel_right]}
#align mul_action.is_pretransitive_quotient MulAction.isPretransitive_quotient
#align add_action.is_pretransitive_quotient AddAction.isPretransitive_quotient

end MulAction

theorem ConjClasses.card_carrier {G : Type*} [Group G] [Fintype G] (g : G)
    [Fintype (ConjClasses.mk g).carrier] [Fintype <| MulAction.stabilizer (ConjAct G) g] :
    Fintype.card (ConjClasses.mk g).carrier =
      Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
  classical
  rw [Fintype.card_congr <| ConjAct.toConjAct (G := G) |>.toEquiv]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g, Nat.mul_div_cancel]
  · simp_rw [ConjAct.orbit_eq_carrier_conjClasses]
  · exact Fintype.card_pos_iff.mpr inferInstance

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

theorem normalCore_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker := by
  apply le_antisymm
  · intro g hg
    apply Equiv.Perm.ext
    refine fun q ↦ QuotientGroup.induction_on q ?_
    refine fun g' => (MulAction.Quotient.smul_mk H g g').trans (QuotientGroup.eq.mpr ?_)
    rw [smul_eq_mul, mul_inv_rev, ← inv_inv g', inv_inv]
    exact H.normalCore.inv_mem hg g'⁻¹
  · refine (Subgroup.normal_le_normalCore.mpr fun g hg => ?_)
    rw [← H.inv_mem_iff, ← mul_one g⁻¹, ← QuotientGroup.eq, ← mul_one g]
    exact (MulAction.Quotient.smul_mk H g 1).symm.trans (Equiv.Perm.ext_iff.mp hg (1 : G))
#align subgroup.normal_core_eq_ker Subgroup.normalCore_eq_ker

open QuotientGroup

/-- Cosets of the centralizer of an element embed into the set of commutators. -/
noncomputable def quotientCentralizerEmbedding (g : G) :
    G ⧸ centralizer (zpowers (g : G)) ↪ commutatorSet G :=
  ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun _ _ => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_iff.mp⟩
#align subgroup.quotient_centralizer_embedding Subgroup.quotientCentralizerEmbedding

theorem quotientCentralizerEmbedding_apply (g : G) (x : G) :
    quotientCentralizerEmbedding g x = ⟨⁅x, g⁆, x, g, rfl⟩ :=
  rfl
#align subgroup.quotient_centralizer_embedding_apply Subgroup.quotientCentralizerEmbedding_apply

/-- If `G` is generated by `S`, then the quotient by the center embeds into `S`-indexed sequences
of commutators. -/
noncomputable def quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) :
    G ⧸ center G ↪ S → commutatorSet G :=
  (quotientEquivOfEq (center_eq_infi' S hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))
#align subgroup.quotient_center_embedding Subgroup.quotientCenterEmbedding

theorem quotientCenterEmbedding_apply {S : Set G} (hS : closure S = ⊤) (g : G) (s : S) :
    quotientCenterEmbedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩ :=
  rfl
#align subgroup.quotient_center_embedding_apply Subgroup.quotientCenterEmbedding_apply

end Subgroup

section conjClasses

open Fintype

theorem card_comm_eq_card_conjClasses_mul_card (G : Type*) [Group G] :
    Nat.card { p : G × G // Commute p.1 p.2 } = Nat.card (ConjClasses G) * Nat.card G := by
  classical
  rcases fintypeOrInfinite G; swap
  · rw [mul_comm, Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_mul]
  simp only [Nat.card_eq_fintype_card]
  -- Porting note: Changed `calc` proof into a `rw` proof.
  rw [card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute), card_sigma,
    sum_equiv ConjAct.toConjAct.toEquiv (fun a ↦ card { b // Commute a b })
      (fun g ↦ card (MulAction.fixedBy G g))
      fun g ↦ card_congr' <| congr_arg _ <| funext fun h ↦ mul_inv_eq_iff_eq_mul.symm.eq,
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  congr 1; apply card_congr'; congr; ext;
  exact (Setoid.comm' _).trans isConj_iff.symm
#align card_comm_eq_card_conj_classes_mul_card card_comm_eq_card_conjClasses_mul_card

end conjClasses
