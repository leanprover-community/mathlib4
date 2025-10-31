/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'`
* Burnside's lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`,

as well as their analogues for additive groups.
-/

assert_not_exists Cardinal

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

/-- A typeclass for when an `AddAction β α` descends to the quotient `α ⧸ H`. -/
class _root_.AddAction.QuotientAction {α : Type u} (β : Type v) [AddGroup α] [AddMonoid β]
  [AddAction β α] (H : AddSubgroup α) : Prop where
  /-- The action fulfils a normality condition on summands that lie in `H`.
    This ensures that the action descends to an action on the quotient `α ⧸ H`. -/
  inv_mul_mem : ∀ (b : β) {a a' : α}, -a + a' ∈ H → -(b +ᵥ a) + (b +ᵥ a') ∈ H

attribute [to_additive] MulAction.QuotientAction

@[to_additive]
instance left_quotientAction : QuotientAction α H :=
  ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive]
instance right_quotientAction : QuotientAction (normalizer H).op H :=
  ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive]
instance right_quotientAction' [hH : H.Normal] : QuotientAction αᵐᵒᵖ H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩

@[to_additive]
instance quotient [QuotientAction β H] : MulAction β (α ⧸ H) where
  smul b :=
    Quotient.map' (b • ·) fun _ _ h =>
      leftRel_apply.mpr <| QuotientAction.inv_mul_mem b <| leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul β a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)

variable {β}

@[to_additive (attr := simp)]
theorem Quotient.smul_mk [QuotientAction β H] (b : β) (a : α) :
    (b • QuotientGroup.mk a : α ⧸ H) = QuotientGroup.mk (b • a) :=
  rfl

@[to_additive (attr := simp)]
theorem Quotient.smul_coe [QuotientAction β H] (b : β) (a : α) :
    b • (a : α ⧸ H) = (↑(b • a) : α ⧸ H) :=
  rfl

@[to_additive (attr := simp)]
theorem Quotient.mk_smul_out [QuotientAction β H] (b : β) (q : α ⧸ H) :
    QuotientGroup.mk (b • q.out) = b • q := by rw [← Quotient.smul_mk, QuotientGroup.out_eq']

@[to_additive]
theorem Quotient.coe_smul_out [QuotientAction β H] (b : β) (q : α ⧸ H) : ↑(b • q.out) = b • q := by
  simp

theorem _root_.QuotientGroup.out_conj_pow_minimalPeriod_mem (a : α) (q : α ⧸ H) :
    q.out⁻¹ * a ^ Function.minimalPeriod (a • ·) q * q.out ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, Quotient.mk_smul_out,
    eq_comm, pow_smul_eq_iff_minimalPeriod_dvd]

end QuotientAction

open QuotientGroup

/-- The canonical map to the left cosets. -/
def _root_.MulActionHom.toQuotient (H : Subgroup α) : α →[α] α ⧸ H where
  toFun := (↑); map_smul' := Quotient.smul_coe H

@[simp]
theorem _root_.MulActionHom.toQuotient_apply (H : Subgroup α) (g : α) :
    MulActionHom.toQuotient H g = g :=
  rfl

@[to_additive]
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup α) : MulAction I (α ⧸ H) :=
  MulAction.compHom (α ⧸ H) (Subgroup.subtype I)

variable (α)
variable [MulAction α β] (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive /-- The canonical map from the quotient of the stabilizer to the set. -/]
def ofQuotientStabilizer (g : α ⧸ MulAction.stabilizer α x) : β :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

@[to_additive (attr := simp)]
theorem ofQuotientStabilizer_mk (g : α) : ofQuotientStabilizer α x (QuotientGroup.mk g) = g • x :=
  rfl

@[to_additive]
theorem ofQuotientStabilizer_mem_orbit (g) : ofQuotientStabilizer α x g ∈ orbit α x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩

@[to_additive]
theorem ofQuotientStabilizer_smul (g : α) (g' : α ⧸ MulAction.stabilizer α x) :
    ofQuotientStabilizer α x (g • g') = g • ofQuotientStabilizer α x g' :=
  Quotient.inductionOn' g' fun _ => mul_smul _ _ _

@[to_additive]
theorem injective_ofQuotientStabilizer : Function.Injective (ofQuotientStabilizer α x) :=
  fun y₁ y₂ =>
  Quotient.inductionOn₂' y₁ y₂ fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
    Quotient.sound' <| by
      rw [leftRel_apply]
      change (g₁⁻¹ * g₂) • x = x
      rw [mul_smul, ← H, inv_smul_smul]

/-- **Orbit-stabilizer theorem**. -/
@[to_additive /-- Orbit-stabilizer theorem. -/]
noncomputable def orbitEquivQuotientStabilizer (b : β) : orbit α b ≃ α ⧸ stabilizer α b :=
  Equiv.symm <|
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer α b g, ofQuotientStabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer α b (by convert congr_arg Subtype.val hxy),
        fun ⟨_, ⟨g, hgb⟩⟩ => ⟨g, Subtype.ext hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.orbitProdStabilizerEquivAddGroup /-- Orbit-stabilizer theorem. -/]
noncomputable def orbitProdStabilizerEquivGroup (b : β) : orbit α b × stabilizer α b ≃ α :=
  (Equiv.prodCongr (orbitEquivQuotientStabilizer α _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm

/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup
/-- Orbit-stabilizer theorem. -/]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α] [Fintype <| orbit α b]
    [Fintype <| stabilizer α b] :
    Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbitProdStabilizerEquivGroup α b)]

@[to_additive (attr := simp)]
theorem orbitEquivQuotientStabilizer_symm_apply (b : β) (a : α) :
    ((orbitEquivQuotientStabilizer α b).symm a : β) = a • b :=
  rfl

@[to_additive (attr := simp)]
theorem stabilizer_quotient {G} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext
  simp [QuotientGroup.eq]

variable (β)

local notation "Ω" => Quotient <| orbitRel α β

/-- **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
under this action (that is, each element of the quotient of `X` by the relation `orbitRel G X`) to
an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `Quotient.out`, so we
provide `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a special case. -/
@[to_additive
      /-- **Class formula** : given `G` an additive group acting on `X` and `φ` a function
      mapping each orbit of `X` under this action (that is, each element of the quotient of `X` by
      the relation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable)
      bijection between `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most
      cases you'll want `φ` to be `Quotient.out`, so we provide
      `AddAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a special case. -/]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω → β}
    (hφ : LeftInverse Quotient.mk'' φ) : β ≃ Σ ω : Ω, α ⧸ stabilizer α (φ ω) :=
  calc
    β ≃ Σ ω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' α β
    _ ≃ Σ ω : Ω, α ⧸ stabilizer α (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
        (Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans <|
          orbitEquivQuotientStabilizer α (φ ω)

/-- **Class formula**. This is a special case of
`MulAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out`. -/
@[to_additive
      /-- **Class formula**. This is a special case of
      `AddAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out`. -/]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer : β ≃ Σ ω : Ω, α ⧸ stabilizer α ω.out :=
  selfEquivSigmaOrbitsQuotientStabilizer' α β Quotient.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
`X/G` denotes the quotient of `X` by the relation `orbitRel G X`. -/
@[to_additive AddAction.sigmaFixedByEquivOrbitsProdAddGroup
      /-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
      `{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group
      acting on `X` and `X/G`denotes the quotient of `X` by the relation `orbitRel G X`. -/]
noncomputable def sigmaFixedByEquivOrbitsProdGroup : (Σ a : α, fixedBy β a) ≃ Ω × α :=
  calc
    (Σ a : α, fixedBy β a) ≃ { ab : α × β // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : β × α // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm α β).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σ b : β, stabilizer α b :=
      Equiv.subtypeProdEquivSigmaSubtype fun (b : β) a => a ∈ stabilizer α b
    _ ≃ Σ ωb : Σ ω : Ω, orbit α ω.out, stabilizer α (ωb.2 : β) :=
      (selfEquivSigmaOrbits α β).sigmaCongrLeft'
    _ ≃ Σ ω : Ω, Σ b : orbit α ω.out, stabilizer α (b : β) :=
      Equiv.sigmaAssoc fun (ω : Ω) (b : orbit α ω.out) => stabilizer α (b : β)
    _ ≃ Σ ω : Ω, Σ _ : orbit α ω.out, stabilizer α ω.out :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun ⟨_, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σ ω : Ω, orbit α ω.out × stabilizer α ω.out :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ Σ _ : Ω, α := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω.out
    _ ≃ Ω × α := Equiv.sigmaEquivProd Ω α

/-- **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
elements fixed by each `g ∈ G` is the number of orbits. -/
@[to_additive AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
      /-- **Burnside's lemma** : given a finite additive group `G` acting on a set `X`,
      the average number of elements fixed by each `g ∈ G` is the number of orbits. -/]
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group [Fintype α] [∀ a : α, Fintype <| fixedBy β a]
    [Fintype Ω] : (∑ a : α, Fintype.card (fixedBy β a)) = Fintype.card Ω * Fintype.card α := by
  rw [← Fintype.card_prod, ← Fintype.card_sigma,
    Fintype.card_congr (sigmaFixedByEquivOrbitsProdGroup α β)]

@[to_additive]
instance isPretransitive_quotient (G) [Group G] (H : Subgroup G) : IsPretransitive G (G ⧸ H) where
  exists_smul_eq := by
    { rintro ⟨x⟩ ⟨y⟩
      refine ⟨y * x⁻¹, QuotientGroup.eq.mpr ?_⟩
      simp only [smul_eq_mul, H.one_mem, inv_mul_cancel, inv_mul_cancel_right]}

variable {α}

@[to_additive]
instance finite_quotient_of_pretransitive_of_finite_quotient [IsPretransitive α β] {H : Subgroup α}
    [Finite (α ⧸ H)] : Finite <| orbitRel.Quotient H β := by
  rcases isEmpty_or_nonempty β with he | ⟨⟨b⟩⟩
  · exact Quotient.finite _
  · have h' : Finite (Quotient (rightRel H)) :=
      Finite.of_equiv _ (quotientRightRelEquivQuotientLeftRel _).symm
    let f : Quotient (rightRel H) → orbitRel.Quotient H β :=
      fun a ↦ Quotient.liftOn' a (fun g ↦ ⟦g • b⟧) fun g₁ g₂ r ↦ by
        replace r := Setoid.symm' _ r
        rw [rightRel_eq] at r
        simp only [Quotient.eq, orbitRel_apply, mem_orbit_iff]
        exact ⟨⟨g₁ * g₂⁻¹, r⟩, by simp [mul_smul]⟩
    exact Finite.of_surjective f ((Quotient.surjective_liftOn' _).2
      (Quotient.mk''_surjective.comp (MulAction.surjective_smul _ _)))

variable {β} in
/-- A bijection between the quotient of the action of a subgroup `H` on an orbit, and a
corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/
@[to_additive /-- A bijection between the quotient of the action of an additive subgroup `H` on an
orbit, and a corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/]
noncomputable def equivSubgroupOrbitsSetoidComap (H : Subgroup α) (ω : Ω) :
    orbitRel.Quotient H (orbitRel.Quotient.orbit ω) ≃
      Quotient ((orbitRel H β).comap (Subtype.val : Quotient.mk (orbitRel α β) ⁻¹' {ω} → β)) where
  toFun := fun q ↦ q.liftOn' (fun x ↦ ⟦⟨↑x, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx := x.property
    rwa [orbitRel.Quotient.mem_orbit] at hx⟩⟧) fun a b h ↦ by
      simp only [← Quotient.eq, orbitRel.Quotient.subgroup_quotient_eq_iff] at h
      simp only [Quotient.eq] at h ⊢
      exact h
  invFun := fun q ↦ q.liftOn' (fun x ↦ ⟦⟨↑x, by
    have hx := x.property
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rwa [orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk]⟩⟧) fun a b h ↦ by
      rw [Setoid.comap_rel, ← Quotient.eq'', @Quotient.mk''_eq_mk] at h
      simp only [orbitRel.Quotient.subgroup_quotient_eq_iff]
      exact h
  left_inv := by
    simp only [LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl
  right_inv := by
    simp only [Function.RightInverse, LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl

/-- A bijection between the orbits under the action of a subgroup `H` on `β`, and the orbits
under the action of `H` on each orbit under the action of `G`. -/
@[to_additive /-- A bijection between the orbits under the action of an additive subgroup `H` on
`β`, and the orbits under the action of `H` on each orbit under the action of `G`. -/]
noncomputable def equivSubgroupOrbits (H : Subgroup α) :
    orbitRel.Quotient H β ≃ Σ ω : Ω, orbitRel.Quotient H (orbitRel.Quotient.orbit ω) :=
  (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm.trans
    (Equiv.sigmaCongrRight fun ω ↦ (equivSubgroupOrbitsSetoidComap H ω).symm)

variable {β}

@[to_additive]
instance finite_quotient_of_finite_quotient_of_finite_quotient {H : Subgroup α}
    [Finite (orbitRel.Quotient α β)] [Finite (α ⧸ H)] :
    Finite <| orbitRel.Quotient H β := by
  rw [(equivSubgroupOrbits β H).finite_iff]
  infer_instance

/-- Given a group acting freely and transitively, an equivalence between the orbits under the
action of a subgroup and the quotient group. -/
@[to_additive /-- Given an additive group acting freely and transitively, an equivalence between the
orbits under the action of an additive subgroup and the quotient group. -/]
noncomputable def equivSubgroupOrbitsQuotientGroup [IsPretransitive α β]
    (free : ∀ y : β, MulAction.stabilizer α y = ⊥) (H : Subgroup α) :
    orbitRel.Quotient H β ≃ α ⧸ H where
  toFun := fun q ↦ q.liftOn' (fun y ↦ (exists_smul_eq α y x).choose) (by
    intro y₁ y₂ h
    rw [orbitRel_apply] at h
    rw [Quotient.eq'', leftRel_eq]
    dsimp only
    rcases h with ⟨g, rfl⟩
    dsimp only
    suffices (exists_smul_eq α (g • y₂) x).choose = (exists_smul_eq α y₂ x).choose * g⁻¹ by
      simp [this]
    rw [← inv_mul_eq_one, ← Subgroup.mem_bot, ← free ((g : α) • y₂)]
    simp only [mem_stabilizer_iff, smul_smul, mul_assoc, InvMemClass.coe_inv, inv_mul_cancel,
               mul_one]
    rw [← smul_smul, (exists_smul_eq α y₂ x).choose_spec, inv_smul_eq_iff,
        (exists_smul_eq α ((g : α) • y₂) x).choose_spec])
  invFun := fun q ↦ q.liftOn' (fun g ↦ ⟦g⁻¹ • x⟧) (by
    intro g₁ g₂ h
    rw [leftRel_eq] at h
    simp only
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', orbitRel_apply]
    exact ⟨⟨_, h⟩, by simp [mul_smul]⟩)
  left_inv := fun y ↦ by
    cases y using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', orbitRel_apply]
    convert mem_orbit_self _
    rw [inv_smul_eq_iff, (exists_smul_eq α _ x).choose_spec]
  right_inv := fun g ↦ by
    cases g using Quotient.inductionOn' with | _ g
    simp only [Quotient.liftOn'_mk'', QuotientGroup.mk]
    rw [Quotient.eq'', leftRel_eq]
    simp only
    convert one_mem H
    · rw [inv_mul_eq_one, eq_comm, ← inv_mul_eq_one, ← Subgroup.mem_bot, ← free (g⁻¹ • x),
        mem_stabilizer_iff, mul_smul, (exists_smul_eq α (g⁻¹ • x) x).choose_spec]

/-- If `α` acts on `β` with trivial stabilizers, `β` is equivalent
to the product of the quotient of `β` by `α` and `α`.
See `MulAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/
@[to_additive selfEquivOrbitsQuotientProd' /-- If `α` acts freely on `β`, `β` is equivalent
to the product of the quotient of `β` by `α` and `α`.
See `AddAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/]
noncomputable def selfEquivOrbitsQuotientProd'
    {φ : Quotient (MulAction.orbitRel α β) → β} (hφ : Function.LeftInverse Quotient.mk'' φ)
    (h : ∀ b : β, MulAction.stabilizer α b = ⊥) :
    β ≃ Quotient (MulAction.orbitRel α β) × α :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' α β hφ).trans <|
    (Equiv.sigmaCongrRight <| fun _ ↦
      (Subgroup.quotientEquivOfEq (h _)).trans (QuotientGroup.quotientEquivSelf α)).trans <|
    Equiv.sigmaEquivProd _ _

/-- If `α` acts freely on `β`, `β` is equivalent to the product of the quotient of `β` by `α` and
`α`. -/
@[to_additive selfEquivOrbitsQuotientProd
  /-- If `α` acts freely on `β`, `β` is equivalent to the product of the quotient of `β` by
`α` and `α`. -/]
noncomputable def selfEquivOrbitsQuotientProd (h : ∀ b : β, MulAction.stabilizer α b = ⊥) :
    β ≃ Quotient (MulAction.orbitRel α β) × α :=
  MulAction.selfEquivOrbitsQuotientProd' Quotient.out_eq' h

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

theorem quotientCentralizerEmbedding_apply (g : G) (x : G) :
    quotientCentralizerEmbedding g x = ⟨⁅x, g⁆, x, g, rfl⟩ :=
  rfl

/-- If `G` is generated by `S`, then the quotient by the center embeds into `S`-indexed sequences
of commutators. -/
noncomputable def quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) :
    G ⧸ center G ↪ S → commutatorSet G :=
  (quotientEquivOfEq (center_eq_infi' S hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))

theorem quotientCenterEmbedding_apply {S : Set G} (hS : closure S = ⊤) (g : G) (s : S) :
    quotientCenterEmbedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩ :=
  rfl

end Subgroup
