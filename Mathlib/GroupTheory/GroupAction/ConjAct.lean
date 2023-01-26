/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module group_theory.group_action.conj_act
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Subgroup.Zpowers
import Mathbin.Algebra.GroupRingAction.Basic

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `mul_aut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `conj_act G` is introduced for a group `G`. The group `conj_act G` acts on `G`
by conjugation. The group `conj_act G` also acts on any normal subgroup of `G` by conjugation.

As a generalization, this also allows:
* `conj_act Mˣ` to act on `M`, when `M` is a `monoid`
* `conj_act G₀` to act on `G₀`, when `G₀` is a `group_with_zero`

## Implementation Notes

The scalar action in defined in this file can also be written using `mul_aut.conj g • h`. This
has the advantage of not using the type alias `conj_act`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`mul_aut.conj g • h` describes an action of `mul_aut G` on `G`, and not an action of `G`.

-/


variable (α M G G₀ R K : Type _)

/-- A type alias for a group `G`. `conj_act G` acts on `G` by conjugation -/
def ConjAct : Type _ :=
  G
#align conj_act ConjAct

namespace ConjAct

open MulAction Subgroup

variable {M G G₀ R K}

instance : ∀ [Group G], Group (ConjAct G) :=
  id

instance : ∀ [DivInvMonoid G], DivInvMonoid (ConjAct G) :=
  id

instance : ∀ [GroupWithZero G], GroupWithZero (ConjAct G) :=
  id

instance : ∀ [Fintype G], Fintype (ConjAct G) :=
  id

@[simp]
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl
#align conj_act.card ConjAct.card

section DivInvMonoid

variable [DivInvMonoid G]

instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/-- Reinterpret `g : conj_act G` as an element of `G`. -/
def ofConjAct : ConjAct G ≃* G :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
#align conj_act.of_conj_act ConjAct.ofConjAct

/-- Reinterpret `g : G` as an element of `conj_act G`. -/
def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm
#align conj_act.to_conj_act ConjAct.toConjAct

/-- A recursor for `conj_act`, for use as `induction x using conj_act.rec` when `x : conj_act G`. -/
protected def rec {C : ConjAct G → Sort _} (h : ∀ g, C (toConjAct g)) : ∀ g, C g :=
  h
#align conj_act.rec ConjAct.rec

@[simp]
theorem forall (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (toConjAct x) :=
  Iff.rfl
#align conj_act.forall ConjAct.forall

@[simp]
theorem of_mul_symm_eq : (@ofConjAct G _).symm = to_conj_act :=
  rfl
#align conj_act.of_mul_symm_eq ConjAct.of_mul_symm_eq

@[simp]
theorem to_mul_symm_eq : (@toConjAct G _).symm = of_conj_act :=
  rfl
#align conj_act.to_mul_symm_eq ConjAct.to_mul_symm_eq

@[simp]
theorem toConjAct_ofConjAct (x : ConjAct G) : toConjAct (ofConjAct x) = x :=
  rfl
#align conj_act.to_conj_act_of_conj_act ConjAct.toConjAct_ofConjAct

@[simp]
theorem ofConjAct_toConjAct (x : G) : ofConjAct (toConjAct x) = x :=
  rfl
#align conj_act.of_conj_act_to_conj_act ConjAct.ofConjAct_toConjAct

@[simp]
theorem ofConjAct_one : ofConjAct (1 : ConjAct G) = 1 :=
  rfl
#align conj_act.of_conj_act_one ConjAct.ofConjAct_one

@[simp]
theorem toConjAct_one : toConjAct (1 : G) = 1 :=
  rfl
#align conj_act.to_conj_act_one ConjAct.toConjAct_one

@[simp]
theorem ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹ :=
  rfl
#align conj_act.of_conj_act_inv ConjAct.ofConjAct_inv

@[simp]
theorem toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹ :=
  rfl
#align conj_act.to_conj_act_inv ConjAct.toConjAct_inv

@[simp]
theorem ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  rfl
#align conj_act.of_conj_act_mul ConjAct.ofConjAct_mul

@[simp]
theorem toConjAct_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y :=
  rfl
#align conj_act.to_conj_act_mul ConjAct.toConjAct_mul

instance : SMul (ConjAct G) G where smul g h := ofConjAct g * h * (ofConjAct g)⁻¹

theorem smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  rfl
#align conj_act.smul_def ConjAct.smul_def

end DivInvMonoid

section Units

section Monoid

variable [Monoid M]

instance hasUnitsScalar : SMul (ConjAct Mˣ) M where smul g h := ofConjAct g * h * ↑(ofConjAct g)⁻¹
#align conj_act.has_units_scalar ConjAct.hasUnitsScalar

theorem units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl
#align conj_act.units_smul_def ConjAct.units_smul_def

instance unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M
    where
  smul := (· • ·)
  one_smul := by simp [units_smul_def]
  mul_smul := by simp [units_smul_def, mul_assoc, mul_inv_rev]
  smul_mul := by simp [units_smul_def, mul_assoc]
  smul_one := by simp [units_smul_def]
#align conj_act.units_mul_distrib_mul_action ConjAct.unitsMulDistribMulAction

instance units_sMulCommClass [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M] :
    SMulCommClass α (ConjAct Mˣ) M
    where smul_comm a um m := by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]
#align conj_act.units_smul_comm_class ConjAct.units_sMulCommClass

instance units_smul_comm_class' [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M] :
    SMulCommClass (ConjAct Mˣ) α M :=
  haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _
#align conj_act.units_smul_comm_class' ConjAct.units_smul_comm_class'

end Monoid

section Semiring

variable [Semiring R]

instance unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R :=
  { ConjAct.unitsMulDistribMulAction with
    smul := (· • ·)
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }
#align conj_act.units_mul_semiring_action ConjAct.unitsMulSemiringAction

end Semiring

end Units

section GroupWithZero

variable [GroupWithZero G₀]

@[simp]
theorem ofConjAct_zero : ofConjAct (0 : ConjAct G₀) = 0 :=
  rfl
#align conj_act.of_conj_act_zero ConjAct.ofConjAct_zero

@[simp]
theorem toConjAct_zero : toConjAct (0 : G₀) = 0 :=
  rfl
#align conj_act.to_conj_act_zero ConjAct.toConjAct_zero

instance mulAction₀ : MulAction (ConjAct G₀) G₀
    where
  smul := (· • ·)
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc, mul_inv_rev]
#align conj_act.mul_action₀ ConjAct.mulAction₀

instance smul_comm_class₀ [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass α (ConjAct G₀) G₀
    where smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]
#align conj_act.smul_comm_class₀ ConjAct.smul_comm_class₀

instance smul_comm_class₀' [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass (ConjAct G₀) α G₀ :=
  haveI := SMulCommClass.symm G₀ α G₀
  SMulCommClass.symm _ _ _
#align conj_act.smul_comm_class₀' ConjAct.smul_comm_class₀'

end GroupWithZero

section DivisionRing

variable [DivisionRing K]

instance distribMulAction₀ : DistribMulAction (ConjAct K) K :=
  { ConjAct.mulAction₀ with
    smul := (· • ·)
    smul_zero := by simp [smul_def]
    smul_add := by simp [smul_def, mul_add, add_mul] }
#align conj_act.distrib_mul_action₀ ConjAct.distribMulAction₀

end DivisionRing

variable [Group G]

instance : MulDistribMulAction (ConjAct G) G
    where
  smul := (· • ·)
  smul_mul := by simp [smul_def, mul_assoc]
  smul_one := by simp [smul_def]
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

instance sMulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] :
    SMulCommClass α (ConjAct G) G
    where smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]
#align conj_act.smul_comm_class ConjAct.sMulCommClass

instance smul_comm_class' [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G] :
    SMulCommClass (ConjAct G) α G :=
  haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _
#align conj_act.smul_comm_class' ConjAct.smul_comm_class'

theorem smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  rfl
#align conj_act.smul_eq_mul_aut_conj ConjAct.smul_eq_mulAut_conj

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
theorem fixedPoints_eq_center : fixedPoints (ConjAct G) G = center G :=
  by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]
#align conj_act.fixed_points_eq_center ConjAct.fixedPoints_eq_center

theorem stabilizer_eq_centralizer (g : G) : stabilizer (ConjAct G) g = (zpowers g).centralizer :=
  le_antisymm (le_centralizer_iff.mp (zpowers_le.mpr fun x => mul_inv_eq_iff_eq_mul.mp)) fun x h =>
    mul_inv_eq_of_eq_mul (h g (mem_zpowers g)).symm
#align conj_act.stabilizer_eq_centralizer ConjAct.stabilizer_eq_centralizer

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
instance Subgroup.conjAction {H : Subgroup G} [hH : H.Normal] : SMul (ConjAct G) H :=
  ⟨fun g h => ⟨g • h, hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩
#align conj_act.subgroup.conj_action ConjAct.Subgroup.conjAction

theorem Subgroup.coe_conj_smul {H : Subgroup G} [hH : H.Normal] (g : ConjAct G) (h : H) :
    ↑(g • h) = g • (h : G) :=
  rfl
#align conj_act.subgroup.coe_conj_smul ConjAct.Subgroup.coe_conj_smul

instance Subgroup.conjMulDistribMulAction {H : Subgroup G} [hH : H.Normal] :
    MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.MulDistribMulAction H.Subtype Subgroup.coe_conj_smul
#align conj_act.subgroup.conj_mul_distrib_mul_action ConjAct.Subgroup.conjMulDistribMulAction

/-- Group conjugation on a normal subgroup. Analogous to `mul_aut.conj`. -/
def MulAut.conjNormal {H : Subgroup G} [hH : H.Normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom
#align mul_aut.conj_normal MulAut.conjNormal

@[simp]
theorem MulAut.conjNormal_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl
#align mul_aut.conj_normal_apply MulAut.conjNormal_apply

@[simp]
theorem MulAut.conjNormal_symm_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g :=
  by
  change _ * _⁻¹⁻¹ = _
  rw [inv_inv]
  rfl
#align mul_aut.conj_normal_symm_apply MulAut.conjNormal_symm_apply

@[simp]
theorem MulAut.conjNormal_inv_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conjNormal_symm_apply g h
#align mul_aut.conj_normal_inv_apply MulAut.conjNormal_inv_apply

theorem MulAut.conjNormal_coe {H : Subgroup G} [H.Normal] {h : H} :
    MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun x => rfl
#align mul_aut.conj_normal_coe MulAut.conjNormal_coe

instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
    [h : K.Characteristic] : (K.map H.Subtype).Normal :=
  ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact
      K.apply_coe_mem_map H.subtype
        ⟨_, (set_like.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩
#align conj_act.normal_of_characteristic_of_normal ConjAct.normal_of_characteristic_of_normal

end ConjAct

