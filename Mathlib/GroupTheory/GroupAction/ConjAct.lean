/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `MulAut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `ConjAct G` is introduced for a group `G`. The group `ConjAct G` acts on `G`
by conjugation. The group `ConjAct G` also acts on any normal subgroup of `G` by conjugation.

As a generalization, this also allows:
* `ConjAct Mˣ` to act on `M`, when `M` is a `Monoid`
* `ConjAct G₀` to act on `G₀`, when `G₀` is a `GroupWithZero`

## Implementation Notes

The scalar action in defined in this file can also be written using `MulAut.conj g • h`. This
has the advantage of not using the type alias `ConjAct`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`MulAut.conj g • h` describes an action of `MulAut G` on `G`, and not an action of `G`.

-/

assert_not_exists MonoidWithZero

variable (α M G : Type*)

/-- A type alias for a group `G`. `ConjAct G` acts on `G` by conjugation -/
def ConjAct : Type _ :=
  G

namespace ConjAct

open MulAction Subgroup

variable {M G}

instance [Group G] : Group (ConjAct G) := ‹Group G›

instance [DivInvMonoid G] : DivInvMonoid (ConjAct G) := ‹DivInvMonoid G›

instance [Fintype G] : Fintype (ConjAct G) := ‹Fintype G›

@[simp]
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl

section DivInvMonoid

variable [DivInvMonoid G]

instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/-- Reinterpret `g : ConjAct G` as an element of `G`. -/
def ofConjAct : ConjAct G ≃* G where
  toFun := id
  invFun := id
  map_mul' := fun _ _ => rfl

/-- Reinterpret `g : G` as an element of `ConjAct G`. -/
def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm

/-- A recursor for `ConjAct`, for use as `induction x` when `x : ConjAct G`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {C : ConjAct G → Sort*} (h : ∀ g, C (toConjAct g)) : ∀ g, C g :=
  h

@[simp]
theorem «forall» (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (toConjAct x) :=
  id Iff.rfl

@[simp]
theorem of_mul_symm_eq : (@ofConjAct G _).symm = toConjAct :=
  rfl

@[simp]
theorem to_mul_symm_eq : (@toConjAct G _).symm = ofConjAct :=
  rfl

@[simp]
theorem toConjAct_ofConjAct (x : ConjAct G) : toConjAct (ofConjAct x) = x :=
  rfl

@[simp]
theorem ofConjAct_toConjAct (x : G) : ofConjAct (toConjAct x) = x :=
  rfl

@[simp]
theorem ofConjAct_one : ofConjAct (1 : ConjAct G) = 1 :=
  rfl

@[simp]
theorem toConjAct_one : toConjAct (1 : G) = 1 :=
  rfl

@[simp]
theorem ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹ :=
  rfl

@[simp]
theorem toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹ :=
  rfl

@[simp]
theorem ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  rfl

@[simp]
theorem toConjAct_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y :=
  rfl

instance : SMul (ConjAct G) G where smul g h := ofConjAct g * h * (ofConjAct g)⁻¹

theorem smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  rfl

theorem toConjAct_smul (g h : G) : toConjAct g • h = g * h * g⁻¹ :=
  rfl

end DivInvMonoid

section Units

section Monoid

variable [Monoid M]

instance unitsScalar : SMul (ConjAct Mˣ) M where smul g h := ofConjAct g * h * ↑(ofConjAct g)⁻¹

theorem units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl

instance unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M where
  one_smul := by simp [units_smul_def]
  mul_smul := by simp [units_smul_def, mul_assoc]
  smul_mul := by simp [units_smul_def, mul_assoc]
  smul_one := by simp [units_smul_def]


instance unitsSMulCommClass [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M] :
    SMulCommClass α (ConjAct Mˣ) M where
  smul_comm a um m := by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]

instance unitsSMulCommClass' [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M] :
    SMulCommClass (ConjAct Mˣ) α M :=
  haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

end Monoid

end Units

variable [Group G]

-- todo: this file is not in good order; I will refactor this after the PR

instance : MulDistribMulAction (ConjAct G) G where
  smul_mul := by simp [smul_def]
  smul_one := by simp [smul_def]
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

instance smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] :
    SMulCommClass α (ConjAct G) G where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

instance smulCommClass' [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G] :
    SMulCommClass (ConjAct G) α G :=
  haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _

theorem smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  rfl

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
theorem fixedPoints_eq_center : fixedPoints (ConjAct G) G = center G := by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]

@[simp]
theorem mem_orbit_conjAct {g h : G} : g ∈ orbit (ConjAct G) h ↔ IsConj g h := by
  rw [isConj_comm, isConj_iff, mem_orbit_iff]; rfl

theorem orbitRel_conjAct : ⇑(orbitRel (ConjAct G) G) = IsConj :=
  funext₂ fun g h => by rw [orbitRel_apply, mem_orbit_conjAct]

theorem orbit_eq_carrier_conjClasses (g : G) :
    orbit (ConjAct G) g = (ConjClasses.mk g).carrier := by
  ext h
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, mem_orbit_conjAct]

theorem stabilizer_eq_centralizer (g : G) :
    stabilizer (ConjAct G) g = centralizer (zpowers (toConjAct g) : Set (ConjAct G)) :=
  le_antisymm (le_centralizer_iff.mp (zpowers_le.mpr fun _ => mul_inv_eq_iff_eq_mul.mp)) fun _ h =>
    mul_inv_eq_of_eq_mul (h g (mem_zpowers g)).symm

theorem _root_.Subgroup.centralizer_eq_comap_stabilizer (g : G) :
    Subgroup.centralizer {g} = Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct G) g) := by
  ext k
-- NOTE: `Subgroup.mem_centralizer_iff` should probably be stated
-- with the equality in the other direction
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [eq_comm]
  exact Iff.symm mul_inv_eq_iff_eq_mul

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
instance Subgroup.conjAction {H : Subgroup G} [hH : H.Normal] : SMul (ConjAct G) H :=
  ⟨fun g h => ⟨g • (h : G), hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩

theorem Subgroup.val_conj_smul {H : Subgroup G} [H.Normal] (g : ConjAct G) (h : H) :
    ↑(g • h) = g • (h : G) :=
  rfl

instance Subgroup.conjMulDistribMulAction {H : Subgroup G} [H.Normal] :
    MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.mulDistribMulAction H.subtype Subgroup.val_conj_smul

/-- Group conjugation on a normal subgroup. Analogous to `MulAut.conj`. -/
def _root_.MulAut.conjNormal {H : Subgroup G} [H.Normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom

@[simp]
theorem _root_.MulAut.conjNormal_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl

@[simp]
theorem _root_.MulAut.conjNormal_symm_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g := by
  change _ * _⁻¹⁻¹ = _
  rw [inv_inv]
  rfl

theorem _root_.MulAut.conjNormal_inv_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conjNormal_symm_apply g h

theorem _root_.MulAut.conjNormal_val {H : Subgroup G} [H.Normal] {h : H} :
    MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun _ => rfl

instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
    [h : K.Characteristic] : (K.map H.subtype).Normal :=
  ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact K.apply_coe_mem_map H.subtype
      ⟨_, (SetLike.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩

end ConjAct

section Units

variable [Monoid M]

/-- The stabilizer of `Mˣ` acting on itself by conjugation at `x : Mˣ` is exactly the
units of the centralizer of `x : M`. -/
@[simps! apply_coe_val symm_apply_val_coe]
def unitsCentralizerEquiv (x : Mˣ) :
    (Submonoid.centralizer ({↑x} : Set M))ˣ ≃* MulAction.stabilizer (ConjAct Mˣ) x :=
  MulEquiv.symm
  { toFun := MonoidHom.toHomUnits <|
      { toFun := fun u ↦ ⟨↑(ConjAct.ofConjAct u.1 : Mˣ), by
          rintro x ⟨rfl⟩
          have : (u : ConjAct Mˣ) • x = x := u.2
          rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩,
        map_one' := rfl,
        map_mul' := fun _ _ ↦ rfl }
    invFun := fun u ↦
      ⟨ConjAct.toConjAct (Units.map (Submonoid.centralizer ({↑x} : Set M)).subtype u), by
      change _ • _ = _
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
      exact Units.ext <| (u.1.2 x <| Set.mem_singleton _).symm⟩
    map_mul' := map_mul _ }

end Units
