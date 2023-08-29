/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.ZPowers
import Mathlib.Algebra.GroupRingAction.Basic

#align_import group_theory.group_action.conj_act from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

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


variable (α M G G₀ R K : Type*)

/-- A type alias for a group `G`. `ConjAct G` acts on `G` by conjugation -/
def ConjAct : Type _ :=
  G
#align conj_act ConjAct

namespace ConjAct

open MulAction Subgroup

variable {M G G₀ R K}

instance [Group G] : Group (ConjAct G) := ‹Group G›

instance [DivInvMonoid G] : DivInvMonoid (ConjAct G) := ‹DivInvMonoid G›

instance [GroupWithZero G] : GroupWithZero (ConjAct G) := ‹GroupWithZero G›

instance [Fintype G] : Fintype (ConjAct G) := ‹Fintype G›

@[simp]
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl
#align conj_act.card ConjAct.card

section DivInvMonoid

variable [DivInvMonoid G]

instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/-- Reinterpret `g : ConjAct G` as an element of `G`. -/
def ofConjAct : ConjAct G ≃* G where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
#align conj_act.of_conj_act ConjAct.ofConjAct

/-- Reinterpret `g : G` as an element of `ConjAct G`. -/
def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm
#align conj_act.to_conj_act ConjAct.toConjAct

/-- A recursor for `ConjAct`, for use as `induction x using ConjAct.rec` when `x : ConjAct G`. -/
protected def rec {C : ConjAct G → Sort*} (h : ∀ g, C (toConjAct g)) : ∀ g, C g :=
  h
#align conj_act.rec ConjAct.rec

@[simp]
theorem «forall» (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (toConjAct x) :=
  id Iff.rfl
#align conj_act.forall ConjAct.forall

@[simp]
theorem of_mul_symm_eq : (@ofConjAct G _).symm = toConjAct :=
  rfl
#align conj_act.of_mul_symm_eq ConjAct.of_mul_symm_eq

@[simp]
theorem to_mul_symm_eq : (@toConjAct G _).symm = ofConjAct :=
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

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem ofConjAct_one : ofConjAct (1 : ConjAct G) = 1 :=
  rfl
#align conj_act.of_conj_act_one ConjAct.ofConjAct_one

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
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

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  rfl
#align conj_act.of_conj_act_mul ConjAct.ofConjAct_mul

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
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

instance unitsScalar : SMul (ConjAct Mˣ) M where smul g h := ofConjAct g * h * ↑(ofConjAct g)⁻¹
#align conj_act.has_units_scalar ConjAct.unitsScalar

theorem units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl
#align conj_act.units_smul_def ConjAct.units_smul_def

-- porting note: very slow without `simp only` and need to separate `units_smul_def`
-- so that things trigger appropriately
instance unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M where
  one_smul := by simp only [units_smul_def, ofConjAct_one, Units.val_one, one_mul, inv_one,
    mul_one, forall_const]
  mul_smul := by
    simp only [units_smul_def]
    -- ⊢ ∀ (x y : ConjAct Mˣ) (b : M), ↑(↑ofConjAct (x * y)) * b * ↑(↑ofConjAct (x *  …
    simp only [map_mul, Units.val_mul, mul_assoc, mul_inv_rev, forall_const, «forall»]
    -- 🎉 no goals
  smul_mul := by
    simp only [units_smul_def]
    -- ⊢ ∀ (r : ConjAct Mˣ) (x y : M), ↑(↑ofConjAct r) * (x * y) * ↑(↑ofConjAct r)⁻¹  …
    simp only [mul_assoc, Units.inv_mul_cancel_left, forall_const, «forall»]
    -- 🎉 no goals
  smul_one := by simp [units_smul_def, mul_one, Units.mul_inv, «forall», forall_const]
                 -- 🎉 no goals
#align conj_act.units_mul_distrib_mul_action ConjAct.unitsMulDistribMulAction


instance unitsSMulCommClass [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M] :
    SMulCommClass α (ConjAct Mˣ) M
    where smul_comm a um m := by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]
                                 -- 🎉 no goals
#align conj_act.units_smul_comm_class ConjAct.unitsSMulCommClass

instance unitsSMulCommClass' [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M] :
    SMulCommClass (ConjAct Mˣ) α M :=
  haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _
#align conj_act.units_smul_comm_class' ConjAct.unitsSMulCommClass'

end Monoid

section Semiring

variable [Semiring R]

-- porting note: very slow without `simp only` and need to separate `units_smul_def`
-- so that things trigger appropriately
instance unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R :=
  { ConjAct.unitsMulDistribMulAction with
    smul_zero := by
      simp only [units_smul_def, mul_zero, zero_mul, «forall», forall_const]
      -- 🎉 no goals
    smul_add := by
      simp only [units_smul_def]
      -- ⊢ ∀ (a : ConjAct Rˣ) (x y : R), ↑(↑ofConjAct a) * (x + y) * ↑(↑ofConjAct a)⁻¹  …
      simp only [mul_add, add_mul, forall_const, «forall»] }
      -- 🎉 no goals
#align conj_act.units_mul_semiring_action ConjAct.unitsMulSemiringAction

end Semiring

end Units

section GroupWithZero

variable [GroupWithZero G₀]

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem ofConjAct_zero : ofConjAct (0 : ConjAct G₀) = 0 :=
  rfl
#align conj_act.of_conj_act_zero ConjAct.ofConjAct_zero

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem toConjAct_zero : toConjAct (0 : G₀) = 0 :=
  rfl
#align conj_act.to_conj_act_zero ConjAct.toConjAct_zero

-- porting note: very slow without `simp only` and need to separate `smul_def`
-- so that things trigger appropriately
instance mulAction₀ : MulAction (ConjAct G₀) G₀ where
  one_smul := by
    simp only [smul_def]
    -- ⊢ ∀ (b : G₀), ↑ofConjAct 1 * b * (↑ofConjAct 1)⁻¹ = b
    simp only [map_one, one_mul, inv_one, mul_one, forall_const]
    -- 🎉 no goals
  mul_smul := by
    simp only [smul_def]
    -- ⊢ ∀ (x y : ConjAct G₀) (b : G₀), ↑ofConjAct (x * y) * b * (↑ofConjAct (x * y)) …
    simp only [map_mul, mul_assoc, mul_inv_rev, forall_const, «forall»]
    -- 🎉 no goals
#align conj_act.mul_action₀ ConjAct.mulAction₀

instance smulCommClass₀ [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass α (ConjAct G₀) G₀
    where smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]
                                 -- 🎉 no goals
#align conj_act.smul_comm_class₀ ConjAct.smulCommClass₀

instance smulCommClass₀' [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass (ConjAct G₀) α G₀ :=
  haveI := SMulCommClass.symm G₀ α G₀
  SMulCommClass.symm _ _ _
#align conj_act.smul_comm_class₀' ConjAct.smulCommClass₀'

end GroupWithZero

section DivisionRing

variable [DivisionRing K]

-- porting note: very slow without `simp only` and need to separate `smul_def`
-- so that things trigger appropriately
instance distribMulAction₀ : DistribMulAction (ConjAct K) K :=
  { ConjAct.mulAction₀ with
    smul_zero := by
      simp only [smul_def]
      -- ⊢ ∀ (a : ConjAct K), ↑ofConjAct a * 0 * (↑ofConjAct a)⁻¹ = 0
      simp only [mul_zero, zero_mul, «forall», forall_const]
      -- 🎉 no goals
    smul_add := by
      simp only [smul_def]
      -- ⊢ ∀ (a : ConjAct K) (x y : K), ↑ofConjAct a * (x + y) * (↑ofConjAct a)⁻¹ = ↑of …
      simp only [mul_add, add_mul, forall_const, «forall»] }
      -- 🎉 no goals
#align conj_act.distrib_mul_action₀ ConjAct.distribMulAction₀

end DivisionRing

variable [Group G]

-- todo: this file is not in good order; I will refactor this after the PR

-- porting note: very slow without `simp only` and need to separate `smul_def`
-- so that things trigger appropriately
instance : MulDistribMulAction (ConjAct G) G where
  smul_mul := by
    simp only [smul_def]
    -- ⊢ ∀ (r : ConjAct G) (x y : G), ↑ofConjAct r * (x * y) * (↑ofConjAct r)⁻¹ = ↑of …
    simp only [mul_assoc, inv_mul_cancel_left, forall_const, «forall»]
    -- 🎉 no goals
                 -- 🎉 no goals
  smul_one := by simp only [smul_def, mul_one, mul_right_inv, «forall», forall_const]
                 -- 🎉 no goals
    -- ⊢ ∀ (x y : ConjAct G) (b : G), ↑ofConjAct (x * y) * b * (↑ofConjAct (x * y))⁻¹ …
  one_smul := by simp only [smul_def, ofConjAct_one, one_mul, inv_one, mul_one, forall_const]
    -- 🎉 no goals
  mul_smul := by
    simp only [smul_def]
    simp only [map_mul, mul_assoc, mul_inv_rev, forall_const, «forall»]

instance smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] :
    SMulCommClass α (ConjAct G) G
    where smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]
                                 -- 🎉 no goals
#align conj_act.smul_comm_class ConjAct.smulCommClass

instance smulCommClass' [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G] :
    SMulCommClass (ConjAct G) α G :=
  haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _
#align conj_act.smul_comm_class' ConjAct.smulCommClass'

theorem smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  rfl
#align conj_act.smul_eq_mul_aut_conj ConjAct.smul_eq_mulAut_conj

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
theorem fixedPoints_eq_center : fixedPoints (ConjAct G) G = center G := by
  ext x
  -- ⊢ x ∈ fixedPoints (ConjAct G) G ↔ x ∈ ↑(center G)
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]
  -- 🎉 no goals
#align conj_act.fixed_points_eq_center ConjAct.fixedPoints_eq_center

@[simp]
theorem mem_orbit_conjAct {g h : G} : g ∈ orbit (ConjAct G) h ↔ IsConj g h := by
  rw [isConj_comm, isConj_iff, mem_orbit_iff]; rfl
  -- ⊢ (∃ x, x • h = g) ↔ ∃ c, c * h * c⁻¹ = g
                                               -- 🎉 no goals
#align conj_act.mem_orbit_conj_act ConjAct.mem_orbit_conjAct

theorem orbitRel_conjAct : (orbitRel (ConjAct G) G).Rel = IsConj :=
  funext₂ fun g h => by rw [orbitRel_apply, mem_orbit_conjAct]
                        -- 🎉 no goals
#align conj_act.orbit_rel_conj_act ConjAct.orbitRel_conjAct

theorem orbit_eq_carrier_conjClasses [Group G] (g : G) :
    orbit (ConjAct G) g = (ConjClasses.mk g).carrier := by
  ext h
  -- ⊢ h ∈ orbit (ConjAct G) g ↔ h ∈ ConjClasses.carrier (ConjClasses.mk g)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, mem_orbit_conjAct]
  -- 🎉 no goals

theorem stabilizer_eq_centralizer (g : G) :
    stabilizer (ConjAct G) g = centralizer (zpowers (toConjAct g) : Set (ConjAct G)) :=
  le_antisymm (le_centralizer_iff.mp (zpowers_le.mpr fun _ => mul_inv_eq_iff_eq_mul.mp)) fun _ h =>
    mul_inv_eq_of_eq_mul (h g (mem_zpowers g)).symm
#align conj_act.stabilizer_eq_centralizer ConjAct.stabilizer_eq_centralizer

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
instance Subgroup.conjAction {H : Subgroup G} [hH : H.Normal] : SMul (ConjAct G) H :=
  ⟨fun g h => ⟨g • (h : G), hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩
#align conj_act.subgroup.conj_action ConjAct.Subgroup.conjAction

theorem Subgroup.val_conj_smul {H : Subgroup G} [H.Normal] (g : ConjAct G) (h : H) :
    ↑(g • h) = g • (h : G) :=
  rfl
#align conj_act.subgroup.coe_conj_smul ConjAct.Subgroup.val_conj_smul

instance Subgroup.conjMulDistribMulAction {H : Subgroup G} [H.Normal] :
    MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.mulDistribMulAction H.subtype Subgroup.val_conj_smul
#align conj_act.subgroup.conj_mul_distrib_mul_action ConjAct.Subgroup.conjMulDistribMulAction

/-- Group conjugation on a normal subgroup. Analogous to `MulAut.conj`. -/
def _root_.MulAut.conjNormal {H : Subgroup G} [H.Normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom
#align mul_aut.conj_normal MulAut.conjNormal

@[simp]
theorem _root_.MulAut.conjNormal_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl
#align mul_aut.conj_normal_apply MulAut.conjNormal_apply

@[simp]
theorem _root_.MulAut.conjNormal_symm_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g := by
  change _ * _⁻¹⁻¹ = _
  -- ⊢ ↑ofConjAct (↑(MulEquiv.toMonoidHom toConjAct) g)⁻¹ * ↑h * (↑(MulEquiv.toMono …
  rw [inv_inv]
  -- ⊢ ↑ofConjAct (↑(MulEquiv.toMonoidHom toConjAct) g)⁻¹ * ↑h * ↑(MulEquiv.toMonoi …
  rfl
  -- 🎉 no goals
#align mul_aut.conj_normal_symm_apply MulAut.conjNormal_symm_apply

@[simp]
theorem _root_.MulAut.conjNormal_inv_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conjNormal_symm_apply g h
#align mul_aut.conj_normal_inv_apply MulAut.conjNormal_inv_apply

theorem _root_.MulAut.conjNormal_val {H : Subgroup G} [H.Normal] {h : H} :
    MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun _ => rfl
#align mul_aut.conj_normal_coe MulAut.conjNormal_val

instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
    [h : K.Characteristic] : (K.map H.subtype).Normal :=
  ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    -- ⊢ b * ↑(Subgroup.subtype H) a * b⁻¹ ∈ map (Subgroup.subtype H) K
    exact K.apply_coe_mem_map H.subtype
      ⟨_, (SetLike.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩
#align conj_act.normal_of_characteristic_of_normal ConjAct.normal_of_characteristic_of_normal

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
          -- ⊢ ↑x * ↑(↑ConjAct.ofConjAct ↑u) = ↑(↑ConjAct.ofConjAct ↑u) * ↑x
          have : (u : ConjAct Mˣ) • x = x := u.2
          -- ⊢ ↑x * ↑(↑ConjAct.ofConjAct ↑u) = ↑(↑ConjAct.ofConjAct ↑u) * ↑x
          rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩,
          -- 🎉 no goals
        map_one' := rfl,
        map_mul' := fun a b ↦ rfl }
    invFun := fun u ↦
      ⟨ConjAct.toConjAct (Units.map (Submonoid.centralizer ({↑x} : Set M)).subtype u), by
      change _ • _ = _
      -- ⊢ ↑ConjAct.toConjAct (↑(Units.map (Submonoid.subtype (Submonoid.centralizer {↑ …
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
      -- ⊢ ↑(Units.map (Submonoid.subtype (Submonoid.centralizer {↑x}))) u * x = x * ↑( …
      exact Units.ext <| (u.1.2 x <| Set.mem_singleton _).symm⟩
      -- 🎉 no goals
    left_inv := fun _ ↦ by ext; rfl
                           -- ⊢ ↑((fun u => { val := ↑ConjAct.toConjAct (↑(Units.map (Submonoid.subtype (Sub …
                                -- 🎉 no goals
    right_inv := fun _ ↦ by ext; rfl
                            -- ⊢ ↑↑(↑(MonoidHom.toHomUnits { toOneHom := { toFun := fun u => { val := ↑(↑Conj …
                                 -- 🎉 no goals
    map_mul' := map_mul _ }

end Units
