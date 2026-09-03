/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Data.Set.BooleanAlgebra
public meta import Mathlib.Tactic.ToDual

/-!
# Definition of `orbit`, `fixedPoints` and `stabilizer`

This file defines orbits, stabilizers, and other objects defined in terms of actions.

## Main definitions

* `MonoidAction.orbit`
* `MonoidAction.fixedPoints`
* `MonoidAction.fixedBy`
* `MonoidAction.stabilizer`

-/

@[expose] public section

assert_not_exists MonoidWithZero DistribMulAction

universe u v

open scoped Pointwise

open Function

namespace MonoidAction

variable (M γ α : Type*) [SMul γ α] [Monoid M] [MonoidAction M α]

section Orbit

variable {α}

/-- The orbit of an element under an action. -/
@[to_additive /-- The orbit of an element under an action. -/]
def orbit (a : α) :=
  Set.range fun m : γ => m • a

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbit := orbit
@[deprecated (since := "2026-09-02")] alias _root_.AddAction.orbit := _root_.AddMonoidAction.orbit

variable {γ}

@[to_additive]
theorem mem_orbit_iff {a₁ a₂ : α} : a₂ ∈ orbit γ a₁ ↔ ∃ x : γ, x • a₁ = a₂ :=
  Iff.rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_orbit_iff := mem_orbit_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_iff := _root_.AddMonoidAction.mem_orbit_iff

@[to_additive (attr := simp)]
theorem mem_orbit (a : α) (m : γ) : m • a ∈ orbit γ a :=
  ⟨m, rfl⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_orbit := mem_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit := _root_.AddMonoidAction.mem_orbit

variable {M}

@[to_additive]
theorem mem_orbit_of_mem_orbit {a₁ a₂ : α} (m : M) (h : a₂ ∈ orbit M a₁) :
    m • a₂ ∈ orbit M a₁ := by
  obtain ⟨x, rfl⟩ := mem_orbit_iff.mp h
  simp [smul_smul]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.mem_orbit_of_mem_orbit := mem_orbit_of_mem_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_of_mem_orbit := _root_.AddMonoidAction.mem_orbit_of_mem_orbit

@[to_additive (attr := simp)]
theorem mem_orbit_self (a : α) : a ∈ orbit M a :=
  ⟨1, by simp⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_orbit_self := mem_orbit_self
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_self := _root_.AddMonoidAction.mem_orbit_self

@[to_additive]
theorem nonempty_orbit (a : α) : Set.Nonempty (orbit M a) :=
  Set.range_nonempty _

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.nonempty_orbit := nonempty_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.nonempty_orbit := _root_.AddMonoidAction.nonempty_orbit

@[to_additive]
theorem mapsTo_smul_orbit (m : M) (a : α) : Set.MapsTo (m • ·) (orbit M a) (orbit M a) :=
  Set.mapsTo_iff_subset_preimage.mpr <| Set.range_subset_iff.mpr fun m' => ⟨m * m', mul_smul _ _ _⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mapsTo_smul_orbit := mapsTo_smul_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mapsTo_vadd_orbit := _root_.AddMonoidAction.mapsTo_vadd_orbit

@[to_additive]
theorem smul_orbit_subset (m : M) (a : α) : m • orbit M a ⊆ orbit M a :=
  (mapsTo_smul_orbit m a).image_subset

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.smul_orbit_subset := smul_orbit_subset
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.vadd_orbit_subset := _root_.AddMonoidAction.vadd_orbit_subset

@[to_additive]
theorem orbit_smul_subset (m : M) (a : α) : orbit M (m • a) ⊆ orbit M a :=
  Set.range_subset_iff.2 fun m' => mul_smul m' m a ▸ mem_orbit _ _

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbit_smul_subset := orbit_smul_subset
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit_vadd_subset := _root_.AddMonoidAction.orbit_vadd_subset

@[to_additive]
instance {a : α} : MonoidAction M (orbit M a) where
  smul m := (mapsTo_smul_orbit m a).restrict _ _ _
  one_smul m := Subtype.ext (one_smul M (m : α))
  mul_smul m m' a' := Subtype.ext (mul_smul m m' (a' : α))

@[to_additive (attr := simp)]
theorem orbit.coe_smul {a : α} {m : M} {a' : orbit M a} : ↑(m • a') = m • (a' : α) :=
  rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbit.coe_smul := orbit.coe_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit.coe_vadd := _root_.AddMonoidAction.orbit.coe_vadd

@[to_additive]
lemma orbit_submonoid_subset (S : Submonoid M) (a : α) : orbit S a ⊆ orbit M a := by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbit_submonoid_subset := orbit_submonoid_subset
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit_addSubmonoid_subset := _root_.AddMonoidAction.orbit_addSubmonoid_subset

@[to_additive]
lemma mem_orbit_of_mem_orbit_submonoid {S : Submonoid M} {a b : α} (h : a ∈ orbit S b) :
    a ∈ orbit M b :=
  orbit_submonoid_subset S _ h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.mem_orbit_of_mem_orbit_submonoid := mem_orbit_of_mem_orbit_submonoid
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_of_mem_orbit_addSubmonoid :=
  _root_.AddMonoidAction.mem_orbit_of_mem_orbit_addSubmonoid

end Orbit

section FixedPoints

/-- The set of elements fixed under the whole action. -/
@[to_additive /-- The set of elements fixed under the whole action. -/]
def fixedPoints : Set α :=
  { a : α | ∀ m : M, m • a = a }

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.fixedPoints := fixedPoints
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.fixedPoints := _root_.AddMonoidAction.fixedPoints

variable {M} in
/-- `fixedBy m` is the set of elements fixed by `m`. -/
@[to_additive /-- `fixedBy m` is the set of elements fixed by `m`. -/]
def fixedBy (m : M) : Set α :=
  { x | m • x = x }

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.fixedBy := fixedBy
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.fixedBy := _root_.AddMonoidAction.fixedBy

@[to_additive]
theorem fixed_eq_iInter_fixedBy : fixedPoints M α = ⋂ m : M, fixedBy α m :=
  Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun m => hx m, fun hx m => (Set.mem_iInter.1 hx m :)⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.fixed_eq_iInter_fixedBy := fixed_eq_iInter_fixedBy
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.fixed_eq_iInter_fixedBy := _root_.AddMonoidAction.fixed_eq_iInter_fixedBy

variable {M α}

@[to_additive (attr := simp)]
theorem mem_fixedPoints {a : α} : a ∈ fixedPoints M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_fixedPoints := mem_fixedPoints
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_fixedPoints := _root_.AddMonoidAction.mem_fixedPoints

@[to_additive (attr := simp, grind =)]
theorem mem_fixedBy {m : M} {a : α} : a ∈ fixedBy α m ↔ m • a = a :=
  Iff.rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_fixedBy := mem_fixedBy
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_fixedBy := _root_.AddMonoidAction.mem_fixedBy

@[to_additive]
theorem mem_fixedPoints' {a : α} : a ∈ fixedPoints M α ↔ ∀ a', a' ∈ orbit M a → a' = a :=
  ⟨fun h _ h₁ =>
    let ⟨m, hm⟩ := mem_orbit_iff.1 h₁
    hm ▸ h m,
    fun h _ => h _ (mem_orbit _ _)⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_fixedPoints' := mem_fixedPoints'
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_fixedPoints' := _root_.AddMonoidAction.mem_fixedPoints'

end FixedPoints

section Stabilizers

variable {α}

/-- The stabilizer of a point `a` as a submonoid of `M`. -/
@[to_additive /-- The stabilizer of a point `a` as an additive submonoid of `M`. -/]
def stabilizerSubmonoid (a : α) : Submonoid M where
  carrier := { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.stabilizerSubmonoid := stabilizerSubmonoid
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizerAddSubmonoid := _root_.AddMonoidAction.stabilizerAddSubmonoid

variable {M}

@[to_additive]
instance [DecidableEq α] (a : α) : DecidablePred (· ∈ stabilizerSubmonoid M a) :=
  fun _ => inferInstanceAs <| Decidable (_ = _)

@[to_additive (attr := simp)]
theorem mem_stabilizerSubmonoid_iff {a : α} {m : M} : m ∈ stabilizerSubmonoid M a ↔ m • a = a :=
  Iff.rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.mem_stabilizerSubmonoid_iff := mem_stabilizerSubmonoid_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_stabilizerAddSubmonoid_iff :=
  _root_.AddMonoidAction.mem_stabilizerAddSubmonoid_iff

end Stabilizers

end MonoidAction

section FixedPoints

variable (M : Type u) (α : Type v) [Monoid M]

section Monoid

variable [Monoid α] [MulDistribMulAction M α]

/-- The submonoid of elements fixed under the whole action. -/
def FixedPoints.submonoid : Submonoid α where
  carrier := MonoidAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]
lemma FixedPoints.mem_submonoid (a : α) : a ∈ submonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

instance : SMulCommClass M (FixedPoints.submonoid M α) α where
  smul_comm g x y := by simp_rw [Submonoid.smul_def, smul_eq_mul, smul_mul', x.2 g]

end Monoid

section Group
namespace FixedPoints
variable [Group α] [MulDistribMulAction M α]

/-- The subgroup of elements fixed under the whole action. -/
def subgroup : Subgroup α where
  __ := submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

@[simp]
lemma mem_subgroup (a : α) : a ∈ FixedPoints.subgroup M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

instance : SMulCommClass M (FixedPoints.subgroup M α) α :=
  inferInstanceAs (SMulCommClass M (FixedPoints.submonoid M α) α)

@[simp]
lemma subgroup_toSubmonoid : (FixedPoints.subgroup M α).toSubmonoid = submonoid M α :=
  rfl

end FixedPoints
end Group
end FixedPoints

namespace MonoidAction
variable {G α β : Type*} [Group G] [MonoidAction G α] [MonoidAction G β]

section Orbit

@[to_additive (attr := simp)]
theorem orbit_smul (g : G) (a : α) : orbit G (g • a) = orbit G a :=
  (orbit_smul_subset g a).antisymm <|
    calc
      orbit G a = orbit G (g⁻¹ • g • a) := by rw [inv_smul_smul]
      _ ⊆ orbit G (g • a) := orbit_smul_subset _ _

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbit_smul := orbit_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit_vadd := _root_.AddMonoidAction.orbit_vadd

@[to_additive]
theorem orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔ a ∈ orbit G b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbit_eq_iff := orbit_eq_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit_eq_iff := _root_.AddMonoidAction.orbit_eq_iff

@[to_additive]
theorem mem_orbit_smul (g : G) (a : α) : a ∈ orbit G (g • a) := by
  simp only [orbit_smul, mem_orbit_self]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_orbit_smul := mem_orbit_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_vadd := _root_.AddMonoidAction.mem_orbit_vadd

@[to_additive]
theorem smul_mem_orbit_smul (g h : G) (a : α) : g • a ∈ orbit G (h • a) := by
  simp only [orbit_smul, mem_orbit]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.smul_mem_orbit_smul := smul_mem_orbit_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.vadd_mem_orbit_vadd := _root_.AddMonoidAction.vadd_mem_orbit_vadd

@[to_additive]
lemma subgroup_smul_def {H : Subgroup G} (a : H) (b : α) : a • b = (a : G) • b := rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.subgroup_smul_def := subgroup_smul_def
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.addSubgroup_vadd_def := _root_.AddMonoidAction.addSubgroup_vadd_def

@[to_additive]
lemma orbit_subgroup_subset (H : Subgroup G) (a : α) : orbit H a ⊆ orbit G a :=
  orbit_submonoid_subset H.toSubmonoid a

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbit_subgroup_subset := orbit_subgroup_subset
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit_addSubgroup_subset := _root_.AddMonoidAction.orbit_addSubgroup_subset

@[to_additive]
lemma mem_orbit_of_mem_orbit_subgroup {H : Subgroup G} {a b : α} (h : a ∈ orbit H b) :
    a ∈ orbit G b :=
  orbit_subgroup_subset H _ h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.mem_orbit_of_mem_orbit_subgroup := mem_orbit_of_mem_orbit_subgroup
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_of_mem_orbit_addSubgroup :=
  _root_.AddMonoidAction.mem_orbit_of_mem_orbit_addSubgroup

@[to_additive]
lemma mem_orbit_symm {a₁ a₂ : α} : a₁ ∈ orbit G a₂ ↔ a₂ ∈ orbit G a₁ := by
  simp_rw [← orbit_eq_iff, eq_comm]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_orbit_symm := mem_orbit_symm
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_symm := _root_.AddMonoidAction.mem_orbit_symm

@[to_additive]
lemma mem_orbit_trans {a b c : α} (hab : a ∈ orbit G b) (hbc : b ∈ orbit G c) :
    a ∈ orbit G c := by
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hab
  obtain ⟨g', rfl⟩ := mem_orbit_iff.mp hbc
  rw [mem_orbit_iff]
  use g * g'
  rw [mul_smul]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.mem_orbit_trans := mem_orbit_trans
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_orbit_trans := _root_.AddMonoidAction.mem_orbit_trans

@[to_additive]
lemma mem_subgroup_orbit_iff {H : Subgroup G} {x : α} {a b : orbit G x} :
    a ∈ MonoidAction.orbit H b ↔ (a : α) ∈ MonoidAction.orbit H (b : α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨g, rfl⟩
    exact MonoidAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def, ← orbit.coe_smul, ← Subtype.ext_iff] at h
    subst h
    exact MonoidAction.mem_orbit _ g

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.mem_subgroup_orbit_iff := mem_subgroup_orbit_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_addSubgroup_orbit_iff := _root_.AddMonoidAction.mem_addSubgroup_orbit_iff

variable (G α)

/-- The relation 'in the same orbit'. -/
@[to_additive /-- The relation 'in the same orbit'. -/]
def orbitRel : Setoid α where
  r a b := a ∈ orbit G b
  iseqv := ⟨mem_orbit_self, mem_orbit_symm.mp, by grind [orbit_eq_iff]⟩

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbitRel := orbitRel
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel := _root_.AddMonoidAction.orbitRel

variable {G α}

@[to_additive]
theorem orbitRel_apply {a b : α} : orbitRel G α a b ↔ a ∈ orbit G b :=
  Iff.rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbitRel_apply := orbitRel_apply
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel_apply := _root_.AddMonoidAction.orbitRel_apply

/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/
@[to_additive
/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/]
theorem quotient_preimage_image_eq_union_mul (U : Set α) :
    letI := orbitRel G α
    Quotient.mk' ⁻¹' Quotient.mk' '' U = ⋃ g : G, (g • ·) '' U := by
  let := orbitRel G α
  set f : α → Quotient (MonoidAction.orbitRel G α) := Quotient.mk'
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨g, rfl⟩ := Quotient.exact hab
    rw [Set.mem_iUnion]
    exact ⟨g⁻¹, g • a, hb, inv_smul_smul g a⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨g, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image]
    refine ⟨g⁻¹ • a, ?_, by simp +instances [f, orbitRel, Quotient.eq']⟩
    rw [← hu₂]
    convert! hu₁
    simp only [inv_smul_smul]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.quotient_preimage_image_eq_union_mul := quotient_preimage_image_eq_union_mul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.quotient_preimage_image_eq_union_add :=
  _root_.AddMonoidAction.quotient_preimage_image_eq_union_add

@[to_additive]
theorem disjoint_image_image_iff {U V : Set α} :
    letI := orbitRel G α
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ ∀ x ∈ U, ∀ g : G, g • x ∉ V := by
  let := orbitRel G α
  set f : α → Quotient (MonoidAction.orbitRel G α) := Quotient.mk'
  refine
    ⟨fun h a a_in_U g g_in_V =>
      h.le_bot ⟨⟨a, a_in_U, Quotient.sound ⟨g⁻¹, ?_⟩⟩, ⟨g • a, g_in_V, rfl⟩⟩, ?_⟩
  · simp
  · intro h
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb₁, hb₂⟩ ⟨c, hc₁, hc₂⟩
    obtain ⟨g, rfl⟩ := Quotient.exact (hc₂.trans hb₂.symm)
    exact h b hb₁ g hc₁

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.disjoint_image_image_iff := disjoint_image_image_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.disjoint_image_image_iff := _root_.AddMonoidAction.disjoint_image_image_iff

@[to_additive]
theorem image_inter_image_iff (U V : Set α) :
    letI := orbitRel G α
    Quotient.mk' '' U ∩ Quotient.mk' '' V = ∅ ↔ ∀ x ∈ U, ∀ g : G, g • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.image_inter_image_iff := image_inter_image_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.image_inter_image_iff := _root_.AddMonoidAction.image_inter_image_iff

variable (G α)

/-- The quotient by `MonoidAction.orbitRel`, given a name to enable dot notation. -/
@[to_additive
    /-- The quotient by `AddMonoidAction.orbitRel`, given a name to enable dot notation. -/]
abbrev orbitRel.Quotient : Type _ :=
  _root_.Quotient <| orbitRel G α

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbitRel.Quotient := orbitRel.Quotient
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient := _root_.AddMonoidAction.orbitRel.Quotient

variable {G α}

@[to_additive (attr := simp)]
lemma orbitRel.Quotient.quotient_smul_eq {g : G} {a : α} :
    ⟦g • a⟧ = (⟦a⟧ : orbitRel.Quotient G α) := Quotient.eq.mpr ⟨g, rfl⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.quotient_smul_eq := orbitRel.Quotient.quotient_smul_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.quotient_vadd_eq :=
  _root_.AddMonoidAction.orbitRel.Quotient.quotient_vadd_eq

/-- The orbit corresponding to an element of the quotient by `MonoidAction.orbitRel` -/
@[to_additive /-- The orbit corresponding to an element of the quotient by
`AddMonoidAction.orbitRel` -/]
nonrec def orbitRel.Quotient.orbit (x : orbitRel.Quotient G α) : Set α :=
  Quotient.liftOn' x (orbit G) fun _ _ => MonoidAction.orbit_eq_iff.2

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.orbit := orbitRel.Quotient.orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.orbit := _root_.AddMonoidAction.orbitRel.Quotient.orbit

@[to_additive (attr := simp)]
theorem orbitRel.Quotient.orbit_mk (a : α) :
    orbitRel.Quotient.orbit (Quotient.mk'' a : orbitRel.Quotient G α) = MonoidAction.orbit G a :=
  rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.orbit_mk := orbitRel.Quotient.orbit_mk
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.orbit_mk :=
  _root_.AddMonoidAction.orbitRel.Quotient.orbit_mk

@[to_additive]
theorem orbitRel.Quotient.mem_orbit {a : α} {x : orbitRel.Quotient G α} :
    a ∈ x.orbit ↔ Quotient.mk'' a = x := by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.mem_orbit := orbitRel.Quotient.mem_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.mem_orbit :=
  _root_.AddMonoidAction.orbitRel.Quotient.mem_orbit

/-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/
@[to_additive /-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/]
theorem orbitRel.Quotient.orbit_eq_orbit_out (x : orbitRel.Quotient G α)
    {φ : orbitRel.Quotient G α → α} (hφ : letI := orbitRel G α; RightInverse φ Quotient.mk') :
    orbitRel.Quotient.orbit x = MonoidAction.orbit G (φ x) := by
  conv_lhs => rw [← hφ x]
  rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.orbit_eq_orbit_out := orbitRel.Quotient.orbit_eq_orbit_out
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.orbit_eq_orbit_out :=
  _root_.AddMonoidAction.orbitRel.Quotient.orbit_eq_orbit_out

@[to_additive]
lemma orbitRel.Quotient.orbit_injective :
    Injective (orbitRel.Quotient.orbit : orbitRel.Quotient G α → Set α) := by
  intro x y h
  simp_rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', orbit_eq_iff,
    ← orbitRel_apply] at h
  simpa [← Quotient.eq''] using h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.orbit_injective := orbitRel.Quotient.orbit_injective
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.orbit_injective :=
  _root_.AddMonoidAction.orbitRel.Quotient.orbit_injective

@[to_additive (attr := simp)]
lemma orbitRel.Quotient.orbit_inj {x y : orbitRel.Quotient G α} : x.orbit = y.orbit ↔ x = y :=
  orbitRel.Quotient.orbit_injective.eq_iff

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.orbit_inj := orbitRel.Quotient.orbit_inj
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.orbit_inj :=
  _root_.AddMonoidAction.orbitRel.Quotient.orbit_inj

@[to_additive]
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq {H : Subgroup G} {a b : α}
    (h : (⟦a⟧ : orbitRel.Quotient H α) = ⟦b⟧) : (⟦a⟧ : orbitRel.Quotient G α) = ⟦b⟧ := by
  rw [@Quotient.eq] at h ⊢
  exact mem_orbit_of_mem_orbit_subgroup h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq :=
  orbitRel.quotient_eq_of_quotient_subgroup_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.quotient_eq_of_quotient_addSubgroup_eq :=
  _root_.AddMonoidAction.orbitRel.quotient_eq_of_quotient_addSubgroup_eq

@[to_additive]
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq' {H : Subgroup G} {a b : α}
    (h : (Quotient.mk'' a : orbitRel.Quotient H α) = Quotient.mk'' b) :
    (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b :=
  orbitRel.quotient_eq_of_quotient_subgroup_eq h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq' :=
  orbitRel.quotient_eq_of_quotient_subgroup_eq'
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.quotient_eq_of_quotient_addSubgroup_eq' :=
  _root_.AddMonoidAction.orbitRel.quotient_eq_of_quotient_addSubgroup_eq'

@[to_additive]
nonrec lemma orbitRel.Quotient.nonempty_orbit (x : orbitRel.Quotient G α) :
    Set.Nonempty x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact nonempty_orbit _

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.nonempty_orbit := orbitRel.Quotient.nonempty_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.nonempty_orbit :=
  _root_.AddMonoidAction.orbitRel.Quotient.nonempty_orbit

@[to_additive]
nonrec lemma orbitRel.Quotient.mapsTo_smul_orbit (g : G) (x : orbitRel.Quotient G α) :
    Set.MapsTo (g • ·) x.orbit x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact mapsTo_smul_orbit g x.out

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.mapsTo_smul_orbit := orbitRel.Quotient.mapsTo_smul_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.mapsTo_vadd_orbit :=
  _root_.AddMonoidAction.orbitRel.Quotient.mapsTo_vadd_orbit

@[to_additive]
instance (x : orbitRel.Quotient G α) : MonoidAction G x.orbit where
  smul g := (orbitRel.Quotient.mapsTo_smul_orbit g x).restrict _ _ _
  one_smul a := Subtype.ext (one_smul G (a : α))
  mul_smul g g' a' := Subtype.ext (mul_smul g g' (a' : α))

@[to_additive (attr := simp)]
lemma orbitRel.Quotient.orbit.coe_smul {g : G} {x : orbitRel.Quotient G α} {a : x.orbit} :
    ↑(g • a) = g • (a : α) :=
  rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.orbit.coe_smul := orbitRel.Quotient.orbit.coe_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.orbit.coe_vadd :=
  _root_.AddMonoidAction.orbitRel.Quotient.orbit.coe_vadd

@[to_additive (attr := norm_cast, simp)]
lemma orbitRel.Quotient.mem_subgroup_orbit_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (a : α) ∈ MonoidAction.orbit H (b : α) ↔ a ∈ MonoidAction.orbit H b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def, ← orbit.coe_smul, ← Subtype.ext_iff] at h
    subst h
    exact MonoidAction.mem_orbit _ g
  · rcases h with ⟨g, rfl⟩
    exact MonoidAction.mem_orbit _ g

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.mem_subgroup_orbit_iff :=
  orbitRel.Quotient.mem_subgroup_orbit_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.mem_addSubgroup_orbit_iff :=
  _root_.AddMonoidAction.orbitRel.Quotient.mem_addSubgroup_orbit_iff

@[to_additive]
lemma orbitRel.Quotient.subgroup_quotient_eq_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧ ↔
      (⟦↑a⟧ : orbitRel.Quotient H α) = ⟦↑b⟧ := by
  simp_rw [← @Quotient.mk''_eq_mk, Quotient.eq'']
  exact orbitRel.Quotient.mem_subgroup_orbit_iff.symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.subgroup_quotient_eq_iff :=
  orbitRel.Quotient.subgroup_quotient_eq_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.addSubgroup_quotient_eq_iff :=
  _root_.AddMonoidAction.orbitRel.Quotient.addSubgroup_quotient_eq_iff

@[to_additive]
lemma orbitRel.Quotient.mem_subgroup_orbit_iff' {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} {c : α} (h : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧) :
    (a : α) ∈ MonoidAction.orbit H c ↔ (b : α) ∈ MonoidAction.orbit H c := by
  simp_rw [mem_orbit_symm (a₂ := c)]
  convert! Iff.rfl using 2
  rw [orbit_eq_iff]
  suffices hb : ↑b ∈ orbitRel.Quotient.orbit (⟦a⟧ : orbitRel.Quotient H x.orbit) by
    rw [orbitRel.Quotient.orbit_eq_orbit_out (⟦a⟧ : orbitRel.Quotient H x.orbit) Quotient.out_eq']
       at hb
    rw [orbitRel.Quotient.mem_subgroup_orbit_iff]
    convert! hb using 1
    rw [orbit_eq_iff, ← orbitRel_apply, ← Quotient.eq'', Quotient.out_eq', @Quotient.mk''_eq_mk]
  rw [orbitRel.Quotient.mem_orbit, h, @Quotient.mk''_eq_mk]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbitRel.Quotient.mem_subgroup_orbit_iff' :=
  orbitRel.Quotient.mem_subgroup_orbit_iff'
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbitRel.Quotient.mem_addSubgroup_orbit_iff' :=
  _root_.AddMonoidAction.orbitRel.Quotient.mem_addSubgroup_orbit_iff'

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `MonoidAction.orbitRel.Quotient.orbit` instead of
`MonoidAction.orbit`, to avoid mentioning `Quotient.out`. -/
@[to_additive
  /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive group action.

  This version is expressed in terms of `AddMonoidAction.orbitRel.Quotient.orbit` instead of
  `AddMonoidAction.orbit`, to avoid mentioning `Quotient.out`. -/]
def selfEquivSigmaOrbits' : α ≃ Σ ω : Ω, ω.orbit :=
  letI := orbitRel G α
  calc
    α ≃ Σ ω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σ ω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.selfEquivSigmaOrbits' := selfEquivSigmaOrbits'
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.selfEquivSigmaOrbits' := _root_.AddMonoidAction.selfEquivSigmaOrbits'

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive
group action. -/]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
noncomputable def selfEquivSigmaOrbits : α ≃ Σ ω : Ω, orbit G ω.out :=
  (selfEquivSigmaOrbits' G α).trans <|
    Equiv.sigmaCongrRight fun _ =>
      Set.equivOfEq <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.selfEquivSigmaOrbits := selfEquivSigmaOrbits
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.selfEquivSigmaOrbits := _root_.AddMonoidAction.selfEquivSigmaOrbits

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
Phrased as a set union. See `MonoidAction.selfEquivSigmaOrbits` for the type isomorphism. -/
@[to_additive /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive
group action. Phrased as a set union. See `AddMonoidAction.selfEquivSigmaOrbits` for the type
isomorphism. -/]
lemma univ_eq_iUnion_orbit :
    Set.univ (α := α) = ⋃ x : Ω, x.orbit := by
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨Quotient.mk'' x, by simp⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.univ_eq_iUnion_orbit := univ_eq_iUnion_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.univ_eq_iUnion_orbit := _root_.AddMonoidAction.univ_eq_iUnion_orbit

end Orbit

section Stabilizer

variable (G) in
/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive /-- The stabilizer of an element under an action, i.e. what sends the element to
itself. An additive subgroup. -/]
def stabilizer (a : α) : Subgroup G :=
  { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.stabilizer := stabilizer
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizer := _root_.AddMonoidAction.stabilizer

@[to_additive]
instance [DecidableEq α] (a : α) : DecidablePred (· ∈ stabilizer G a) :=
  fun _ => inferInstanceAs <| Decidable (_ = _)

@[to_additive (attr := simp)]
theorem mem_stabilizer_iff {a : α} {g : G} : g ∈ stabilizer G a ↔ g • a = a :=
  Iff.rfl

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.mem_stabilizer_iff := mem_stabilizer_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.mem_stabilizer_iff := _root_.AddMonoidAction.mem_stabilizer_iff

@[to_additive]
lemma le_stabilizer_smul_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β) :
    stabilizer G a ≤ stabilizer G (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.le_stabilizer_smul_left := le_stabilizer_smul_left
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.le_stabilizer_vadd_left := _root_.AddMonoidAction.le_stabilizer_vadd_left

-- This lemma does not need `MonoidAction G α`, only `SMul G α`.
-- We use `G'` instead of `G` to locally reduce the typeclass assumptions.
@[to_additive]
lemma le_stabilizer_smul_right {G'} [Group G'] [SMul α β] [MonoidAction G' β]
    [SMulCommClass G' α β] (a : α) (b : β) :
    stabilizer G' b ≤ stabilizer G' (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.le_stabilizer_smul_right := le_stabilizer_smul_right
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.le_stabilizer_vadd_right := _root_.AddMonoidAction.le_stabilizer_vadd_right

@[to_additive (attr := simp)]
lemma stabilizer_smul_eq_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
    (h : Injective (· • b : α → β)) : stabilizer G (a • b) = stabilizer G a := by
  refine (le_stabilizer_smul_left _ _).antisymm' fun a ha ↦ ?_
  simpa only [mem_stabilizer_iff, ← smul_assoc, h.eq_iff] using ha

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.stabilizer_smul_eq_left := stabilizer_smul_eq_left
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizer_vadd_eq_left := _root_.AddMonoidAction.stabilizer_vadd_eq_left

@[to_additive (attr := simp)]
lemma stabilizer_smul_eq_right {α} [Group α] [MonoidAction α β] [SMulCommClass G α β] (a : α)
    (b : β) :
    stabilizer G (a • b) = stabilizer G b :=
  (le_stabilizer_smul_right _ _).antisymm' <| (le_stabilizer_smul_right a⁻¹ _).trans_eq <| by
    rw [inv_smul_smul]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.stabilizer_smul_eq_right := stabilizer_smul_eq_right
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizer_vadd_eq_right := _root_.AddMonoidAction.stabilizer_vadd_eq_right

@[to_additive (attr := simp)]
lemma stabilizer_mul_eq_left [Group α] [IsScalarTower G α α] (a b : α) :
    stabilizer G (a * b) = stabilizer G a := stabilizer_smul_eq_left a _ <| mul_left_injective _

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.stabilizer_mul_eq_left := stabilizer_mul_eq_left
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizer_add_eq_left := _root_.AddMonoidAction.stabilizer_add_eq_left

@[to_additive (attr := simp)]
lemma stabilizer_mul_eq_right [Group α] [SMulCommClass G α α] (a b : α) :
    stabilizer G (a * b) = stabilizer G b := stabilizer_smul_eq_right a _

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.stabilizer_mul_eq_right := stabilizer_mul_eq_right
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizer_add_eq_right := _root_.AddMonoidAction.stabilizer_add_eq_right

end Stabilizer

end MonoidAction
