/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Basic properties of group actions

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `MulAction.orbit`
* `MulAction.fixedPoints`
* `MulAction.fixedBy`
* `MulAction.stabilizer`

-/


universe u v

open Pointwise

open Function

namespace MulAction

variable (M : Type u) [Monoid M] (α : Type v) [MulAction M α] {β : Type*} [MulAction M β]

section Orbit

variable {α M}

@[to_additive]
lemma fst_mem_orbit_of_mem_orbit {x y : α × β} (h : x ∈ MulAction.orbit M y) :
    x.1 ∈ MulAction.orbit M y.1 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
lemma snd_mem_orbit_of_mem_orbit {x y : α × β} (h : x ∈ MulAction.orbit M y) :
    x.2 ∈ MulAction.orbit M y.2 := by
  rcases h with ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
lemma _root_.Finite.finite_mulAction_orbit [Finite M] (a : α) : Set.Finite (orbit M a) :=
  Set.finite_range _

variable (M)

@[to_additive]
theorem orbit_eq_univ [IsPretransitive M α] (a : α) : orbit M a = Set.univ :=
  (surjective_smul M a).range_eq

end Orbit

section FixedPoints

variable {M α}

@[to_additive (attr := simp)]
theorem subsingleton_orbit_iff_mem_fixedPoints {a : α} :
    (orbit M a).Subsingleton ↔ a ∈ fixedPoints M α := by
  rw [mem_fixedPoints]
  constructor
  · exact fun h m ↦ h (mem_orbit a m) (mem_orbit_self a)
  · rintro h _ ⟨m, rfl⟩ y ⟨p, rfl⟩
    simp only [h]

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : α} [Fintype (orbit M a)] :
    a ∈ fixedPoints M α ↔ Fintype.card (orbit M a) = 1 := by
  simp only [← subsingleton_orbit_iff_mem_fixedPoints, le_antisymm_iff,
    Fintype.card_le_one_iff_subsingleton, Nat.add_one_le_iff, Fintype.card_pos_iff,
    Set.subsingleton_coe, iff_self_and, Set.nonempty_coe_sort, orbit_nonempty, implies_true]

@[to_additive instDecidablePredMemSetFixedByAddOfDecidableEq]
instance (m : M) [DecidableEq β] :
    DecidablePred fun b : β => b ∈ MulAction.fixedBy β m := fun b ↦ by
  simp only [MulAction.mem_fixedBy]
  infer_instance

end FixedPoints

end MulAction

/-- `smul` by a `k : M` over a group is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `NoZeroSMulDivisors`. -/
theorem smul_cancel_of_non_zero_divisor {M G : Type*} [Monoid M] [AddGroup G]
    [DistribMulAction M G] (k : M) (h : ∀ x : G, k • x = 0 → x = 0) {a b : G} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub, h', sub_self]

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

@[to_additive] theorem fixedPoints_of_subsingleton [Subsingleton α] :
    fixedPoints G α = .univ := by
  apply Set.eq_univ_of_forall
  simp only [mem_fixedPoints]
  intro x hx
  apply Subsingleton.elim ..

/-- If a group acts nontrivially, then the type is nontrivial -/
@[to_additive /-- If a subgroup acts nontrivially, then the type is nontrivial. -/]
theorem nontrivial_of_fixedPoints_ne_univ (h : fixedPoints G α ≠ .univ) :
    Nontrivial α :=
  (subsingleton_or_nontrivial α).resolve_left fun _ ↦ h fixedPoints_of_subsingleton

section Orbit

-- TODO: This proof is redoing a special case of `MulAction.IsInvariantBlock.isBlock`. Can we move
-- this lemma earlier to golf?
@[to_additive (attr := simp)]
theorem smul_orbit (g : G) (a : α) : g • orbit G a = orbit G a :=
  (smul_orbit_subset g a).antisymm <|
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ ⊆ g • orbit G a := Set.image_mono (smul_orbit_subset _ _)

/-- The action of a group on an orbit is transitive. -/
@[to_additive /-- The action of an additive group on an orbit is transitive. -/]
instance (a : α) : IsPretransitive G (orbit G a) :=
  ⟨by
    rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    use h * g⁻¹
    ext1
    simp [mul_smul]⟩

@[to_additive]
lemma orbitRel_subgroup_le (H : Subgroup G) : orbitRel H α ≤ orbitRel G α :=
  Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

@[to_additive]
lemma orbitRel_subgroupOf (H K : Subgroup G) :
    orbitRel (H.subgroupOf K) α = orbitRel (H ⊓ K : Subgroup G) α := by
  rw [← Subgroup.subgroupOf_map_subtype]
  ext x
  simp_rw [orbitRel_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only
    simp only [Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf] at gp
    refine mem_orbit _ (⟨⟨gv, ?_⟩, ?_⟩ : H.subgroupOf K)
    · exact gp.2
    · simp only [Subgroup.mem_subgroupOf]
      exact gp.1

variable (G α)

/-- An action is pretransitive if and only if the quotient by `MulAction.orbitRel` is a
subsingleton. -/
@[to_additive /-- An additive action is pretransitive if and only if the quotient by
`AddAction.orbitRel` is a subsingleton. -/]
theorem pretransitive_iff_subsingleton_quotient :
    IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α) := by
  refine ⟨fun _ ↦ ⟨fun a b ↦ ?_⟩, fun _ ↦ ⟨fun a b ↦ ?_⟩⟩
  · refine Quot.inductionOn a (fun x ↦ ?_)
    exact Quot.inductionOn b (fun y ↦ Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq''.mp h

/-- If `α` is non-empty, an action is pretransitive if and only if the quotient has exactly one
element. -/
@[to_additive /-- If `α` is non-empty, an additive action is pretransitive if and only if the
quotient has exactly one element. -/]
theorem pretransitive_iff_unique_quotient_of_nonempty [Nonempty α] :
    IsPretransitive G α ↔ Nonempty (Unique <| orbitRel.Quotient G α) := by
  rw [unique_iff_subsingleton_and_nonempty, pretransitive_iff_subsingleton_quotient, iff_self_and]
  exact fun _ ↦ (nonempty_quotient_iff _).mpr inferInstance

variable {G α}

@[to_additive]
instance (x : orbitRel.Quotient G α) : IsPretransitive G x.orbit where
  exists_smul_eq := by
    induction x using Quotient.inductionOn'
    rintro ⟨y, yh⟩ ⟨z, zh⟩
    rw [orbitRel.Quotient.mem_orbit, Quotient.eq''] at yh zh
    rcases yh with ⟨g, rfl⟩
    rcases zh with ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    ext
    simp [mul_smul]

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

@[to_additive]
lemma _root_.Finite.of_finite_mulAction_orbitRel_quotient [Finite G] [Finite Ω] : Finite α := by
  rw [(selfEquivSigmaOrbits' G _).finite_iff]
  have : ∀ g : Ω, Finite g.orbit := by
    intro g
    induction g using Quotient.inductionOn'
    simpa [Set.finite_coe_iff] using Finite.finite_mulAction_orbit _
  exact Finite.instSigma

variable (β)

@[to_additive]
lemma orbitRel_le_fst :
    orbitRel G (α × β) ≤ (orbitRel G α).comap Prod.fst :=
  Setoid.le_def.2 fst_mem_orbit_of_mem_orbit

@[to_additive]
lemma orbitRel_le_snd :
    orbitRel G (α × β) ≤ (orbitRel G β).comap Prod.snd :=
  Setoid.le_def.2 snd_mem_orbit_of_mem_orbit

end Orbit

section Stabilizer
variable (G)

variable {G}

/-- If the stabilizer of `a` is `S`, then the stabilizer of `g • a` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g • a) = (stabilizer G a).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul,
    inv_mul_cancel, one_smul, ← mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable {g h k : G} {a b c : α}

/-- The natural group equivalence between the stabilizers of two elements in the same orbit. -/
def stabilizerEquivStabilizer (hg : b = g • a) : stabilizer G a ≃* stabilizer G b :=
  ((MulAut.conj g).subgroupMap (stabilizer G a)).trans
    (MulEquiv.subgroupCongr (by
      rw [hg, stabilizer_smul_eq_stabilizer_map_conj g a, ← MulEquiv.toMonoidHom_eq_coe]))

theorem stabilizerEquivStabilizer_apply (hg : b = g • a) (x : stabilizer G a) :
    stabilizerEquivStabilizer hg x = MulAut.conj g x := by
  simp [stabilizerEquivStabilizer]

theorem stabilizerEquivStabilizer_symm_apply (hg : b = g • a) (x : stabilizer G b) :
    (stabilizerEquivStabilizer hg).symm x = MulAut.conj g⁻¹ x := by
  simp [stabilizerEquivStabilizer]

theorem stabilizerEquivStabilizer_trans (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)
    (H : k = h * g) :
    (stabilizerEquivStabilizer hg).trans (stabilizerEquivStabilizer hh) =
      stabilizerEquivStabilizer hk := by
  ext; simp [stabilizerEquivStabilizer_apply, H]

theorem stabilizerEquivStabilizer_one :
    stabilizerEquivStabilizer (one_smul G a).symm = MulEquiv.refl (stabilizer G a) := by
  ext; simp [stabilizerEquivStabilizer_apply]

theorem stabilizerEquivStabilizer_symm (hg : b = g • a) :
    (stabilizerEquivStabilizer hg).symm =
      stabilizerEquivStabilizer (eq_inv_smul_iff.mpr hg.symm) := by
  ext x; simp [stabilizerEquivStabilizer]

theorem stabilizerEquivStabilizer_inv (hg : b = g⁻¹ • a) :
    stabilizerEquivStabilizer hg =
      (stabilizerEquivStabilizer (inv_smul_eq_iff.mp hg.symm)).symm := by
  ext; simp [stabilizerEquivStabilizer]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel (h : orbitRel G α a b) :
    stabilizer G a ≃* stabilizer G b :=
  (stabilizerEquivStabilizer (Classical.choose_spec h).symm).symm

end Stabilizer

end MulAction

namespace AddAction
variable {G α : Type*} [AddGroup G] [AddAction G α]

variable {g h k : G} {a b c : α}
/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g +ᵥ a) = (stabilizer G a).map (AddAut.conj g).toMul.toAddMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd,
    neg_add_cancel, zero_vadd, ← mem_stabilizer_iff, AddSubgroup.mem_map_equiv,
    AddAut.conj_symm_apply]

variable {g h k : G} {a b c : α}

/-- The natural group equivalence between the stabilizers of two elements in the same orbit. -/
def stabilizerEquivStabilizer (hg : b = g +ᵥ a) : stabilizer G a ≃+ stabilizer G b :=
  AddEquiv.trans ((AddAut.conj g).toMul.addSubgroupMap _)
    (AddEquiv.addSubgroupCongr (by
      rw [hg, stabilizer_vadd_eq_stabilizer_map_conj g a, ← AddEquiv.toAddMonoidHom_eq_coe]))

theorem stabilizerEquivStabilizer_apply (hg : b = g +ᵥ a) (x : stabilizer G a) :
    stabilizerEquivStabilizer hg x = (AddAut.conj g).toMul x := by
  simp [stabilizerEquivStabilizer]

theorem stabilizerEquivStabilizer_symm_apply (hg : b = g +ᵥ b) (x : stabilizer G b) :
    (stabilizerEquivStabilizer hg).symm x = (AddAut.conj (-g)).toMul x := by
  simp [stabilizerEquivStabilizer]

theorem stabilizerEquivStabilizer_trans
    (hg : b = g +ᵥ a) (hh : c = h +ᵥ b) (hk : c = k +ᵥ a) (H : k = h + g) :
    (stabilizerEquivStabilizer hg).trans (stabilizerEquivStabilizer hh)
      = stabilizerEquivStabilizer hk := by
  ext; simp [stabilizerEquivStabilizer_apply, H]

theorem stabilizerEquivStabilizer_zero :
    stabilizerEquivStabilizer (zero_vadd G a).symm = AddEquiv.refl (stabilizer G a) := by
  ext; simp [stabilizerEquivStabilizer_apply]

theorem stabilizerEquivStabilizer_symm (hg : b = g +ᵥ a) :
    (stabilizerEquivStabilizer hg).symm =
      stabilizerEquivStabilizer (eq_neg_vadd_iff.mpr hg.symm) := by
  ext; simp [stabilizerEquivStabilizer]

theorem stabilizerEquivStabilizer_neg (hg : b = -g +ᵥ a) :
    stabilizerEquivStabilizer hg =
      (stabilizerEquivStabilizer (neg_vadd_eq_iff.mp hg.symm)).symm := by
  ext; simp [stabilizerEquivStabilizer]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel (h : orbitRel G α a b) :
    stabilizer G a ≃+ stabilizer G b :=
  (stabilizerEquivStabilizer (Classical.choose_spec h).symm).symm

end AddAction

attribute [to_additive existing] MulAction.stabilizerEquivStabilizer
attribute [to_additive existing] MulAction.stabilizerEquivStabilizer_trans
attribute [to_additive existing] MulAction.stabilizerEquivStabilizer_one
attribute [to_additive existing] MulAction.stabilizerEquivStabilizer_inv
attribute [to_additive existing] MulAction.stabilizerEquivStabilizerOfOrbitRel

theorem Equiv.swap_mem_stabilizer {α : Type*} [DecidableEq α] {S : Set α} {a b : α} :
    Equiv.swap a b ∈ MulAction.stabilizer (Equiv.Perm α) S ↔ (a ∈ S ↔ b ∈ S) := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff, ← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h ↦ by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩

namespace MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions. -/
@[to_additive
  /-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions. -/]
theorem le_stabilizer_iff_smul_le (s : Set α) (H : Subgroup G) :
    H ≤ stabilizer G s ↔ ∀ g ∈ H, g • s ⊆ s := by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  · intro hyp g hg
    rw [mem_stabilizer_iff]
    apply subset_antisymm (hyp g hg)
    intro x hx
    use g⁻¹ • x
    constructor
    · apply hyp g⁻¹ (inv_mem hg)
      simp only [Set.smul_mem_smul_set_iff, hx]
    · simp only [smul_inv_smul]

end MulAction

section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

variable {M} in
lemma Module.stabilizer_units_eq_bot_of_ne_zero {x : M} (hx : x ≠ 0) :
    MulAction.stabilizer Rˣ x = ⊥ := by
  rw [eq_bot_iff]
  intro g (hg : g.val • x = x)
  ext
  rw [← sub_eq_zero, ← smul_eq_zero_iff_left hx, Units.val_one, sub_smul, hg, one_smul, sub_self]

end
