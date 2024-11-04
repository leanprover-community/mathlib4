/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Pointwise.SMul
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

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : α} [Fintype (orbit M a)] :
    a ∈ fixedPoints M α ↔ Fintype.card (orbit M a) = 1 := by
  rw [Fintype.card_eq_one_iff, mem_fixedPoints]
  constructor
  · exact fun h => ⟨⟨a, mem_orbit_self _⟩, fun ⟨a, ⟨x, hx⟩⟩ => Subtype.eq <| by simp [h x, hx.symm]⟩
  · intro h x
    rcases h with ⟨⟨z, hz⟩, hz₁⟩
    calc
      x • a = z := Subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      _ = a := (Subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm

end FixedPoints

end MulAction

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `NoZeroSMulDivisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type*} [Monoid M] [NonUnitalNonAssocRing R]
    [DistribMulAction M R] (k : M) (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub, h', sub_self]

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

section Orbit

-- TODO: This proof is redoing a special case of `MulAction.IsInvariantBlock.isBlock`. Can we move
-- this lemma earlier to golf?
@[to_additive (attr := simp)]
theorem smul_orbit (g : G) (a : α) : g • orbit G a = orbit G a :=
  (smul_orbit_subset g a).antisymm <|
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ ⊆ g • orbit G a := Set.image_subset _ (smul_orbit_subset _ _)

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
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
    simp only [Submonoid.mk_smul]
    refine mem_orbit _ (⟨gv, ?_⟩ : Subgroup.map K.subtype (H.subgroupOf K))
    simpa using gp
  · rcases h with ⟨⟨gv, gp⟩, rfl⟩
    simp only [Submonoid.mk_smul]
    simp only [Subgroup.subgroupOf_map_subtype, Subgroup.mem_inf] at gp
    refine mem_orbit _ (⟨⟨gv, ?_⟩, ?_⟩ : H.subgroupOf K)
    · exact gp.2
    · simp only [Subgroup.mem_subgroupOf]
      exact gp.1

variable (G α)

/-- An action is pretransitive if and only if the quotient by `MulAction.orbitRel` is a
subsingleton. -/
@[to_additive "An additive action is pretransitive if and only if the quotient by
`AddAction.orbitRel` is a subsingleton."]
theorem pretransitive_iff_subsingleton_quotient :
    IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α) := by
  refine ⟨fun _ ↦ ⟨fun a b ↦ ?_⟩, fun _ ↦ ⟨fun a b ↦ ?_⟩⟩
  · refine Quot.inductionOn a (fun x ↦ ?_)
    exact Quot.inductionOn b (fun y ↦ Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq''.mp h

/-- If `α` is non-empty, an action is pretransitive if and only if the quotient has exactly one
element. -/
@[to_additive "If `α` is non-empty, an additive action is pretransitive if and only if the
quotient has exactly one element."]
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

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {a b : α} (h : orbitRel G α a b) :
    stabilizer G a ≃* stabilizer G b :=
  let g : G := Classical.choose h
  have hg : g • b = a := Classical.choose_spec h
  have this : stabilizer G a = (stabilizer G b).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer G b).symm

end Stabilizer

end MulAction

namespace AddAction
variable {G α : Type*} [AddGroup G] [AddAction G α]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g +ᵥ a) = (stabilizer G a).map (AddAut.conj g).toAddMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd,
    neg_add_cancel, zero_vadd, ← mem_stabilizer_iff, AddSubgroup.mem_map_equiv,
    AddAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {a b : α} (h : orbitRel G α a b) :
    stabilizer G a ≃+ stabilizer G b :=
  let g : G := Classical.choose h
  have hg : g +ᵥ b = a := Classical.choose_spec h
  have this : stabilizer G a = (stabilizer G b).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer G b).symm

end AddAction

attribute [to_additive existing] MulAction.stabilizer_smul_eq_stabilizer_map_conj
attribute [to_additive existing] MulAction.stabilizerEquivStabilizerOfOrbitRel

theorem Equiv.swap_mem_stabilizer {α : Type*} [DecidableEq α] {S : Set α} {a b : α} :
    Equiv.swap a b ∈ MulAction.stabilizer (Equiv.Perm α) S ↔ (a ∈ S ↔ b ∈ S) := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff, ← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h ↦ by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩


namespace MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions.-/
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

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove one inclusion. -/
theorem mem_stabilizer_of_finite_iff_smul_le (s : Set α) (hs : s.Finite) (g : G) :
    g ∈ stabilizer G s ↔ g • s ⊆ s := by
  haveI : Fintype s := Set.Finite.fintype hs
  haveI : Finite (g • s : Set α) := Finite.Set.finite_image ..
  haveI : Fintype (g • s : Set α) := Fintype.ofFinite _
  rw [mem_stabilizer_iff]
  constructor
  · exact Eq.subset
  · rw [← Set.toFinset_inj, ← Set.toFinset_subset_toFinset]
    intro h
    apply Finset.eq_of_subset_of_card_le h
    apply le_of_eq
    suffices (g • s).toFinset = Finset.map ⟨_, MulAction.injective g⟩ hs.toFinset by
      rw [this, Finset.card_map, Set.toFinite_toFinset]
    rw [← Finset.coe_inj]
    simp only [Set.coe_toFinset, Set.toFinite_toFinset, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.image_smul]

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove one inclusion. -/
theorem mem_stabilizer_of_finite_iff_le_smul (s : Set α) (hs : s.Finite) (g : G) :
    g ∈ stabilizer G s ↔ s ⊆ g • s := by
  rw [← @inv_mem_iff, mem_stabilizer_of_finite_iff_smul_le s hs]
  exact Set.subset_set_smul_iff.symm

end MulAction
