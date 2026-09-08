/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Finitely generated monoids and groups

We define finitely generated monoids and groups. See also `Submodule.FG` and `Module.Finite` for
finitely-generated modules.

## Main definition

* `IsAddFG`: A type with addition is finitely generated if there is a finite subset such that
  every element of the type can be written as a finite sum of elements from this finite subset.
* `IsMulFG`: A type with multiplication is finitely generated if there is a finite subset such that
  every element of the type can be written as a finite product of elements from this finite subset.
* `Submonoid.FG S`, `AddSubmonoid.FG S` : A submonoid `S` is finitely generated.
* `Monoid.FG M`, `AddMonoid.FG M` : A typeclass indicating a type `M` is finitely generated as a
  monoid.
* `Subgroup.FG S`, `AddSubgroup.FG S` : A subgroup `S` is finitely generated.
* `Group.FG M`, `AddGroup.FG M` : A typeclass indicating a type `M` is finitely generated as a
  group.

-/

@[expose] public section

assert_not_exists MonoidWithZero

section

open Pointwise

/-- A type with addition is finitely generated if there is a finite subset such that every
element of the type can be written as a finite sum of elements from this finite subset.

This generalizes and will eventually replace the four existing definitions
`AddSubmonoid.FG`, `AddMonoid.FG`, `AddSubgroup.FG`, and `AddGroup.FG`. -/
class IsAddFG (M : Type*) [Add M] : Prop where
  out (M) : ∃ S : Finset M, AddSubsemigroup.closure (S : Set M) = ⊤

section Mul

variable (M M' : Type*) [Mul M] [Mul M']

/-- A type with multiplication is finitely generated if there is a finite subset such that every
element of the type can be written as a finite product of elements from this finite subset.

This generalizes and will eventually replace the four existing definitions
`Submonoid.FG`, `Monoid.FG`, `Subgroup.FG`, and `Group.FG`. -/
@[to_additive existing]
class IsMulFG (M : Type*) [Mul M] : Prop where
  out (M) : ∃ S : Finset M, Subsemigroup.closure (S : Set M) = ⊤

variable {M M'}

-- We give this instance low priority to avoid slow typeclass resolutions.
@[to_additive]
instance (priority := 100) [Finite M] : IsMulFG M := by
  cases nonempty_fintype M
  exact ⟨Finset.univ, by simp⟩

@[to_additive]
theorem IsMulFG.of_surjective {F : Type*} [FunLike F M M'] [MulHomClass F M M'] (f : F)
    (hf : Function.Surjective f) [IsMulFG M] : IsMulFG M' := by
  classical
  obtain ⟨S, hS⟩ := IsMulFG.out M
  use S.image f
  rwa [Finset.coe_image, ← MulHom.coe_coe, ← MulHom.map_mclosure, hS, ← MulHom.srange_eq_map,
    MulHom.srange_eq_top_iff_surjective]

end Mul

namespace Semigroup

variable {M M' : Type*} [Mul M] [Mul M'] (f : M →ₙ* M')

@[to_additive]
theorem isMulFG_iff : IsMulFG M ↔ ∃ S : Finset M, Subsemigroup.closure (S : Set M) = ⊤ :=
  ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩

variable (M) in
@[to_additive]
theorem exists_of_isMulFG [IsMulFG M] : ∃ S : Finset M, Subsemigroup.closure (S : Set M) = ⊤ :=
  isMulFG_iff.mp ‹_›

@[to_additive]
theorem isMulFG_iff_finite : IsMulFG M ↔ ∃ S : Set M, S.Finite ∧ Subsemigroup.closure S = ⊤ := by
  rw [isMulFG_iff, ← Finset.exists_toSet]

variable (M) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG M] : ∃ S : Set M, S.Finite ∧ Subsemigroup.closure S = ⊤ :=
  isMulFG_iff_finite.mp ‹_›

end Semigroup

namespace Monoid

variable {M M' : Type*} [MulOneClass M] [MulOneClass M'] (f : M →* M')

@[to_additive]
theorem isMulFG_iff : IsMulFG M ↔ ∃ S : Finset M, Submonoid.closure (S : Set M) = ⊤ := by
  classical
  simp_rw [Semigroup.isMulFG_iff, SetLike.ext'_iff, Submonoid.closure_eq_one_union,
    Subsemigroup.coe_top, Submonoid.coe_top]
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S, by simp_all⟩, fun ⟨S, hS⟩ ↦ ⟨{1} ∪ S, ?_⟩⟩
  rw [← Set.univ_subset_iff, ← hS]
  rintro x (rfl | hx)
  · exact Subsemigroup.mem_closure_of_mem (by simp)
  · exact Subsemigroup.closure_mono (by simp) hx

variable (M) in
@[to_additive]
theorem exists_of_isMulFG [IsMulFG M] : ∃ S : Finset M, Submonoid.closure (S : Set M) = ⊤ :=
  isMulFG_iff.mp ‹_›

@[to_additive]
theorem isMulFG_iff_finite : IsMulFG M ↔ ∃ S : Set M, S.Finite ∧ Submonoid.closure S = ⊤ := by
  rw [isMulFG_iff, ← Finset.exists_toSet]

variable (M) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG M] : ∃ S : Set M, S.Finite ∧ Submonoid.closure S = ⊤ :=
  isMulFG_iff_finite.mp ‹_›

@[to_additive]
instance [IsMulFG M] : IsMulFG (MonoidHom.mrange f) :=
  .of_surjective f.mrangeRestrict (f.mrangeRestrict_surjective)

@[to_additive]
instance [IsMulFG M] [IsMulFG M'] : IsMulFG (M × M') := by
  classical
  obtain ⟨S, hS⟩ := isMulFG_iff.mp ‹IsMulFG M›
  obtain ⟨S', hS'⟩ := isMulFG_iff.mp ‹IsMulFG M'›
  rw [isMulFG_iff]
  use (S ∪ {1}) ×ˢ (S' ∪ {1})
  simp [Submonoid.closure_prod, hS, hS']

section

open Submonoid

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)]

@[to_additive]
theorem _root_.Submonoid.iSup_map_mulSingle {P : ∀ i, Submonoid (M i)} [DecidableEq ι] :
    ⨆ i, (P i).map (MonoidHom.mulSingle M i) = pi Set.univ P := by
  cases nonempty_fintype ι
  refine iSup_map_mulSingle_le.antisymm fun x hx ↦ ?_
  rw [← Finset.noncommProd_mulSingle x]
  exact noncommProd_mem _ _ _ _ fun i _ ↦ mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

@[to_additive]
instance [h : ∀ i, IsMulFG (M i)] : IsMulFG (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  simp_rw [isMulFG_iff] at h
  choose S hS using h
  rw [isMulFG_iff]
  use Finset.univ.biUnion fun i ↦ (S i).image (MonoidHom.mulSingle M i)
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hS, iSup_map_mulSingle, pi_top]

end

end Monoid

namespace Group

variable {G G' : Type*} [Group G] [Group G'] (f : G →* G')

@[to_additive]
theorem isMulFG_iff : IsMulFG G ↔ ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ := by
  classical
  exact Monoid.isMulFG_iff.trans ⟨fun ⟨S, hS⟩ ↦ ⟨S, Subgroup.closure_eq_top_of_mclosure_eq_top hS⟩,
    fun ⟨S, hS⟩ ↦ ⟨S ∪ S⁻¹, by simp [← Subgroup.closure_toSubmonoid, hS]⟩⟩

variable (G) in
@[to_additive]
theorem exists_of_isMulFG [IsMulFG G] : ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ :=
  isMulFG_iff.mp ‹_›

@[to_additive]
theorem isMulFG_iff_finite : IsMulFG G ↔ ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ := by
  rw [isMulFG_iff, ← Finset.exists_toSet]

variable (G) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG G] : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ :=
  isMulFG_iff_finite.mp ‹_›

@[to_additive]
instance [IsMulFG G] : IsMulFG f.range :=
  .of_surjective f.rangeRestrict (f.rangeRestrict_surjective)

end Group

namespace Subsemigroup

variable {M M' : Type*} [Mul M] [Mul M'] {P : Subsemigroup M} {P' : Subsemigroup M'} (f : M →ₙ* M')

@[to_additive]
theorem isMulFG_iff : IsMulFG P ↔ ∃ S : Finset M, Subsemigroup.closure (S : Set M) = P := by
  classical
  simp_rw [Semigroup.isMulFG_iff,
    ← (map_injective_of_injective (MulMemClass.subtype_injective P)).eq_iff,
    ← MulHom.srange_eq_map, range_subtype, MulHom.map_mclosure]
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S.image (MulMemClass.subtype P), by simpa⟩,
    fun ⟨S, hS⟩ ↦ ⟨S.preimage (MulMemClass.subtype P) (MulMemClass.subtype_injective P).injOn, ?_⟩⟩
  have h : ↑S ⊆ Set.range (Subtype.val : P → M) := by simp [← hS]
  simpa [Set.image_preimage_eq_of_subset h]

variable (P) in
@[to_additive]
theorem exists_of_isMulFG [IsMulFG P] : ∃ S : Finset M, Subsemigroup.closure (S : Set M) = P :=
  isMulFG_iff.mp ‹_›

@[to_additive]
theorem isMulFG_iff_finite : IsMulFG P ↔ ∃ S : Set M, S.Finite ∧ Subsemigroup.closure S = P := by
  rw [isMulFG_iff, ← Finset.exists_toSet]

variable (P) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG P] : ∃ S : Set M, S.Finite ∧ Subsemigroup.closure S = P :=
  isMulFG_iff_finite.mp ‹_›

@[to_additive (attr := simp)]
theorem isMulFG_top_iff : IsMulFG (⊤ : Subsemigroup M) ↔ IsMulFG M :=
  isMulFG_iff.trans Semigroup.isMulFG_iff.symm

@[to_additive]
instance [IsMulFG M] : IsMulFG (⊤ : Subsemigroup M) :=
  isMulFG_top_iff.mpr ‹_›

@[to_additive]
instance [IsMulFG P] : IsMulFG (P.map f) :=
  .of_surjective (f.subsemigroupMap P) (f.subsemigroupMap_surjective P)

end Subsemigroup

namespace Submonoid

variable {M M' : Type*} [MulOneClass M] [MulOneClass M'] {P : Submonoid M} {P' : Submonoid M'}
  (f : M →* M')

@[to_additive]
theorem isMulFG_iff : IsMulFG P ↔ ∃ S : Finset M, Submonoid.closure (S : Set M) = P := by
  classical
  simp_rw [Monoid.isMulFG_iff, ← (map_injective_of_injective P.subtype_injective).eq_iff,
    ← MonoidHom.mrange_eq_map, mrange_subtype, MonoidHom.map_mclosure]
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S.image P.subtype, by simpa⟩,
    fun ⟨S, hS⟩ ↦ ⟨S.preimage P.subtype P.subtype_injective.injOn, ?_⟩⟩
  have h : ↑S ⊆ Set.range (Subtype.val : P → M) := by simp [← hS]
  simpa [Set.image_preimage_eq_of_subset h]

variable (P) in
@[to_additive]
theorem exists_of_isMulFG [IsMulFG P] : ∃ S : Finset M, Submonoid.closure (S : Set M) = P :=
  isMulFG_iff.mp ‹_›

@[to_additive]
theorem isMulFG_iff_finite : IsMulFG P ↔ ∃ S : Set M, S.Finite ∧ Submonoid.closure S = P := by
  rw [isMulFG_iff, ← Finset.exists_toSet]

variable (P) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG P] : ∃ S : Set M, S.Finite ∧ Submonoid.closure S = P :=
  isMulFG_iff_finite.mp ‹_›

@[to_additive (attr := simp)]
theorem isMulFG_top_iff : IsMulFG (⊤ : Submonoid M) ↔ IsMulFG M :=
  isMulFG_iff.trans Monoid.isMulFG_iff.symm

@[to_additive]
instance [IsMulFG M] : IsMulFG (⊤ : Submonoid M) :=
  isMulFG_top_iff.mpr ‹_›

@[to_additive]
instance [IsMulFG P] : IsMulFG (P.map f) :=
  .of_surjective (f.submonoidMap P) (f.submonoidMap_surjective P)

@[to_additive]
instance [IsMulFG P] [IsMulFG P'] : IsMulFG (P.prod P') :=
  .of_surjective (P.prodEquiv P').symm (P.prodEquiv P').symm.surjective

end Submonoid

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'} (f : G →* G')

@[to_additive]
theorem isMulFG_iff : IsMulFG H ↔ ∃ S : Finset G, Subgroup.closure (S : Set G) = H := by
  classical
  simp_rw [Group.isMulFG_iff, ← Subgroup.map_subtype_inj,
    ← MonoidHom.range_eq_map, range_subtype, MonoidHom.map_closure]
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S.image H.subtype, by simpa⟩,
    fun ⟨S, hS⟩ ↦ ⟨S.preimage H.subtype H.subtype_injective.injOn, ?_⟩⟩
  have h : ↑S ⊆ Set.range (Subtype.val : H → G) := by simp [← hS]
  simpa [Set.image_preimage_eq_of_subset h]

variable (H) in
@[to_additive]
theorem exists_of_isMulFG [IsMulFG H] : ∃ S : Finset G, Subgroup.closure (S : Set G) = H :=
  isMulFG_iff.mp ‹_›

@[to_additive]
theorem isMulFG_iff_finite : IsMulFG H ↔ ∃ S : Set G, S.Finite ∧ Subgroup.closure S = H := by
  rw [isMulFG_iff, ← Finset.exists_toSet]

variable (H) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG H] : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = H :=
  isMulFG_iff_finite.mp ‹_›

@[to_additive (attr := simp)]
theorem isMulFG_top_iff : IsMulFG (⊤ : Subgroup G) ↔ IsMulFG G :=
  isMulFG_iff.trans Group.isMulFG_iff.symm

@[to_additive]
instance [IsMulFG G] : IsMulFG (⊤ : Subgroup G) :=
  isMulFG_top_iff.mpr ‹_›

@[to_additive]
instance [IsMulFG H] : IsMulFG (H.map f) :=
  .of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]
instance [IsMulFG H] [IsMulFG H'] : IsMulFG (H.prod H') :=
  .of_surjective (H.prodEquiv H').symm (H.prodEquiv H').symm.surjective

end Subgroup

end

/-! ### Monoids and submonoids -/


open scoped Pointwise

variable {M N : Type*} [Monoid M]

section Submonoid
variable [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive /-- An additive submonoid of `N` is finitely generated if it is the closure of a
finite subset of `M`. -/]
abbrev Submonoid.FG (P : Submonoid M) : Prop :=
  IsMulFG P

/-- An equivalent expression of `Submonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubmonoid.FG` in terms of `Set.Finite` instead of
`Finset`. -/]
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ ∃ S : Set M, Submonoid.closure S = P ∧ S.Finite := by
  simp_rw [Submonoid.FG, isMulFG_iff_finite, and_comm]

/-- A finitely generated submonoid has a minimal generating set. -/
@[to_additive /-- A finitely generated submonoid has a minimal generating set. -/]
lemma Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) :
    ∃ S : Finset M, Minimal (fun S : Finset M ↦ closure S = P) S :=
  exists_minimal_of_wellFoundedLT _ (isMulFG_iff.mp hP)

theorem Submonoid.fg_iff_add_fg (P : Submonoid M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Additive.ofMul ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩

theorem AddSubmonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] (P : AddSubmonoid M) :
    P.FG ↔ P.toSubmonoid.FG := by
  convert! (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm

@[to_additive]
theorem Submonoid.FG.bot : FG (⊥ : Submonoid M) :=
  isMulFG_iff.mpr ⟨∅, by simp⟩

@[to_additive]
theorem Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rw [FG, isMulFG_iff] at *
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s ∪ t, by simp [closure_union]⟩

@[to_additive]
theorem Submonoid.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι → Submonoid M)
    (hP : ∀ i ∈ s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
theorem Submonoid.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι → Submonoid M)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
theorem Submonoid.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι → Submonoid M)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]
theorem Submonoid.FG.iSup {ι : Sort*} [Finite ι] (P : ι → Submonoid M) (hP : ∀ i, (P i).FG) :
    (iSup P).FG := by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

/-- The product of two finitely generated submonoids is finitely generated. -/
@[to_additive prod
/-- The product of two finitely generated additive submonoids is finitely generated. -/]
theorem Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  infer_instance

section Pi

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)] {P : ∀ i, Submonoid (M i)}

/-- Finite product of finitely generated submonoids is finitely generated. -/
@[to_additive
/-- Finite product of finitely generated additive submonoids is finitely generated. -/]
theorem Submonoid.FG.pi (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
  classical
  have := Fintype.ofFinite ι
  simp_rw [FG, isMulFG_iff] at *
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

end Pi

end Submonoid

section Monoid

variable (M) in
/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive /-- An additive monoid is finitely generated if it is finitely generated as an
additive submonoid of itself. -/]
abbrev Monoid.FG : Prop := IsMulFG M

@[to_additive]
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  Submonoid.isMulFG_top_iff.symm

@[to_additive]
theorem Monoid.FG.fg_top [Monoid.FG M] : (⊤ : Submonoid M).FG :=
  Monoid.fg_def.mp ‹_›

/-- An equivalent expression of `Monoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddMonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Monoid.fg_iff :
    Monoid.FG M ↔ ∃ S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite := by
  simp_rw [Monoid.FG, isMulFG_iff_finite, and_comm]

variable (M) in
/-- A finitely generated monoid has a minimal generating set. -/
@[to_additive /-- A finitely generated monoid has a minimal generating set. -/]
lemma Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] :
    ∃ S : Finset M, Minimal (fun S ↦ Submonoid.closure (SetLike.coe S) = ⊤) S :=
  Monoid.FG.fg_top.exists_minimal_closure_eq

theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) := by
  rw [fg_def, AddMonoid.fg_def]
  exact Submonoid.fg_iff_add_fg ⊤

theorem AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] :
    AddMonoid.FG M ↔ Monoid.FG (Multiplicative M) := by
  rw [fg_def, Monoid.fg_def]
  exact AddSubmonoid.fg_iff_mul_fg ⊤

instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›

instance Monoid.fg_of_addMonoid_fg {M : Type*} [AddMonoid M] [AddMonoid.FG M] :
    Monoid.FG (Multiplicative M) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
@[to_additive]
lemma Monoid.fg_of_finite [Finite M] : Monoid.FG M := by
  infer_instance

end Monoid

@[to_additive]
theorem Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M →* M') :
    (P.map e).FG := by
  infer_instance

@[to_additive]
theorem Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M →* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
  rw [FG, isMulFG_iff] at h ⊢
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs, MonoidHom.map_mclosure e, Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff, ← MonoidHom.coe_mrange e, ← Submonoid.closure_le, hs,
      MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top

@[to_additive (attr := simp)]
theorem Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG := by
  rfl

@[to_additive]
theorem Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  exact IsMulFG.of_surjective f hf

@[to_additive]
instance Monoid.fg_range {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M') :
    Monoid.FG (MonoidHom.mrange f) :=
  Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

open FreeMonoid in
@[to_additive]
instance (α : Type*) [Finite α] : Monoid.FG (FreeMonoid α) :=
  Monoid.fg_iff.mpr ⟨Set.range of, closure_range_of, Set.finite_range of⟩

/-- A monoid is finitely generated iff there exists a surjective homomorphism from a `FreeMonoid`
on finitely many generators. -/
@[to_additive /-- An additive monoid is finitely generated iff there exists a surjective
homomorphism from a `FreeAddMonoid` on finitely many generators.-/]
theorem Monoid.fg_iff_exists_freeMonoid_hom_surjective :
    Monoid.FG M ↔ ∃ (S : Set M) (_ : S.Finite) (φ : FreeMonoid S →* M), Function.Surjective φ := by
  constructor
  · rw [fg_iff]
    refine fun ⟨S, hS, hfin⟩ ↦ ⟨S, hfin, FreeMonoid.lift Subtype.val, ?_⟩
    rwa [← MonoidHom.mrange_eq_top, ← Submonoid.closure_eq_mrange]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact IsMulFG.of_surjective φ hφ

/-- A monoid if finitely generated if and only if there exists a surjective homomorphism from a
`FreeMonoid` on an arbitrary finite type `α` to the monoid. -/
@[to_additive /-- An additive monoid is finitely generated iff there exists a surjective
homomorphism from a `FreeAddMonoid` on an arbitrary finite type `α` to the monoid. -/]
theorem Monoid.fg_iff_exists_freeGroup_hom_surjective_finite :
    Monoid.FG M ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeMonoid α →* M), Function.Surjective φ := by
  constructor
  · rw [fg_iff_exists_freeMonoid_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeMonoid.freeMonoidCongr e).symm,
      hφ.comp (FreeMonoid.freeMonoidCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Monoid.fg_of_surjective _ hφ

@[to_additive]
theorem Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG :=
  isMulFG_iff.mpr ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

@[to_additive]
instance Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r) :=
  (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)

@[to_additive]
instance Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s : Set M)) := by
  exact Submonoid.isMulFG_iff.mpr ⟨s, rfl⟩

@[to_additive]
instance Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset

/-! ### Groups and subgroups -/


variable {G H : Type*} [Group G] [AddGroup H]

section Subgroup

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
abbrev Subgroup.FG (P : Subgroup G) : Prop :=
  IsMulFG P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc AddSubgroup.FG

/-- An equivalent expression of `Subgroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubgroup.fg` in terms of `Set.Finite` instead of
`Finset`. -/]
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ ∃ S : Set G, Subgroup.closure S = P ∧ S.Finite := by
  simp_rw [Subgroup.FG, isMulFG_iff_finite, and_comm]

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive /-- An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid. -/]
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG := by
  rfl

theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG := by
  rw [Subgroup.fg_iff_submonoid_fg, AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg

theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG := by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]
theorem Subgroup.FG.bot : FG (⊥ : Subgroup G) :=
  isMulFG_iff.mpr ⟨∅, by simp⟩

@[to_additive]
theorem Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rw [FG, isMulFG_iff] at *
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s ∪ t, by simp [closure_union]⟩

@[to_additive]
theorem Subgroup.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι → Subgroup G)
    (hP : ∀ i ∈ s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
theorem Subgroup.FG.biSup_finset {ι : Type*} (s : Finset ι) (P : ι → Subgroup G)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
theorem Subgroup.FG.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) (P : ι → Subgroup G)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa using biSup_finset hs.toFinset P (by simpa)

@[to_additive]
theorem Subgroup.FG.iSup {ι : Sort*} [Finite ι] (P : ι → Subgroup G) (hP : ∀ i, (P i).FG) :
    (iSup P).FG := by
  simpa [iSup_plift_down] using biSup Set.finite_univ (P ∘ PLift.down) fun i _ => hP i.down

/-- The product of two finitely generated subgroups is finitely generated. -/
@[to_additive prod
/-- The product of two finitely generated additive subgroups is finitely generated. -/]
theorem Subgroup.FG.prod {G' : Type*} [Group G'] {P : Subgroup G} {Q : Subgroup G'}
    (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  rw [fg_iff_submonoid_fg] at *
  exact hP.prod hQ

/-- Finite product of finitely generated subgroups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive subgroups is finitely generated. -/]
theorem Subgroup.FG.pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    {P : ∀ i, Subgroup (G i)} (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
  simp_rw [fg_iff_submonoid_fg] at *
  exact .pi hP

end Subgroup

section Group

variable (G H)

/-- A group is finitely generated if it is finitely generated as a subgroup of itself. -/
@[to_additive /-- An additive group is finitely generated if it is finitely generated as an additive
subgroup of itself. -/]
abbrev Group.FG : Prop :=
  IsMulFG G

variable {G H}

@[to_additive]
theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  Subgroup.isMulFG_top_iff.symm

/-- An equivalent expression of `Group.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddGroup.fg` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Group.fg_iff :
    Group.FG G ↔ ∃ S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite := by
  simp_rw [Group.FG, isMulFG_iff_finite, and_comm]

@[to_additive]
theorem Group.fg_iff' :
    Group.FG G ↔ ∃ (n : _) (S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  isMulFG_iff.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive /-- An additive group is finitely generated if and only
if it is finitely generated as an additive monoid. -/]
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G := by
  rfl

@[to_additive]
instance Monoid.fg_of_group_fg [Group.FG G] : Monoid.FG G :=
  Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]
theorem Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG := by
  rfl

theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) := by
  rw [Group.fg_def, AddGroup.fg_def]
  exact Subgroup.fg_iff_add_fg ⊤

theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) := by
  rw [fg_def, Group.fg_def]
  exact AddSubgroup.fg_iff_mul_fg ⊤

instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›

instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G := by
  infer_instance

@[to_additive]
theorem Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G →* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
  IsMulFG.of_surjective f hf

open FreeGroup in
@[to_additive]
instance (α : Type*) [Finite α] : Group.FG (FreeGroup α) :=
  Group.fg_iff.mpr ⟨Set.range of, closure_range_of α, Set.finite_range of⟩

/-- A group is finitely generated iff there exists a surjective homomorphism from a `FreeGroup`
on finitely many generators. -/
@[to_additive /-- An additive group is finitely generated iff there exists a surjective homomorphism
from a `FreeAddGroup` on finitely many generators. -/]
theorem Group.fg_iff_exists_freeGroup_hom_surjective :
    Group.FG G ↔ ∃ (S : Set G) (_ : S.Finite) (φ : FreeGroup S →* G), Function.Surjective φ := by
  constructor
  · rw [fg_iff]
    refine fun ⟨S, hS, hfin⟩ ↦ ⟨S, hfin, FreeGroup.lift Subtype.val, ?_⟩
    rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact IsMulFG.of_surjective φ hφ

/-- A group if finitely generated if and only if there exists a surjective homomorphism from a
`FreeGroup` on an arbitrary finite type `α` to the group. -/
@[to_additive /-- An additive group is finitely generated iff there exists a surjective homomorphism
from a `FreeAddGroup` on an arbitrary finite type `α` to the group. -/]
theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ := by
  constructor
  · rw [fg_iff_exists_freeGroup_hom_surjective]
    intro ⟨S, hS, φ, hφ⟩
    obtain ⟨n, ⟨e⟩⟩ := hS.exists_equiv_fin S
    exact ⟨Fin n, inferInstance, φ.comp (FreeGroup.freeGroupCongr e).symm,
      hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩
  · intro ⟨α, _, φ, hφ⟩
    exact Group.fg_of_surjective hφ

@[to_additive]
instance Group.fg_range {G' : Type*} [Group G'] [Group.FG G] (f : G →* G') : Group.FG f.range :=
  Group.fg_of_surjective f.rangeRestrict_surjective

@[to_additive]
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) := by
  exact Subgroup.isMulFG_iff.mpr ⟨s, rfl⟩

@[to_additive]
instance Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset

end Group

section QuotientGroup

@[to_additive]
instance QuotientGroup.fg [Group.FG G] (N : Subgroup G) [Subgroup.Normal N] : Group.FG <| G ⧸ N :=
  Group.fg_of_surjective <| QuotientGroup.mk'_surjective N

end QuotientGroup

namespace Prod

variable [Monoid N] {G' : Type*} [Group G']

open Monoid in
/-- The product of two finitely generated monoids is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive monoids is finitely generated. -/]
instance instMonoidFG [FG M] [FG N] : FG (M × N) :=
  inferInstance

open Group in
/-- The product of two finitely generated groups is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive groups is finitely generated. -/]
instance instGroupFG [FG G] [FG G'] : FG (G × G') :=
  inferInstance

end Prod

namespace Pi

variable {ι : Type*} [Finite ι]

/-- Finite product of finitely generated monoids is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive monoids is finitely generated. -/]
instance instMonoidFG {M : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid.FG (M i)] :
    Monoid.FG (∀ i, M i) :=
  inferInstance

/-- Finite product of finitely generated groups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive groups is finitely generated. -/]
instance instGroupFG {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Group.FG (G i)] :
    Group.FG (∀ i, G i) :=
  inferInstance

end Pi

namespace AddMonoid

instance : FG ℕ :=
  isAddFG_iff.mpr ⟨{1}, by simp⟩

end AddMonoid

namespace AddGroup

instance : FG ℤ :=
  isAddFG_iff.mpr ⟨{1}, by simp⟩

end AddGroup

section WellQuasiOrderedLE

variable {M N : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M]
  [IsOrderedCancelMonoid M] [CanonicallyOrderedMul M]

/-- In a canonically ordered and well-quasi-ordered monoid, any divisive submonoid is finitely
generated. -/
@[to_additive fg_of_subtractive /-- In a canonically ordered and well-quasi-ordered additive monoid
(typical example is `ℕ ^ k`), any subtractive submonoid is finitely generated. -/]
theorem Submonoid.fg_of_divisive {P : Submonoid M} (hP : ∀ x ∈ P, ∀ y, x * y ∈ P → y ∈ P) :
    P.FG := by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x ∈ P ∧ x ≠ 1 }
  rw [fg_iff]
  refine ⟨_, ?_, (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOfPred_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOfPred_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 1
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [Set.mem_ofPred_eq, and_imp] at ih
    by_cases hy₃ : Minimal (· ∈ { x | x ∈ P ∧ x ≠ 1 }) y
    · exact mem_closure_of_mem hy₃
    rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
    rcases exists_mul_of_le hz₁.le with ⟨y, rfl⟩
    apply mul_mem
    · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge
    apply ih
    · exact hP _ hz₂ _ hy₁
    · exact (one_lt_of_lt_mul_right hz₁).ne.symm
    · exact le_mul_self
    · rw [mul_le_iff_le_one_left']
      exact (one_lt_of_ne_one hz₃).not_ge

/-- A canonically ordered and well-quasi-ordered monoid must be finitely generated. -/
@[to_additive /-- A canonically ordered and well-quasi-ordered additive monoid must be finitely
generated. -/]
theorem CommMonoid.fg_of_wellQuasiOrderedLE : Monoid.FG M :=
  Submonoid.isMulFG_top_iff.mp (Submonoid.fg_of_divisive (by simp))

/-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered monoid `M` to a
cancellative monoid `N`, the submonoid of `M` on which `f` and `g` agree is finitely generated. -/
@[to_additive /-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered
additive monoid `M` to a cancellative additive monoid `N`, the submonoid of `M` on which `f` and `g`
agree is finitely generated. When `M` and `N` are `ℕ ^ k`, this is also known as a version of
**Gordan's lemma**. -/]
theorem Submonoid.fg_eqLocusM [Monoid N] [IsCancelMul N] (f g : M →* N) : (f.eqLocusM g).FG :=
  fg_of_divisive (by simp_all)

end WellQuasiOrderedLE
