/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Finitely generated monoids and groups

We define finitely generated monoids and groups. See also `Submodule.FG` and `Module.Finite` for
finitely-generated modules.

## Main definition

* `Submonoid.FG S`, `AddSubmonoid.FG S` : A submonoid `S` is finitely generated.
* `Monoid.FG M`, `AddMonoid.FG M` : A typeclass indicating a type `M` is finitely generated as a
  monoid.
* `Subgroup.FG S`, `AddSubgroup.FG S` : A subgroup `S` is finitely generated.
* `Group.FG M`, `AddGroup.FG M` : A typeclass indicating a type `M` is finitely generated as a
  group.

-/

@[expose] public section

assert_not_exists MonoidWithZero

/-! ### Monoids and submonoids -/


open scoped Pointwise

variable {M N : Type*} [Monoid M]

/-- An additive monoid is finitely generated if there is a finite subset whose closure is the whole
additive monoid. -/
@[mk_iff]
class AddMonoid.FG (M : Type*) [AddMonoid M] : Prop where
  fg_top : ∃ S : Finset M, AddSubmonoid.closure (S : Set M) = ⊤

variable (M) in
/-- An monoid is finitely generated if there is a finite subset whose closure is the whole
monoid. -/
@[to_additive]
class Monoid.FG : Prop where
  fg_top : ∃ S : Finset M, Submonoid.closure (S : Set M) = ⊤

section Submonoid
variable [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive /-- An additive submonoid of `N` is finitely generated if it is the closure of a
finite subset of `M`. -/]
abbrev Submonoid.FG (P : Submonoid M) : Prop := Monoid.FG P

@[to_additive]
theorem Submonoid.FG.def {P : Submonoid M} (hP : P.FG) : ∃ S : Finset M, closure S = P := by
  classical
  obtain ⟨S, hS⟩ := hP
  use S.image P.subtype
  rw [Finset.coe_image, ← MonoidHom.map_mclosure, hS, ← MonoidHom.mrange_eq_map, mrange_subtype]

@[to_additive]
theorem Submonoid.fg_def {P : Submonoid M} : FG P ↔ ∃ S : Finset M, closure S = P := by
  classical
  refine ⟨Submonoid.FG.def, fun ⟨S, hS⟩ ↦ ?_⟩
  use S.preimage P.subtype P.subtype_injective.injOn
  apply Submonoid.map_injective_of_injective P.subtype_injective
  rw [MonoidHom.map_mclosure, ← Finset.coe_image, Finset.image_preimage_of_bij, hS,
    ← MonoidHom.mrange_eq_map, mrange_subtype]
  have := subset_closure.trans hS.le
  rw [← P.mrange_subtype, MonoidHom.coe_mrange] at this
  nth_rw 2 [← Set.image_preimage_eq_of_subset this]
  exact (P.subtype_injective.injOn (s := (P.subtype ⁻¹' S))).bijOn_image

/-- An equivalent expression of `Submonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubmonoid.FG` in terms of `Set.Finite` instead of
`Finset`. -/]
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ ∃ S : Set M, Submonoid.closure S = P ∧ S.Finite :=
  fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A finitely generated submonoid has a minimal generating set. -/
@[to_additive /-- A finitely generated submonoid has a minimal generating set. -/]
lemma Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) :
    ∃ S : Finset M, Minimal (fun S : Finset M ↦ closure S = P) S :=
  exists_minimal_of_wellFoundedLT _ hP.def

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
  convert (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm

@[to_additive]
theorem Submonoid.FG.bot : FG (⊥ : Submonoid M) :=
  fg_def.mpr ⟨∅, by simp⟩

@[to_additive]
theorem Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rw [fg_def] at hP hQ ⊢
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
  classical
  rw [fg_def] at hP hQ ⊢
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 ∪ singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [closure_union, hbM, hbN]

section Pi

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)] {P : ∀ i, Submonoid (M i)}

@[to_additive]
theorem Submonoid.iSup_map_mulSingle [DecidableEq ι] :
    ⨆ i, map (MonoidHom.mulSingle M i) (P i) = pi Set.univ P := by
  haveI := Fintype.ofFinite ι
  refine iSup_map_mulSingle_le.antisymm fun x hx => ?_
  rw [← Finset.noncommProd_mulSingle x]
  exact noncommProd_mem _ _ _ _ fun i _ => mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

/-- Finite product of finitely generated submonoids is finitely generated. -/
@[to_additive
/-- Finite product of finitely generated additive submonoids is finitely generated. -/]
theorem Submonoid.FG.pi (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
  classical
  simp_rw [fg_def] at hP ⊢
  haveI := Fintype.ofFinite ι
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

end Pi

end Submonoid

section Monoid

@[to_additive]
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => Submonoid.fg_def.mpr h.1, fun h => ⟨h.def⟩⟩

@[to_additive]
theorem Monoid.fg_top [Monoid.FG M] : (⊤ : Submonoid M).FG :=
  Monoid.fg_def.mp ‹_›

/-- An equivalent expression of `Monoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddMonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Monoid.fg_iff :
    Monoid.FG M ↔ ∃ S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite :=
  Monoid.fg_def.trans (⊤ : Submonoid M).fg_iff

variable (M) in
/-- A finitely generated monoid has a minimal generating set. -/
@[to_additive /-- A finitely generated monoid has a minimal generating set. -/]
lemma Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] :
    ∃ S : Finset M, Minimal (fun S ↦ Submonoid.closure (SetLike.coe S) = ⊤) S :=
  Monoid.fg_top.exists_minimal_closure_eq

theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) := by
  rw [Monoid.fg_def, AddMonoid.fg_def, Submonoid.fg_iff_add_fg, map_top]

theorem AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] :
    AddMonoid.FG M ↔ Monoid.FG (Multiplicative M) := by
  rw [Monoid.fg_def, AddMonoid.fg_def, AddSubmonoid.fg_iff_mul_fg, map_top]

instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›

instance Monoid.fg_of_addMonoid_fg {M : Type*} [AddMonoid M] [AddMonoid.FG M] :
    Monoid.FG (Multiplicative M) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›

end Monoid

@[to_additive]
theorem Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M →* M') :
    (P.map e).FG := by
  classical
    rw [fg_def] at h ⊢
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩

@[to_additive]
theorem Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M →* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
  rw [fg_def] at h ⊢
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs, MonoidHom.map_mclosure e, Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff, ← MonoidHom.coe_mrange e, ← Submonoid.closure_le, hs,
      MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top

@[to_additive (attr := simp)]
theorem Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG :=
  .rfl

@[to_additive]
theorem Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  classical
    obtain ⟨s, hs⟩ := Monoid.FG.fg_top (M := M)
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]

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
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S, S.finite_toSet, FreeMonoid.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.mrange_eq_top, ← Submonoid.closure_eq_mrange]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeMonoid.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_mclosure, hφ, FreeMonoid.closure_range_of, ← MonoidHom.mrange_eq_map]

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
  fg_def.mpr ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

@[to_additive]
instance Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r) :=
  (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)

@[to_additive]
instance Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s : Set M)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, Submonoid.closure_closure_coe_preimage]

@[to_additive]
instance Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset

/-! ### Groups and subgroups -/


variable {G H : Type*} [Group G] [AddGroup H]

variable (G) in
/-- A group is finitely generated if there is a finite subset whose closure is the whole group. -/
abbrev Group.FG : Prop := Monoid.FG G

variable (H) in
/-- An additive group is finitely generated if there is a finite subset whose closure is the whole
additive group. -/
abbrev AddGroup.FG : Prop := AddMonoid.FG H

section Subgroup

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
abbrev Subgroup.FG (P : Subgroup G) : Prop := Group.FG P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc AddSubgroup.FG

open Pointwise in
@[to_additive]
theorem Subgroup.FG.def {P : Subgroup G} (hP : P.FG) : ∃ S : Finset G, closure S = P := by
  obtain ⟨S, hS⟩ := Submonoid.FG.def hP
  refine ⟨S, ?_⟩
  rw [le_antisymm_iff, closure_le, ← toSubmonoid_le, ← hS]
  exact ⟨Submonoid.subset_closure.trans hS.le, le_closure_toSubmonoid (S : Set G)⟩

@[to_additive]
theorem Subgroup.fg_def {P : Subgroup G} : FG P ↔ ∃ S : Finset G, closure S = P := by
  classical
  refine ⟨Subgroup.FG.def, fun ⟨S, hS⟩ ↦ P.fg_iff.mpr ?_⟩
  exact ⟨S ∪ S⁻¹, by rw [← hS, closure_toSubmonoid], S.finite_toSet.union S.finite_toSet.inv⟩

/-- An equivalent expression of `Subgroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubgroup.fg` in terms of `Set.Finite` instead of
`Finset`. -/]
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ ∃ S : Set G, Subgroup.closure S = P ∧ S.Finite :=
  fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive /-- An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid. -/]
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG :=
  .rfl

theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG := by
  rw [Subgroup.fg_iff_submonoid_fg, AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg

theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG := by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]
theorem Subgroup.FG.bot : FG (⊥ : Subgroup G) :=
  Submonoid.FG.bot

@[to_additive]
theorem Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rw [fg_def] at hP hQ ⊢
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

@[to_additive]
theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  Monoid.fg_def

@[to_additive]
theorem Group.fg_top [Group.FG G] : (⊤ : Subgroup G).FG :=
  Group.fg_def.mp ‹_›

/-- An equivalent expression of `Group.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddGroup.fg` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Group.fg_iff : Group.FG G ↔ ∃ S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite :=
  Group.fg_def.trans (⊤ : Subgroup G).fg_iff

@[to_additive]
theorem Group.fg_iff' :
    Group.FG G ↔ ∃ (n : _) (S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  Group.fg_def.trans <| Subgroup.fg_def.trans
    ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive /-- An additive group is finitely generated if and only
if it is finitely generated as an additive monoid. -/]
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G :=
  .rfl

@[to_additive]
instance Monoid.fg_of_group_fg [Group.FG G] : Monoid.FG G :=
  Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]
theorem Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG :=
  (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm

theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) := by
  rw [Group.fg_def, AddGroup.fg_def, Subgroup.fg_iff_add_fg, map_top]

theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) := by
  rw [Group.fg_def, AddGroup.fg_def, AddSubgroup.fg_iff_mul_fg, map_top]

instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›

instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G := by
  exact Group.fg_iff.mpr ⟨Set.univ, Subgroup.closure_univ, Set.finite_univ⟩

@[to_additive]
theorem Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G →* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
  Group.fg_iff_monoid_fg.mpr <|
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf

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
  · rw [Group.fg_iff]
    refine fun ⟨S, hS, hS'⟩ ↦ ⟨S, hS', FreeGroup.lift Subtype.val, ?_⟩
    rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    exact Group.fg_of_surjective hφ

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
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) :=
  Subgroup.fg_def.mpr ⟨s, rfl⟩

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
instance instMonoidFG [FG M] [FG N] : FG (M × N) := by
  rw [Monoid.fg_def, ← Submonoid.top_prod_top]
  exact fg_top.prod fg_top

open Group in
/-- The product of two finitely generated groups is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive groups is finitely generated. -/]
instance instGroupFG [FG G] [FG G'] : FG (G × G') := by
  rw [Group.fg_def, ← Subgroup.top_prod_top]
  exact fg_top.prod fg_top

end Prod

namespace Pi

variable {ι : Type*} [Finite ι]

/-- Finite product of finitely generated monoids is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive monoids is finitely generated. -/]
instance instMonoidFG {M : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid.FG (M i)] :
    Monoid.FG (∀ i, M i) := by
  rw [Monoid.fg_def, ← Submonoid.pi_top Set.univ]
  exact .pi fun i ↦ Monoid.fg_top

/-- Finite product of finitely generated groups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive groups is finitely generated. -/]
instance instGroupFG {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Group.FG (G i)] :
    Group.FG (∀ i, G i) := by
  rw [Group.fg_def, ← Subgroup.pi_top Set.univ]
  exact .pi fun i ↦ Group.fg_top

end Pi

namespace AddMonoid

instance : FG ℕ where
  fg_top := ⟨{1}, by simp⟩

end AddMonoid

namespace AddGroup

instance : FG ℤ :=
  AddGroup.fg_iff.mpr ⟨{1}, by simp⟩

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
  refine ⟨_, ?_, (setOf_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOf_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOf_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 1
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [Set.mem_setOf_eq, and_imp] at ih
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
  Monoid.fg_def.mpr (Submonoid.fg_of_divisive (by simp))

/-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered monoid `M` to a
cancellative monoid `N`, the submonoid of `M` on which `f` and `g` agree is finitely generated. -/
@[to_additive /-- If `f` `g` are homomorphisms from a canonically ordered and well-quasi-ordered
additive monoid `M` to a cancellative additive monoid `N`, the submonoid of `M` on which `f` and `g`
agree is finitely generated. When `M` and `N` are `ℕ ^ k`, this is also known as a version of
**Gordan's lemma**. -/]
theorem Submonoid.fg_eqLocusM [Monoid N] [IsCancelMul N] (f g : M →* N) : (f.eqLocusM g).FG :=
  fg_of_divisive (by simp_all)

end WellQuasiOrderedLE
