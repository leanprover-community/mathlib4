/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Finitely generated semigroups, monoids and groups

We define finitely generated semigroups, monoids and groups. See also `Submodule.FG`
and `Module.Finite` for finitely-generated modules.

## Main definition

* `Subsemigroup.FG S`, `AddSubsemigroup.FG S` : A subsemigroup `S` is finitely generated.
* `Semigroup.FG M`, `AddSemigroup.FG M` : A typeclass indicating a type `M` is finitely generated
  as a semigroup.
* `Submonoid.FG S`, `AddSubmonoid.FG S` : A submonoid `S` is finitely generated.
* `Monoid.FG M`, `AddMonoid.FG M` : A typeclass indicating a type `M` is finitely generated as a
  monoid.
* `Subgroup.FG S`, `AddSubgroup.FG S` : A subgroup `S` is finitely generated.
* `Group.FG M`, `AddGroup.FG M` : A typeclass indicating a type `M` is finitely generated as a
  group.

-/

assert_not_exists MonoidWithZero

/-! ### Monoids and submonoids -/

open Pointwise

variable {M N : Type*}

section Subsemigroup
variable [Semigroup M] [Semigroup N] {P : Subsemigroup M} {Q : Subsemigroup N}

/-- A subsemigroup of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive /-- An additive subsemigroup of `M` is finitely generated if it is the closure of a
finite subset of `M`. -/]
def Subsemigroup.FG (P : Subsemigroup M) : Prop :=
  ∃ S : Finset M, Subsemigroup.closure ↑S = P

/-- An equivalent expression of `Subsemigroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubsemigroup.FG` in terms of `Set.Finite` instead
of `Finset`. -/]
theorem Subsemigroup.fg_iff (P : Subsemigroup M) :
    Subsemigroup.FG P ↔ ∃ S : Set M, Subsemigroup.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A finitely generated subsemigroup has a minimal generating set. -/
@[to_additive /-- A finitely generated subsemigroup has a minimal generating set. -/]
lemma Subsemigroup.FG.exists_minimal_closure_eq (hP : P.FG) :
    ∃ S : Finset M, Minimal (closure ·.toSet = P) S := exists_minimal_of_wellFoundedLT _ hP

theorem Subsemigroup.fg_iff_add_fg (P : Subsemigroup M) : P.FG ↔ P.toAddSubsemigroup.FG :=
  ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Subsemigroup.fg_iff _).1 h
    (AddSubsemigroup.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Subsemigroup.toAddSubsemigroup_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubsemigroup.fg_iff _).1 h
    (Subsemigroup.fg_iff _).mpr
      ⟨Additive.ofMul ⁻¹' T, by simp [← AddSubsemigroup.toSubsemigroup'_closure, hT], hf⟩⟩

theorem AddSubsemigroup.fg_iff_mul_fg {M : Type*} [AddSemigroup M] (P : AddSubsemigroup M) :
    P.FG ↔ P.toSubsemigroup.FG := by
  convert (Subsemigroup.fg_iff_add_fg (toSubsemigroup P)).symm

@[to_additive]
theorem Subsemigroup.FG.bot : FG (⊥ : Subsemigroup M) :=
  ⟨∅, by simp⟩

@[to_additive]
theorem Subsemigroup.FG.sup {Q : Subsemigroup M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
  rcases hP with ⟨s, rfl⟩
  rcases hQ with ⟨t, rfl⟩
  exact ⟨s ∪ t, by simp [closure_union]⟩

@[to_additive]
theorem Subsemigroup.FG.finset_sup {ι : Type*} (s : Finset ι) (P : ι → Subsemigroup M)
    (hP : ∀ i ∈ s, (P i).FG) : (s.sup P).FG :=
  Finset.sup_induction bot (fun _ ha _ hb => ha.sup hb) hP

@[to_additive]
theorem Subsemigroup.FG.biSup {ι : Type*} (s : Finset ι) (P : ι → Subsemigroup M)
    (hP : ∀ i ∈ s, (P i).FG) : (⨆ i ∈ s, P i).FG := by
  simpa only [Finset.sup_eq_iSup] using finset_sup s P hP

@[to_additive]
theorem Subsemigroup.FG.iSup {ι : Sort*} [Finite ι] (P : ι → Subsemigroup M) (hP : ∀ i, (P i).FG) :
    (iSup P).FG := by
  haveI := Fintype.ofFinite (PLift ι)
  simpa [iSup_plift_down] using biSup Finset.univ (P ∘ PLift.down) fun i _ => hP i.down


end Subsemigroup

section Semigroup

variable [Semigroup M]

/-- An additive semigroup is finitely generated if it is finitely generated as an additive
subsemigroup of itself. -/
@[mk_iff]
class AddSemigroup.FG (M : Type*) [AddSemigroup M] : Prop where
  fg_top : (⊤ : AddSubsemigroup M).FG

variable (M) in
/-- A semigroup is finitely generated if it is finitely generated as a subsemigroup of itself. -/
@[to_additive]
class Semigroup.FG : Prop where
  fg_top : (⊤ : Subsemigroup M).FG

@[to_additive]
theorem Semigroup.fg_def : Semigroup.FG M ↔ (⊤ : Subsemigroup M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Semigroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddSemigroup.FG` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Semigroup.fg_iff :
    Semigroup.FG M ↔ ∃ S : Set M, Subsemigroup.closure S = (⊤ : Subsemigroup M) ∧ S.Finite :=
  ⟨fun _ => (Subsemigroup.fg_iff ⊤).1 FG.fg_top, fun h => ⟨(Subsemigroup.fg_iff ⊤).2 h⟩⟩

variable (M) in
/-- A finitely generated semigroup has a minimal generating set. -/
@[to_additive /-- A finitely generated semigroup has a minimal generating set. -/]
lemma Subsemigroup.exists_minimal_closure_eq_top [Semigroup.FG M] :
    ∃ S : Finset M, Minimal (Subsemigroup.closure ·.toSet = ⊤) S :=
  Semigroup.FG.fg_top.exists_minimal_closure_eq

theorem Semigroup.fg_iff_add_fg : Semigroup.FG M ↔ AddSemigroup.FG (Additive M) where
  mp _ := ⟨(Subsemigroup.fg_iff_add_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(Subsemigroup.fg_iff_add_fg ⊤).2 h.fg_top⟩

theorem AddSemigroup.fg_iff_mul_fg {M : Type*} [AddSemigroup M] :
    AddSemigroup.FG M ↔ Semigroup.FG (Multiplicative M) where
  mp _ := ⟨(AddSubsemigroup.fg_iff_mul_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(AddSubsemigroup.fg_iff_mul_fg ⊤).2 h.fg_top⟩

instance AddSemigroup.fg_of_monoid_fg [Semigroup.FG M] : AddSemigroup.FG (Additive M) :=
  Semigroup.fg_iff_add_fg.1 ‹_›

instance Semigroup.fg_of_addSemigroup_fg {M : Type*} [AddSemigroup M] [AddSemigroup.FG M] :
    Semigroup.FG (Multiplicative M) :=
  AddSemigroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]
lemma Semigroup.fg_of_finite [Finite M] : Semigroup.FG M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Subsemigroup.closure_univ⟩⟩

end Semigroup


section Submonoid

variable [Monoid M] [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive /-- An additive submonoid of `M` is finitely generated if it is the closure of a
finite subset of `M`. -/]
def Submonoid.FG (P : Submonoid M) : Prop :=
  ∃ S : Finset M, Submonoid.closure ↑S = P

/-- An equivalent expression of `Submonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubmonoid.FG` in terms of `Set.Finite` instead of
`Finset`. -/]
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ ∃ S : Set M, Submonoid.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A finitely generated submonoid has a minimal generating set. -/
@[to_additive /-- A finitely generated submonoid has a minimal generating set. -/]
lemma Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) :
    ∃ S : Finset M, Minimal (closure ·.toSet = P) S := exists_minimal_of_wellFoundedLT _ hP

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
  ⟨∅, by simp⟩

@[to_additive]
theorem Submonoid.FG.sup {Q : Submonoid M} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
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
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 ∪ singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [closure_union, hbM, hbN]

/-- A submonoid is finitely generated if and only if it is finitely generated as a subsemigroup. -/
@[to_additive /-- An additive submonoid is finitely generated if
and only if it is finitely generated as an additive subsemigroup. -/]
theorem Submonoid.fg_iff_subsemigroup_fg (P : Submonoid M) : P.FG ↔ P.toSubsemigroup.FG := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Subsemigroup.fg_iff]
    let Q : Submonoid M :=
      ⟨Subsemigroup.closure (S ∪ {1}), Subsemigroup.mem_closure_of_mem <| Set.mem_union_right _ rfl⟩
    refine ⟨S ∪ {1}, le_antisymm ?_ ?_, S.finite_toSet.union (Set.finite_singleton 1)⟩
    · apply Subsemigroup.closure_le.mpr <| Set.union_subset subset_closure (by simp)
    · change Submonoid.closure S ≤ Q
      simp only [Set.union_singleton, closure_le, coe_set_mk, Q]
      trans insert 1 (↑S)
      · exact Set.subset_insert _ _
      · exact Subsemigroup.subset_closure
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Submonoid.closure_le, ← Submonoid.coe_toSubsemigroup, ← hS]
      exact Subsemigroup.subset_closure
    · rw [← Submonoid.toSubsemigroup_le, ← hS, Subsemigroup.closure_le]
      exact Submonoid.subset_closure

@[deprecated (since := "2025-08-28")] alias AddSubmonoid.FG.sum := AddSubmonoid.FG.prod

section Pi

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)] {P : ∀ i, Submonoid (M i)}

@[to_additive]
theorem Submonoid.iSup_map_mulSingle [DecidableEq ι] :
    ⨆ i, map (MonoidHom.mulSingle M i) (P i) = pi Set.univ P := by
  haveI := Fintype.ofFinite ι
  refine iSup_map_mulSingle_le.antisymm fun x hx => ?_
  rw [← Finset.noncommProd_mul_single x]
  exact noncommProd_mem _ _ _ _ fun i _ => mem_iSup_of_mem _ (mem_map_of_mem _ (hx i trivial))

/-- Finite product of finitely generated submonoids is finitely generated. -/
@[to_additive
/-- Finite product of finitely generated additive submonoids is finitely generated. -/]
theorem Submonoid.FG.pi (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
  classical
  haveI := Fintype.ofFinite ι
  choose s hs using hP
  refine ⟨Finset.univ.biUnion fun i => (s i).image (MonoidHom.mulSingle M i), ?_⟩
  simp_rw [Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, closure_iUnion, Finset.coe_image,
    ← MonoidHom.map_mclosure, hs, iSup_map_mulSingle]

end Pi

end Submonoid

section Monoid

variable {M : Type*} [Monoid M]

/-- An additive monoid is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
@[mk_iff]
class AddMonoid.FG (M : Type*) [AddMonoid M] : Prop where
  fg_top : (⊤ : AddSubmonoid M).FG

variable (M) in
/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive]
class Monoid.FG : Prop where
  fg_top : (⊤ : Submonoid M).FG

@[to_additive]
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Monoid.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddMonoid.FG` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Monoid.fg_iff :
    Monoid.FG M ↔ ∃ S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite :=
  ⟨fun _ => (Submonoid.fg_iff ⊤).1 FG.fg_top, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩

variable (M) in
/-- A finitely generated monoid has a minimal generating set. -/
@[to_additive /-- A finitely generated monoid has a minimal generating set. -/]
lemma Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] :
    ∃ S : Finset M, Minimal (Submonoid.closure ·.toSet = ⊤) S :=
  Monoid.FG.fg_top.exists_minimal_closure_eq

theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) where
  mp _ := ⟨(Submonoid.fg_iff_add_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.fg_top⟩

theorem AddMonoid.fg_iff_mul_fg {M : Type*} [AddMonoid M] :
    AddMonoid.FG M ↔ Monoid.FG (Multiplicative M) where
  mp _ := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 FG.fg_top⟩
  mpr h := ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.fg_top⟩

instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›

instance Monoid.fg_of_addMonoid_fg {M : Type*} [AddMonoid M] [AddMonoid.FG M] :
    Monoid.FG (Multiplicative M) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
@[to_additive]
lemma Monoid.fg_of_finite [Finite M] : Monoid.FG M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submonoid.closure_univ⟩⟩

end Monoid

section

variable [Semigroup M] {M' : Type*} [Semigroup M']

@[to_additive]
theorem Subsemigroup.FG.map {P : Subsemigroup M} (h : P.FG) (e : M →ₙ* M') :
    (P.map e).FG := by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MulHom.map_mclosure]⟩

@[to_additive]
theorem Subsemigroup.FG.map_injective {P : Subsemigroup M} (e : M →ₙ* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Subsemigroup.map_injective_of_injective he
  rw [← hs, MulHom.map_mclosure e, Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff, ← MulHom.coe_srange e, ← Subsemigroup.closure_le, hs,
      MulHom.srange_eq_map e]
  exact Subsemigroup.monotone_map le_top

@[to_additive (attr := simp)]
theorem Semigroup.fg_iff_subsemigroup_fg (N : Subsemigroup M) : Semigroup.FG N ↔ N.FG := by
  conv_rhs => rw [← N.range_subtype, MulHom.srange_eq_map]
  exact ⟨fun h ↦ h.fg_top.map (MulMemClass.subtype N),
         fun h => ⟨h.map_injective (MulMemClass.subtype N) Subtype.coe_injective⟩⟩

@[to_additive]
theorem Semigroup.fg_of_surjective {M' : Type*} [Semigroup M'] [Semigroup.FG M] (f : M →ₙ* M')
    (hf : Function.Surjective f) : Semigroup.FG M' := by
  classical
    obtain ⟨s, hs⟩ := Semigroup.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MulHom.map_mclosure, hs, ← MulHom.srange_eq_map,
      MulHom.srange_eq_top_iff_surjective]

@[to_additive]
instance Semigroup.fg_range {M' : Type*} [Semigroup M'] [Semigroup.FG M] (f : M →ₙ* M') :
    Semigroup.FG (MulHom.srange f) :=
  Semigroup.fg_of_surjective f.srangeRestrict f.srangeRestrict_surjective

@[to_additive]
instance Semigroup.closure_finset_fg (s : Finset M) :
    Semigroup.FG (Subsemigroup.closure (s : Set M)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, Subsemigroup.closure_closure_coe_preimage]

@[to_additive]
instance Semigroup.closure_finite_fg (s : Set M) [Finite s] :
    Semigroup.FG (Subsemigroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Semigroup.closure_finset_fg s.toFinset

end


section

variable {M : Type*} [Monoid M]

@[to_additive]
theorem Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M →* M') :
    (P.map e).FG := by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩

@[to_additive]
theorem Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M →* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
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
  conv_rhs => rw [← N.mrange_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h ↦ h.fg_top.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩

@[to_additive]
theorem Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  classical
    obtain ⟨s, hs⟩ := Monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]

@[to_additive]
instance Monoid.fg_range {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M') :
    Monoid.FG (MonoidHom.mrange f) :=
  Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

@[to_additive]
theorem Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG :=
  ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩

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


/-- A monoid is finitely generated if and only if it is finitely generated as a semigroup. -/
@[to_additive /-- An additive monoid is finitely generated if and only
if it is finitely generated as an additive semigroup. -/]
theorem Monoid.fg_iff_semigroup_fg : Monoid.FG M ↔ Semigroup.FG M :=
  ⟨fun h => Semigroup.fg_def.2 <| (Submonoid.fg_iff_subsemigroup_fg ⊤).1 (Monoid.fg_def.1 h),
   fun h => Monoid.fg_def.2 <| (Submonoid.fg_iff_subsemigroup_fg ⊤).2 (Semigroup.fg_def.1 h)⟩

@[to_additive]
instance Semigroup.fg_of_monoid_fg [Monoid.FG M] : Semigroup.FG M :=
  Monoid.fg_iff_semigroup_fg.1 ‹_›

end

/-! ### Groups and subgroups -/


section Subgroup
variable {G H : Type*} [Group G] [AddGroup H]

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
def Subgroup.FG (P : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.closure ↑S = P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc AddSubgroup.FG

/-- An equivalent expression of `Subgroup.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive /-- An equivalent expression of `AddSubgroup.fg` in terms of `Set.Finite` instead of
`Finset`. -/]
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ ∃ S : Set G, Subgroup.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive /-- An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid. -/]
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine ⟨S ∪ S⁻¹, ?_, S.finite_toSet.union S.finite_toSet.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure

theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG := by
  rw [Subgroup.fg_iff_submonoid_fg, AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg

theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG := by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)

@[to_additive]
theorem Subgroup.FG.bot : FG (⊥ : Subgroup G) :=
  ⟨∅, by simp⟩

@[to_additive]
theorem Subgroup.FG.sup {P Q : Subgroup G} (hP : P.FG) (hQ : Q.FG) : (P ⊔ Q).FG := by
  classical
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

variable (G H : Type*) [Group G] [AddGroup H]

/-- A group is finitely generated if it is finitely generated as a subgroup of itself. -/
class Group.FG : Prop where
  out : (⊤ : Subgroup G).FG

/-- An additive group is finitely generated if it is finitely generated as an additive subgroup of
itself. -/
class AddGroup.FG : Prop where
  out : (⊤ : AddSubgroup H).FG

attribute [to_additive] Group.FG

variable {G H}

theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Group.FG` in terms of `Set.Finite` instead of `Finset`. -/
@[to_additive
/-- An equivalent expression of `AddGroup.fg` in terms of `Set.Finite` instead of `Finset`. -/]
theorem Group.fg_iff : Group.FG G ↔ ∃ S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite :=
  ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩

@[to_additive]
theorem Group.fg_iff' :
    Group.FG G ↔ ∃ (n : _) (S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩

/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive /-- An additive group is finitely generated if and only
if it is finitely generated as an additive monoid. -/]
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G :=
  ⟨fun h => Monoid.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
    Group.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩

@[to_additive]
instance Monoid.fg_of_group_fg [Group.FG G] : Monoid.FG G :=
  Group.fg_iff_monoid_fg.1 ‹_›

@[to_additive (attr := simp)]
theorem Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG :=
  (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm

theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) :=
  ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩

theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) :=
  ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩

instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›

instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›

@[to_additive]
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G := by
  cases nonempty_fintype G
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Subgroup.closure_univ⟩⟩

@[to_additive]
theorem Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G →* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
  Group.fg_iff_monoid_fg.mpr <|
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf

@[to_additive]
instance Group.fg_range {G' : Type*} [Group G'] [Group.FG G] (f : G →* G') : Group.FG f.range :=
  Group.fg_of_surjective f.rangeRestrict_surjective

@[to_additive]
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, ← Subgroup.coe_subtype, Subgroup.closure_preimage_eq_top]

@[to_additive]
instance Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset

end Group

section Quotient

@[to_additive]
instance Con.semigroup_fg {M : Type*} [Semigroup M] [Semigroup.FG M] {c : Con M} :
    Semigroup.FG c.Quotient :=
  Semigroup.fg_of_surjective c.mkMulHom Quotient.mk''_surjective

@[to_additive]
instance Con.monoid_fg {M : Type*} [Monoid M] [Monoid.FG M] {c : Con M} : Monoid.FG c.Quotient :=
  Monoid.fg_of_surjective c.mk' c.mk'_surjective

@[to_additive]
instance QuotientGroup.fg {G : Type*} [Group G] [Group.FG G] (N : Subgroup G)
    [Subgroup.Normal N] : Group.FG <| G ⧸ N :=
  Group.fg_of_surjective <| QuotientGroup.mk'_surjective N

end Quotient

namespace Prod

variable [Monoid M] [Monoid N] {G G' : Type*} [Group G] [Group G']

open Monoid in
/-- The product of two finitely generated monoids is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive monoids is finitely generated. -/]
instance instMonoidFG [FG M] [FG N] : FG (M × N) where
  fg_top := by
    rw [← Submonoid.top_prod_top]
    exact ‹FG M›.fg_top.prod ‹FG N›.fg_top

open Group in
/-- The product of two finitely generated groups is finitely generated. -/
@[to_additive /-- The product of two finitely generated additive groups is finitely generated. -/]
instance instGroupFG [FG G] [FG G'] : FG (G × G') where
  out := by
    rw [← Subgroup.top_prod_top]
    exact ‹FG G›.out.prod ‹FG G'›.out

end Prod

namespace Pi

variable {ι : Type*} [Finite ι]

/-- Finite product of finitely generated monoids is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive monoids is finitely generated. -/]
instance instMonoidFG {M : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid.FG (M i)] :
    Monoid.FG (∀ i, M i) where
  fg_top := by
    rw [← Submonoid.pi_top Set.univ]
    exact .pi fun i => Monoid.FG.fg_top

/-- Finite product of finitely generated groups is finitely generated. -/
@[to_additive /-- Finite product of finitely generated additive groups is finitely generated. -/]
instance instGroupFG {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Group.FG (G i)] :
    Group.FG (∀ i, G i) where
  out := by
    rw [← Subgroup.pi_top Set.univ]
    exact .pi fun i => Group.FG.out

end Pi

namespace AddMonoid

instance : FG ℕ where
  fg_top := ⟨{1}, by simp⟩

end AddMonoid

namespace AddGroup

instance : FG ℤ where
  out := ⟨{1}, by simp⟩

end AddGroup
