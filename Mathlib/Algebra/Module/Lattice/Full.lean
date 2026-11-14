/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anouk Brose, Judith Ludwig, Christian Merten, Justus Springer
-/
module

public import Mathlib.Algebra.Module.Lattice.Basic

/-!
# Full lattices

A lattice in an `A`-module `V` is full if its `A`-span is all of `V`.

## Main definitions

- `Submodule.IsFullLattice`: a `Submodule.IsLattice` whose `A`-span is `V`.

## Main statements

- `Module.Basis.extendOfIsFullLattice`: an `R`-basis of a full lattice is an `A`-basis of `V`.
- `Submodule.IsFullLattice.rank`: a full lattice has `R`-rank the `A`-rank of `V`.
- `Submodule.IsFullLattice.inf`: over a fraction field, the intersection of two full lattices in a
  finite-dimensional module is again a full lattice.
-/

@[expose] public section

open Module
open scoped Pointwise

variable {R : Type*} [CommRing R]

namespace Submodule

/-- A lattice that spans `V` over `A`. -/
class IsFullLattice (A : Type*) [CommRing A] [Algebra R A] {V : Type*} [AddCommGroup V]
    [Module R V] [Module A V] [IsScalarTower R A V] (M : Submodule R V) extends IsLattice A M where
  span_eq_top : span A (M : Set V) = ⊤

namespace IsFullLattice

section CommRing

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

/-- Any basis of a full `R`-lattice in `V` defines a `A`-basis of `V`. -/
noncomputable def _root_.Module.Basis.extendOfIsFullLattice {M : Submodule R V}
    [IsFullLattice A M] {ι : Type*} (b : Basis ι R M) : Basis ι A V :=
  have hsp : ⊤ ≤ span A (Set.range fun i ↦ (b i : V)) := by
    rw [← Submodule.span_span_of_tower R, Set.range_comp', ← M.coe_subtype, ← Submodule.map_span]
    simp [span_eq_top]
  Basis.mk (IsLattice.basis_linearIndependent A M b) hsp

@[simp]
lemma _root_.Module.Basis.extendOfIsFullLattice_apply {M : Submodule R V} [IsFullLattice A M]
    {ι : Type*} (b : Basis ι R M) (k : ι) : b.extendOfIsFullLattice A k = (b k).val := by
  simp [Basis.extendOfIsFullLattice]

@[simp]
lemma _root_.Module.Basis.extendOfIsFullLattice_repr_apply {M : Submodule R V}
    [IsFullLattice A M] {ι : Type*} (b : Basis ι R M) (x : M) (i : ι) :
    (b.extendOfIsFullLattice A).repr x i = algebraMap R A (b.repr x i) := by
  suffices ((b.extendOfIsFullLattice A).repr.toLinearMap.restrictScalars R) ∘ₗ M.subtype =
      Finsupp.mapRange.linearMap (Algebra.linearMap R A) ∘ₗ b.repr.toLinearMap by
    congrm $this x i
  refine b.ext fun j ↦ ?_
  simp_rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, coe_subtype, ← b.extendOfIsFullLattice_apply A, Basis.repr_self,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

lemma _root_.Module.Basis.extendOfIsFullLattice_span {M : Submodule R V} [IsFullLattice A M]
    {ι : Type*} (b : Basis ι R M) : span R (Set.range (b.extendOfIsFullLattice A)) = M := by
  rw [show ⇑(b.extendOfIsFullLattice A) = M.subtype ∘ b from
    funext (b.extendOfIsFullLattice_apply A), Set.range_comp, ← map_span, b.span_eq, map_top,
    range_subtype]

/-- A lattice containing a full lattice is itself full. -/
theorem of_le {M N : Submodule R V} (hle : M ≤ N) [IsFullLattice A M] [IsLattice A N] :
    IsFullLattice A N where
  span_eq_top := eq_top_iff.mpr <| le_trans (by rw [IsFullLattice.span_eq_top]) <|
    span_mono (SetLike.coe_subset_coe.mpr hle)

set_option backward.isDefEq.respectTransparency false in
/-- The action of `Aˣ` on `R`-submodules of `V` preserves `IsFullLattice`. -/
instance smul (M : Submodule R V) [IsFullLattice A M] (a : Aˣ) :
    IsFullLattice A (a • M : Submodule R V) where
  span_eq_top := by
    rw [Submodule.coe_pointwise_smul, ← Submodule.smul_span, IsFullLattice.span_eq_top]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    rw [show x = a • a⁻¹ • x by simp]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial)

section map

variable {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
variable (M : Submodule R V)

/-- The image of a full lattice under an `A`-linear equivalence is a full lattice. -/
instance instMapRestrictScalars [IsFullLattice A M] (e : V ≃ₗ[A] W) :
    IsFullLattice A (M.map (e.restrictScalars R).toLinearMap) where
  span_eq_top := by
    rw [map_coe, LinearEquiv.restrictScalars_toLinearMap, LinearMap.coe_restrictScalars, span_image,
      span_eq_top, map_top, LinearEquiv.range]

/-- The preimage of a full lattice under an `A`-linear equivalence is a full lattice. -/
instance instComapRestrictScalars [IsFullLattice A M] (e : W ≃ₗ[A] V) :
    IsFullLattice A (M.comap (e.restrictScalars R).toLinearMap) where
  span_eq_top := by
    rw [comap_coe, LinearEquiv.restrictScalars_toLinearMap, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, ← e.image_symm_eq_preimage, ← LinearEquiv.coe_coe, span_image,
      span_eq_top, map_top, LinearEquiv.range]

/-- A lattice is a full lattice in its own `A`-span. -/
instance _root_.Submodule.IsLattice.isFullLattice_span_self [IsLattice A M] :
    IsFullLattice A (M.comap ((span A (M : Set V)).subtype.restrictScalars R)) where
  toIsLattice := .comap A M (injective_subtype _) fun x hx ↦ ⟨⟨x, subset_span hx⟩, rfl⟩
  span_eq_top := by
    apply map_injective_of_injective (injective_subtype (span A (M : Set V)))
    rw [map_span, map_top, range_subtype, comap_coe, LinearMap.coe_restrictScalars,
      Set.image_preimage_eq_of_subset fun x hx ↦ ⟨⟨x, subset_span hx⟩, rfl⟩]

end map

end CommRing

section Field

variable (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable (M : Submodule R V)

omit [FaithfulSMul R K] in
lemma finiteDimensional (M : Submodule R V) [IsFullLattice K M] : FiniteDimensional K V := by
  have h := IsLattice.finiteDimensional_span K M
  rw [span_eq_top] at h
  exact Finite.equiv topEquiv

/-- The `R`-span of a finite `K`-basis is a full lattice. -/
instance span_range_basis {ι : Type*} [Finite ι] (b : Basis ι K V) :
    IsFullLattice K (span R (Set.range b)) where
  toIsLattice := IsLattice.span_of_linearIndependent K b.linearIndependent
  span_eq_top := by rw [span_span_of_tower, b.span_eq]

/-- The `R`-rank of a full lattice equals the `K`-rank of the ambient module. -/
theorem rank [IsFullLattice K M] : Module.rank R M = Module.rank K V := by
  rw [← IsLattice.rank_span_eq_rank K M, span_eq_top, rank_top]

/-- The `R`-finrank of a full lattice equals the `K`-finrank of the ambient module. -/
theorem finrank [IsFullLattice K M] : finrank R M = finrank K V :=
  congrArg Cardinal.toNat (rank K M)

/-- A lattice whose `R`-rank is at least the `K`-rank of a finite-dimensional ambient module
is full. -/
theorem of_rank_le [Module.Finite K V] [IsLattice K M] (hr : Module.rank K V ≤ Module.rank R M) :
    IsFullLattice K M where
  span_eq_top := by
    refine Submodule.eq_top_of_finrank_eq (congrArg Cardinal.toNat (le_antisymm
      (Submodule.rank_le _) ?_))
    rw [IsLattice.rank_span_eq_rank K M]
    exact hr

section IsPrincipalIdealRing

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- A basis of a full lattice in `ι → K`, indexed by `ι`. -/
noncomputable def basisOfPi {ι : Type*} [Fintype ι] (M : Submodule R (ι → K))
    [IsFullLattice K M] : Basis ι R M :=
  have := IsLattice.finite K M
  have := IsLattice.free K M
  (Free.chooseBasis R M).reindex <| Fintype.equivOfCardEq <| by
    rw [← finrank_eq_card_chooseBasisIndex, IsFullLattice.finrank K M,
      Module.finrank_fintype_fun_eq_card]

end IsPrincipalIdealRing

section IsFractionRing

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K` is the field of fractions of `R`, the supremum of two full lattices is a full lattice. -/
instance sup (M N : Submodule R V) [IsFullLattice K M] [IsFullLattice K N] :
    IsFullLattice K (M ⊔ N) :=
  of_le K le_sup_left

/-- If `K` is the field of fractions of `R`, any finitely generated `R`-submodule of `V`
containing a full lattice is a full lattice. -/
theorem of_le_of_fg {M N : Submodule R V} (hle : M ≤ N) [IsFullLattice K M] (hfg : N.FG) :
    IsFullLattice K N :=
  have := IsLattice.of_fg K hfg
  of_le K hle

/-- If `K` is the field of fractions of `R`, the intersection of two full lattices in a
finite-dimensional module is a full lattice. -/
instance inf [IsDomain R] [IsNoetherianRing R] [Module.Finite K V] (M N : Submodule R V)
    [IsFullLattice K M] [IsFullLattice K N] : IsFullLattice K (M ⊓ N) := by
  refine IsFullLattice.of_rank_le K _ (le_of_eq ?_)
  have h := Submodule.rank_sup_add_rank_inf_eq M N
  rw [IsFullLattice.rank K M, IsFullLattice.rank K N, IsFullLattice.rank K (M ⊔ N)] at h
  exact (Cardinal.eq_of_add_eq_add_left h (Module.rank_lt_aleph0 K V)).symm

end IsFractionRing

end Field

end Submodule.IsFullLattice

namespace Submodule

@[deprecated (since := "2026-10-27")]
alias IsLattice.of_le_of_isLattice_of_fg := IsFullLattice.of_le_of_fg

@[deprecated (since := "2026-10-27")]
alias IsLattice.of_rank_le := IsFullLattice.of_rank_le

@[deprecated (since := "2026-10-27")]
alias IsLattice.rank' := IsFullLattice.rank

@[deprecated "Use `IsFullLattice.rank` and `rank_fun'`." (since := "2026-10-27")]
theorem IsLattice.rank_of_pi (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K] {ι : Type*}
    [Fintype ι] (M : Submodule R (ι → K)) [IsFullLattice K M] :
    Module.rank R M = Fintype.card ι := by
  rw [IsFullLattice.rank K M, rank_fun']

@[deprecated "Use `IsFullLattice.finrank` and `Module.finrank_fintype_fun_eq_card`."
  (since := "2026-10-27")]
theorem IsLattice.finrank_of_pi (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
    {ι : Type*} [Fintype ι] (M : Submodule R (ι → K)) [IsFullLattice K M] :
    finrank R M = Fintype.card ι := by
  rw [IsFullLattice.finrank K M, finrank_fintype_fun_eq_card]

@[deprecated (since := "2026-10-27")]
alias IsLattice.span_eq_top := IsFullLattice.span_eq_top

@[deprecated (since := "2026-10-27")]
alias IsLattice.inf := IsFullLattice.inf

end Submodule

@[deprecated (since := "2026-10-27")]
alias Module.Basis.extendOfIsLattice := Module.Basis.extendOfIsFullLattice

@[deprecated (since := "2026-10-27")]
alias Module.Basis.extendOfIsLattice_apply := Module.Basis.extendOfIsFullLattice_apply
