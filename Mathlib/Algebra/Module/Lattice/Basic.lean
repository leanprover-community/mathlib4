/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anouk Brose, Judith Ludwig, Christian Merten, Justus Springer
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization

import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. An `R`-submodule `M` of `V` is a lattice if it is
finitely generated and every `R`-linearly independent subset of `M` is `A`-linearly independent.
If `A` is a field, this is equivalent to the `R`-rank of `M` being equal to the `A`-rank of its
`A`-span (see `Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank`).

The typical use-case of this is when `A = K` is a field with `[FaithfulSMul R K]`,
which includes e.g. `(R, K) = (ℤ, ℚ)` or `(R, K) = (ℤ, ℝ)`.

We do not require a lattice to be full. See `Submodule.IsFullLattice` for full lattices.

## Main definitions

- `Submodule.IsLattice`: an `R`-submodule `M` of `V` that is finitely generated
  and such that every `R`-linearly independent subset of `M` is `A`-linearly independent.

## Main statements

- `Submodule.IsLattice.of_fg`: over the fraction field `A = K` of a domain `R` the second axiom
  is automatic, so there lattices are exactly the finitely generated submodules.
- `Submodule.IsLattice.free`: over a PID, every lattice is `R`-free.
- `Submodule.IsLattice.inf_left`, `Submodule.IsLattice.inf_right`: over a
  Noetherian ring, the intersection of a lattice with a submodule is a lattice.

## Future work

In the fraction field setting with `V = ι → K` for finite `ι`, scaling a lattice by a unit of `K`
again gives a lattice, which yields a homothety relation. For `R` a DVR and `ι = Fin 2`, the
quotient by it is the vertex set of the Bruhat-Tits tree of `GL 2 K`.

For `R = ℤ` and `K` a normed field, `IsZLattice K L` instead asks that `L` be discrete and span
`K`, making it the topological analogue of `Submodule.IsFullLattice`; it is used for instance for
complex tori. The two notions agree in common cases, e.g. when `K = ℝ` and `V` is
finite-dimensional, but API relating them is still missing.

## References

* [S. Viguié, *Index-modules and applications*][viguie2011]
-/
@[expose] public section

open Module
open scoped Pointwise

variable {R : Type*} [CommRing R]

namespace Submodule

/-- An `R`-submodule `M` of an `A`-module `V` is a lattice if it is finitely generated and every
`R`-linearly independent subset of `M` is `A`-linearly independent. If `A is a field, this is
equivalent to the `R`-rank of `M` being equal to the `A`-rank of its `A`-span, see
`Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank`.

Note: for `R = ℤ` and `A` a normed field there is also `IsZLattice`, the analogue of
`Submodule.IsFullLattice` with discreteness in place of the two conditions here. -/
@[mk_iff]
class IsLattice (A : Type*) [CommRing A] [Algebra R A] {V : Type*} [AddCommGroup V]
    [Module R V] [Module A V] [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg (M) : M.FG
  linearIndepOn : ∀ s ⊆ (M : Set V), LinearIndepOn R id s → LinearIndepOn A id s

namespace IsLattice

section CommRing

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable (M : Submodule R V)

@[nontriviality]
theorem of_subsingleton [Nontrivial A] [Subsingleton R] : IsLattice A M :=
  have : Nontrivial R := (algebraMap R A).domain_nontrivial
  (not_subsingleton R inferInstance).elim

/-- Any `R`-independent family of vectors in a lattice is `A`-linearly independent. -/
theorem linearIndependent [IsLattice A M] {ι : Type*} {v : ι → V}
    (hv : ∀ i, v i ∈ M) (h : LinearIndependent R v) : LinearIndependent A v := by
  nontriviality R using Algebra.subsingleton R A
  rw [← linearIndepOn_id_range_iff h.injective]
  exact linearIndepOn _ (Set.range_subset_iff.mpr hv) h.linearIndepOn_id

/-- Any basis of an `R`-lattice in `V` is `A`-linearly independent. -/
theorem basis_linearIndependent [IsLattice A M] {ι : Type*} (b : Basis ι R M) :
    LinearIndependent A (fun i ↦ (b i).val) :=
  linearIndependent A M (fun i ↦ (b i).property) (b.linearIndependent.map' M.subtype M.ker_subtype)

/-- Any `R`-lattice is finite. Not an instance, since `A` cannot be inferred. -/
theorem finite [IsLattice A M] : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg A M

/-- A finitely generated submodule of a lattice is a lattice. -/
theorem mono_of_fg {M N : Submodule R V} (hle : M ≤ N) (hfg : M.FG) [IsLattice A N] :
    IsLattice A M where
  fg := hfg
  linearIndepOn s hs hli := linearIndepOn s (hs.trans hle) hli

/-- Over a Noetherian ring, any submodule of a lattice is a lattice. -/
theorem mono [IsNoetherianRing R] {M N : Submodule R V} (hle : M ≤ N) [IsLattice A N] :
    IsLattice A M :=
  mono_of_fg A hle ((fg A N).of_le hle)

/-- Over a Noetherian ring, the intersection of two submodules,
the first a lattice, is a lattice. -/
instance inf_left [IsNoetherianRing R] (M N : Submodule R V) [IsLattice A M] :
    IsLattice A (M ⊓ N) :=
  mono A inf_le_left

/-- Over a Noetherian ring, the intersection of two submodules,
the second a lattice, is a lattice. -/
instance inf_right [IsNoetherianRing R] (M N : Submodule R V) [IsLattice A N] :
    IsLattice A (M ⊓ N) :=
  mono A inf_le_right

set_option backward.isDefEq.respectTransparency false in
/-- The action of `Aˣ` on `R`-submodules of `V` preserves `IsLattice`. -/
instance smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where
  fg := by
    obtain ⟨s, rfl⟩ := IsLattice.fg A M
    exact (fg A _).map _
  linearIndepOn s hsM hs := by
    rw [coe_pointwise_smul, Set.subset_smul_set_iff] at hsM
    rw [← linearIndepOn_id_smul_set_iff a⁻¹] at hs ⊢
    exact linearIndepOn _ hsM hs

end CommRing

section Field

variable (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable (M : Submodule R V)

/-- The `R`-rank of a lattice equals the `K`-dimension of its `K`-span. -/
theorem rank_span_eq_rank [IsLattice K M] :
    Module.rank K (span K (M : Set V)) = Module.rank R M :=
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  rank_span_eq_rank_of_linearIndepOn M linearIndepOn

/-- The `R`-rank of a lattice equals the `K`-dimension of its `K`-span.
This is the finrank version of `rank_span_eq_rank`. -/
theorem finrank_span_eq_finrank [IsLattice K M] : finrank K (span K (M : Set V)) = finrank R M :=
  congr(Cardinal.toNat $(rank_span_eq_rank K M))

/-- If the `R`-span of `s` is a lattice, then the `K`-rank of `s` equals its `R`-rank. -/
theorem _root_.Set.finrank_eq_of_isLattice (s : Set V) (hs : IsLattice K (span R s)) :
    Set.finrank K s = Set.finrank R s := by
  rw [Set.finrank, Set.finrank, ← span_span_of_tower R K s]
  exact finrank_span_eq_finrank K _

/-- An `R`-module `M` is a lattice in an ambient `K`-module `V` if and only if `M`
is finitely generated, and its `R`-rank equals the `K`-dimension of its `K`-span. -/
theorem iff_fg_and_finrank_span_eq_finrank :
    IsLattice K M ↔ M.FG ∧ finrank K (span K (M : Set V)) = finrank R M := by
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  simp +contextual [isLattice_iff, finrank_span_eq_finrank_iff]

/-- The `R`-span of a finite `K`-linearly independent family is a lattice. -/
theorem span_of_linearIndependent {ι : Type*} [Finite ι] {v : ι → V}
    (hv : LinearIndependent K v) : IsLattice K (span R (Set.range v)) := by
  nontriviality R
  have := Fintype.ofFinite ι
  refine (iff_fg_and_finrank_span_eq_finrank _ _).mpr ⟨fg_span (Set.finite_range v), ?_⟩
  rw [span_span_of_tower, finrank_span_eq_card hv, finrank_span_eq_card (hv.restrict_scalars' R)]

/-- Any lattice is contained in the `R`-span of a finite `K`-linearly independent set with the
same `K`-span. In particular, every lattice is contained in a free lattice with the same `K`-span.

Note that if `R` is a PID, every lattice is free (`IsLattice.free`), so this holds trivially. -/
theorem exists_finite_linearIndepOn_le_span [IsLattice K M] :
    ∃ s : Set V, s.Finite ∧ LinearIndepOn K id s ∧ M ≤ span R s ∧
      span K s = span K (M : Set V) := by
  have := IsDomain.of_faithfulSMul R K
  have := finite K M
  obtain ⟨n, g, hg⟩ := Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, hI, a, ha, haM⟩ := exists_linearIndepOn_smul_mem_span hg
  have ha' : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr ha
  let φ : V →ₗ[R] V := (LinearMap.lsmul K V (algebraMap R K a)⁻¹).restrictScalars R
  have hM : M ≤ span R ((fun i ↦ φ (g i)) '' I) := fun m hm ↦ by
    simpa [map_span, ← Set.image_comp, Function.comp_def, φ, -algebraMap_smul,
      ← algebraMap_smul K a m, smul_smul, mul_inv_cancel₀ ha'] using
      mem_map_of_mem (f := φ ∘ₗ M.subtype) (haM ⟨m, hm⟩)
  refine ⟨_, I.toFinite.image _, ?_, hM, le_antisymm ?_ ?_⟩
  · exact .id_image <|
      (linearIndependent K M (fun i : I ↦ (g i).prop) (hI.map' M.subtype M.ker_subtype)).units_smul
        fun _ ↦ Units.mk0 _ (inv_ne_zero ha')
  · exact span_le.mpr <| Set.image_subset_iff.mpr fun i _ ↦ smul_mem _ _ (subset_span (g i).prop)
  · exact span_le.mpr <| hM.trans (span_le_restrictScalars R K _)

/-- The `K`-span of a lattice is finite-dimensional. -/
instance finiteDimensional_span [IsLattice K M] : FiniteDimensional K (span K (M : Set V)) := by
  obtain ⟨s, rfl⟩ := fg K (M := M)
  rw [span_span_of_tower]
  exact FiniteDimensional.span_finset K s

section IsPrincipalIdealRing

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Any lattice over a PID is a free `R`-module. Not an instance, since `K` cannot be inferred. -/
theorem free [IsLattice K M] : Module.Free R M := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  have := finite K M
  -- any torsion free finite module over a PID is free
  infer_instance

/-- A lattice over a PID has a basis that's `K`-linearly independent. -/
theorem exists_basis_linearIndependent [IsLattice K M] :
    ∃ b : Basis (Fin (finrank R M)) R M, LinearIndependent K (fun i ↦ (b i).val) :=
  have := free K M
  have := finite K M
  ⟨finBasis R M, basis_linearIndependent K M _⟩

end IsPrincipalIdealRing

section IsFractionRing

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K` is the field of fractions of `R`, any finitely generated `R`-submodule of `V`
is a lattice. -/
theorem of_fg {M : Submodule R V} (hM : M.FG) : IsLattice K M where
  fg := hM
  linearIndepOn _ _ := (LinearIndependent.iff_fractionRing R K).mp

/-- If `K` is the field of fractions of `R`, then a submodule of `V` is a lattice if and
only if it is finitely generated. -/
theorem iff_fg {M : Submodule R V} : IsLattice K M ↔ M.FG :=
  ⟨fun _ ↦ fg K M, of_fg K⟩

/-- If `K` is the field of fractions of `R`, the supremum of two lattices is a lattice. -/
instance sup (M N : Submodule R V) [IsLattice K M] [IsLattice K N] : IsLattice K (M ⊔ N) :=
  of_fg _ ((fg K M).sup (fg K N))

end IsFractionRing

end Field

end IsLattice

end Submodule
