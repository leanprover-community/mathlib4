/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anouk Brose, Judith Ludwig, Christian Merten, Justus Springer
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. An `R`-submodule `M` of `V` is a lattice if it is
finitely generated and every `R`-linearly independent subset of `M` is `A`-linearly independent.
Equivalently, the `R`-rank of `M` equals the `A`-rank of its `A`-span (See
`Submodule.IsLattice.iff_fg_and_finrank_eq_finrank_span`).

The typical use-case of this is when `A = K` is a field with `[FaithfulSMul R K]`,
which includes e.g. `(R, K) = (ℤ, ℚ)` or `(R, K) = (ℤ, ℝ)`.

We do not require lattice to be full. See `Submodule.IsFullLattice` for full lattices.

## Main definitions

- `Submodule.IsLattice`: an `R`-submodule `M` of `V` that is finitely generated
  and such that every `R`-linearly independent subset of `M` is `A`-linearly independent.

## Main statements

- `Submodule.IsLattice.of_fg`: over the fraction field `A = K` of a domain `R` the second axiom
  is automatic, so there lattices are exactly the finitely generated submodules.
- `Submodule.IsLattice.free`: over a PID, every lattice is `R`-free.
- `Submodule.IsLattice.inf`: over a Noetherian ring, the intersection of two lattices is a lattice.

## Future work

In the fraction field setting with `V = ι → K` for finite `ι`, scaling a lattice by a unit of `K`
again gives a lattice, which yields a homothety relation. For `R` a DVR and `ι = Fin 2`, the
quotient by it is the vertex set of the Bruhat-Tits tree of `GL 2 K`.

For `R = ℤ` and `K` a normed field, `IsZLattice K L` instead asks that `L` be discrete and span
`K`, making it the topological analogue of `Submodule.IsFullLattice`; it is used for instance for
complex tori. The two definitions do not seem to admit a common generalization, but API relating
them is still missing.

## References

* [S. Viguié, *Index-modules and applications*][viguie2011]
-/
@[expose] public section

universe u v

open Module
open scoped Pointwise

variable {R : Type*} [CommRing R]

namespace Submodule

/-- An `R`-submodule `M` of an `A`-module `V` is a lattice if it is finitely generated and every
`R`-linearly independent subset of `M` is `A`-linearly independent. Equivalently, the `R`-rank of
`M` equals the `A`-rank of its `A`-span, see
`Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank`.

Note: for `R = ℤ` and `A` a normed field there is also `IsZLattice`, the analogue of
`Submodule.IsFullLattice` with discreteness in place of the two conditions here. -/
@[mk_iff]
class IsLattice (A : Type*) [CommRing A] [Algebra R A] {V : Type v} [AddCommMonoid V]
    [Module R V] [Module A V] [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  linearIndepOn : ∀ s ⊆ (M : Set V), LinearIndepOn R id s → LinearIndepOn A id s

namespace IsLattice

section CommRing

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type v} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable (M : Submodule R V)

/-- Any `R`-independent family of vectors in a lattice is `A`-linearly independent. -/
theorem linearIndependent [IsLattice A M] {ι : Type*} {v : ι → V}
    (hv : ∀ i, v i ∈ M) (h : LinearIndependent R v) : LinearIndependent A v := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R A).codomain_trivial
    exact linearIndependent_of_subsingleton
  exact (linearIndepOn_id_range_iff h.injective).mp <|
    linearIndepOn _ (Set.range_subset_iff.mpr hv) h.linearIndepOn_id

/-- Any basis of an `R`-lattice in `V` is `A`-linearly independent. -/
theorem basis_linearIndependent [IsLattice A M] {ι : Type*} (b : Basis ι R M) :
    LinearIndependent A (fun i ↦ (b i).val) :=
  linearIndependent A M (fun i ↦ (b i).2)
    (b.linearIndependent.map' M.subtype (Submodule.ker_subtype _))

/-- Any `R`-lattice is finite. Not an instance, since `A` cannot be inferred. -/
theorem finite [IsLattice A M] : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg A

theorem mono_of_fg {M N : Submodule R V} (hle : M ≤ N) (hfg : M.FG) [IsLattice A N] :
    IsLattice A M where
  fg := hfg
  linearIndepOn s hs hli := linearIndepOn s (hs.trans hle) hli

/-- Over a Noetherian ring, any submodule of a lattice is a lattice. -/
theorem mono [IsNoetherianRing R] {M N : Submodule R V} (hle : M ≤ N) [IsLattice A N] :
    IsLattice A M :=
  have := finite A N
  mono_of_fg A hle (isNoetherian_submodule.mp inferInstance M hle)

/-- Over a Noetherian ring, the intersection of two lattices is a lattice. -/
instance inf [IsNoetherianRing R] (M N : Submodule R V) [IsLattice A M] [IsLattice A N] :
    IsLattice A (M ⊓ N) :=
  mono A inf_le_left

set_option backward.isDefEq.respectTransparency false in
/-- The action of `Aˣ` on `R`-submodules of `V` preserves `IsLattice`. -/
instance smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where
  fg := by
    obtain ⟨s, rfl⟩ := IsLattice.fg A (M := M)
    rw [Submodule.smul_span]
    have : Finite (a • (s : Set V) : Set V) := Finite.Set.finite_image _ _
    exact Submodule.fg_span (Set.toFinite (a • (s : Set V)))
  linearIndepOn s hsM hs := by
    rw [coe_pointwise_smul, Set.subset_smul_set_iff] at hsM
    rw [← smul_inv_smul a s, linearIndepOn_id_smul_set_iff]
    exact linearIndepOn _ hsM ((linearIndepOn_id_smul_set_iff _ _).mpr hs)

end CommRing

section Field

variable (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
variable {V : Type v} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable (M : Submodule R V)

/-- The `R`-rank of a lattice equals the `K`-dimension of its `K`-span. -/
theorem rank_span_eq_rank [IsLattice K M] :
    Module.rank K (span K (M : Set V)) = Module.rank R M :=
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  rank_span_eq_rank_of_linearIndepOn M linearIndepOn

/-- The `R`-rank of a lattice equals the `K`-dimension
of its `K`-span. This is the finrank version of `rank_eq_rank_span`. -/
theorem finrank_span_eq_finrank [IsLattice K M] : finrank K (span K (M : Set V)) = finrank R M :=
  congrArg Cardinal.toNat (rank_span_eq_rank K M)

/-- An `R`-module `M` is a lattice in an ambient `K`-module `V` if and only if `M`
is finitely generated, and its `R`-rank equals the `K`-dimension of its `K`-span. -/
theorem iff_fg_and_finrank_span_eq_finrank :
    IsLattice K M ↔ M.FG ∧ finrank K (span K (M : Set V)) = finrank R M := by
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  rw [isLattice_iff]
  exact and_congr_right fun hfg ↦ (finrank_span_eq_finrank_iff M hfg).symm

section IsPrincipalIdealRing

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Any lattice over a PID is a free `R`-module. Not an instance, since `K` cannot be inferred. -/
theorem free (M : Submodule R V) [IsLattice K M] : Module.Free R M := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  have := finite K M
  -- any torsion free finite module over a PID is free
  infer_instance

/-- A lattice over a PID has a basis that's `K`-linearly independent. -/
theorem exists_basis_linearIndependent (M : Submodule R V) [IsLattice K M] :
    ∃ (I : Type v) (b : Basis I R M), LinearIndependent K (fun i ↦ (b i).val) := by
  have := free K M
  obtain ⟨I, b⟩ := Module.Free.exists_basis R M
  exact ⟨I, b, basis_linearIndependent K M b⟩

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
  ⟨fun _ ↦ fg K, of_fg K⟩

/-- If `K` is the field of fractions of `R`, the supremum of two lattices is a lattice. -/
instance sup (M N : Submodule R V) [IsLattice K M] [IsLattice K N] : IsLattice K (M ⊔ N) :=
  of_fg _ ((fg K).sup (fg K))

end IsFractionRing

end Field

end IsLattice

end Submodule
