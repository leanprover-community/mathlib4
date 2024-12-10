/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.NoZeroSMulDivisors.Pi

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. Then an `R`-submodule `M` of `V` is a lattice,
if `M` is finitely generated and spans `V` as an `A`-module.

The typical use case is `A = K` is the fraction field of `R` and `V = ι → K` for some finite `ι`.
In this case there is a natural action of `GL ι K` on the type of lattices, whose stabilizer
at the standard lattice is `GL ι R`.

By taking the quotient of the type of `R`-lattices in `ι → K` by the homothety relation,
one obtains the vertices of what is called the Bruhat-Tits tree of `GL 2 K` when `ι = Fin 2`.

## Main definitions

- `Submodule.IsLattice`: An `R`-submodule `M` of `V` is a lattice, if it is finitely generated
  and its `A`-span is `V`.

-/

/-- If `M` is `A`-torsion free and `algebraMap R A` is injective, `M` is also `R`-torsion free. -/
lemma NoZeroSMulDivisors.of_algebraMap_injective' {R A M : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [NoZeroSMulDivisors A M]
    (h : Function.Injective (algebraMap R A)) :
    NoZeroSMulDivisors R M where
  eq_zero_or_eq_zero_of_smul_eq_zero hx := by
    rw [← algebraMap_smul (A := A)] at hx
    obtain (hc|hx) := eq_zero_or_eq_zero_of_smul_eq_zero hx
    · exact Or.inl <| (map_eq_zero_iff _ h).mp hc
    · exact Or.inr hx

variable {R : Type*} [CommRing R]
--variable {V : Type*} [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]

open Pointwise

namespace Submodule

/--
An `R`-submodule `M` of `V` is a lattice if it is finitely generated
and spans `V` as an `A`-module.

Note: `A` is marked as an `outParam` here. In practice this should not cause issues, since
`R` and `A` are fixed, where typically `A` is the fraction field of `R`. -/
class IsLattice (A : outParam Type*) [CommRing A] [Algebra R A]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]
    [Algebra R A] [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span A (M : Set V) = ⊤

namespace IsLattice

section

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable (M : Submodule R V)

/-- Any `R`-lattice is finite. -/
instance finite [IsLattice A M] : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg

/-- The action of `Aˣ` on `R`-submodules of `V` preserves `IsLattice`. -/
instance smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where
  fg := by
    obtain ⟨s, rfl⟩ := IsLattice.fg (M := M)
    rw [Submodule.smul_span]
    have : Finite (a • (s : Set V) : Set V) := Finite.Set.finite_image _ _
    exact Submodule.fg_span (Set.toFinite (a • (s : Set V)))
  span_eq_top := by
    rw [Submodule.coe_pointwise_smul, ← Submodule.smul_span, IsLattice.span_eq_top]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    rw [show x = a • a⁻¹ • x by simp]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial)

lemma span_basis_eq_top {κ : Type*} [Fintype κ]
    {M : Submodule R V} (b : Basis κ R M)
    [IsLattice A M] : Submodule.span A (Set.range fun i ↦ (b i).val) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : x ∈ Submodule.span A (M : Set V) := by
    rw [IsLattice.span_eq_top]
    trivial
  induction' hx using Submodule.span_induction with x hx x y _ _ hx hy a x _ hx
  · have hv : ⟨x, hx⟩ ∈ Submodule.span R (Set.range b) := Basis.mem_span b ⟨x, hx⟩
    obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun _).mp hv
    simp only [Subtype.ext_iff, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at hc
    rw [← hc]
    refine Submodule.sum_mem _ (fun i _ ↦ ?_)
    rw [← algebraMap_smul (A := A)]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span (Set.mem_range_self i)
  · simp
  · exact Submodule.add_mem _ hx hy
  · exact Submodule.smul_mem _ _ hx


end

section

/-!
## Lattices are free

In this section we prove that every lattice is a free `R`-module of rank `2` and
every such `R`-module is a lattice.
-/

variable (K : Type*) [Field K] [Algebra R K]
variable [IsDomain R] [IsPrincipalIdealRing R] [NoZeroSMulDivisors R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- Any lattice over a PID is a free `R`-module. -/
instance free (M : Submodule R V) [IsLattice K M] : Module.Free R M := by
  haveI : NoZeroSMulDivisors R V := by
    apply NoZeroSMulDivisors.of_algebraMap_injective' (A := K)
    exact NoZeroSMulDivisors.algebraMap_injective R K
  /- torsion free, finite module over a PID -/
  infer_instance

/-- Any lattice has `R`-rank equal to the `K`-rank of `V`. -/
theorem rank' [IsFractionRing R K] (M : Submodule R V) [IsLattice K M] :
    Module.rank R M = Module.rank K V := by
  let b := Module.Free.chooseBasis R M
  have hli : LinearIndependent K (fun i ↦ (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearIndependent s g hs
  have hsp : ⊤ ≤ Submodule.span K (Set.range <| fun i ↦ (b i).val) := by
    rw [span_basis_eq_top]
  let b' := Basis.mk hli hsp
  rw [rank_eq_card_basis b, ← rank_eq_card_basis b']

/-- Any `R`-lattice has rank `k` as an `R`-module. -/
lemma rank [IsFractionRing R K] {k : ℕ} (M : Submodule R (Fin k → K)) [IsLattice K M] :
    Module.rank R M = k := by
  rw [IsLattice.rank' K M]
  simp

/-- `Module.finrank` version of `IsLattice.rank`. -/
lemma finrank [IsFractionRing R K] {k : ℕ} (M : Submodule R (Fin k → K)) [IsLattice K M] :
    Module.finrank R M = k :=
  Module.finrank_eq_of_rank_eq (IsLattice.rank K M)

/-- The supremum of two lattices is a lattice. -/
instance sup (M N : Submodule R V) [IsLattice K M] [IsLattice K N] :
    IsLattice K (M ⊔ N) where
  fg := Submodule.FG.sup IsLattice.fg IsLattice.fg
  span_eq_top := by
    rw [_root_.eq_top_iff]
    trans
    · show ⊤ ≤ Submodule.span K M
      rw [IsLattice.span_eq_top (M := M)]
    · apply Submodule.span_mono
      simp

omit [IsPrincipalIdealRing R] [NoZeroSMulDivisors R K] in
lemma span_eq_top_of_rank [Module.Finite K V] [IsFractionRing R K]
    {M : Submodule R V} (h : Module.rank R M = Module.rank K V) :
    Submodule.span K (M : Set V) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' M.subtype (Submodule.ker_subtype M)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  rw [h, ← Module.finrank_eq_rank, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ x.val.val) ⊆ M := by
    rintro x ⟨a, rfl⟩
    simp
  have hcard : Fintype.card ↑s = Module.finrank K V := by simpa
  rw [_root_.eq_top_iff]
  rw [← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

omit [IsPrincipalIdealRing R] [NoZeroSMulDivisors R K] in
/-- A finitely-generated `R`-submodule of `V` that has rank the `K`-rank of `V` is
a lattice. -/
lemma of_rank [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
    (hfg : M.FG) (hr : Module.rank R M = Module.rank K V) : IsLattice K M where
  fg := hfg
  span_eq_top := span_eq_top_of_rank K hr

/-- The intersection of two lattices is a lattice. -/
theorem inf [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V)
    [IsLattice K M] [IsLattice K N] :
    IsLattice K (M ⊓ N) where
  fg := by
    have aux : M.FG := IsLattice.fg
    have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M aux
    have g : (M ⊓ N) ≤ M := inf_le_left
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le g
    have h : Module.Finite R ↥(M ⊓ N):= Module.IsNoetherian.finite R ↥(M ⊓ N)
    apply Module.Finite.iff_fg.mp
    exact h
  span_eq_top := by
    apply span_eq_top_of_rank
    have h := Submodule.rank_sup_add_rank_inf_eq M N
    rw [IsLattice.rank' K M, IsLattice.rank' K N, IsLattice.rank'] at h
    apply Cardinal.eq_of_add_eq_add_left h
    exact Module.rank_lt_aleph0 K V

end

end IsLattice

end Submodule
