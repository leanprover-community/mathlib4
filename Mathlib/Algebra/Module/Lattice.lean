/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. Then an `R`-submodule `M` of `V` is a lattice,
if `M` is finitely generated and spans `V` as an `A`-module.

The typical use case is `A = K` is the fraction field of an integral domain `R` and `V = ι → K`
for some finite `ι`. The scalar multiple a lattice by a unit in `K` is again a lattice. This gives
rise to a homothety relation.

When `R` is a DVR and `ι = Fin 2`, then by taking the quotient of the type of `R`-lattices in
`ι → K` by the homothety relation, one obtains the vertices of what is called the Bruhat-Tits tree
of `GL 2 K`.

## Main definitions

- `Submodule.IsLattice`: An `R`-submodule `M` of `V` is a lattice, if it is finitely generated
  and its `A`-span is `V`.

## Main properties

Let `R` be a PID and `A = K` its field of fractions.

- `Submodule.IsLattice.free`: Every lattice in `V` is `R`-free.
- `Basis.extendOfIsLattice`: Any `R`-basis of a lattice `M` in `V` defines a `K`-basis of `V`.
- `Submodule.IsLattice.rank`: The `R`-rank of a lattice in `V` is equal to the `K`-rank of `V`.
- `Submodule.IsLattice.inf`: The intersection of two lattices is a lattice.

## Note

In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` where the finitely
generated condition is replaced by having the discrete topology. This is for example used
for complex tori.
-/

universe u

variable {R : Type*} [CommRing R]

open Pointwise

namespace Submodule

/--
An `R`-submodule `M` of `V` is a lattice if it is finitely generated
and spans `V` as an `A`-module.

Note 1: `A` is marked as an `outParam` here. In practice this should not cause issues, since
`R` and `A` are fixed, where typically `A` is the fraction field of `R`.

Note 2: In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` where the finitely
generated condition is replaced by having the discrete topology. -/
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

lemma of_le_of_isLattice_of_fg {M N : Submodule R V} (hle : M ≤ N) [IsLattice A M]
    (hfg : N.FG) : IsLattice A N :=
  ⟨hfg, eq_top_iff.mpr <|
    le_trans (by rw [IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

/-- The supremum of two lattices is a lattice. -/
instance sup (M N : Submodule R V) [IsLattice A M] [IsLattice A N] :
    IsLattice A (M ⊔ N) :=
  of_le_of_isLattice_of_fg A le_sup_left (Submodule.FG.sup IsLattice.fg IsLattice.fg)

end

section Field

variable {K : Type*} [Field K] [Algebra R K]

lemma _root_.Submodule.span_range_eq_top_of_injective_of_rank_le {M N : Type u} [IsDomain R]
    [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N] [Module.Finite K N]
    {f : M →ₗ[R] N} (hf : Function.Injective f) (h : Module.rank K N ≤ Module.rank R M) :
    Submodule.span K (LinearMap.range f : Set N) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h)
  rw [← Module.finrank_eq_rank, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ f x.val) ⊆ (LinearMap.range f : Set N) := by
    rintro x ⟨a, rfl⟩
    simp
  rw [eq_top_iff, ← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- Any basis of an `R`-lattice in `V` defines a `K`-basis of `V`. -/
noncomputable def _root_.Basis.extendOfIsLattice [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) :
    Basis κ K V :=
  have hli : LinearIndependent K (fun i ↦ (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearIndependent s g hs
  have hsp : ⊤ ≤ span K (Set.range fun i ↦ (M.subtype ∘ b) i) := by
    rw [← Submodule.span_span_of_tower R, Set.range_comp, ← Submodule.map_span]
    simp [b.span_eq, Submodule.map_top, span_eq_top]
  Basis.mk hli hsp

@[simp]
lemma _root_.Basis.extendOfIsLattice_apply [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) (k : κ) :
    b.extendOfIsLattice K k = (b k).val := by
  simp [Basis.extendOfIsLattice]

variable [IsDomain R]

/-- A finitely-generated `R`-submodule of `V` of rank at least the `K`-rank of `V`
is a lattice. -/
lemma of_rank_le [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
    (hfg : M.FG) (hr : Module.rank K V ≤ Module.rank R M) : IsLattice K M where
  fg := hfg
  span_eq_top := by
    simpa using Submodule.span_range_eq_top_of_injective_of_rank_le M.injective_subtype hr

variable [IsPrincipalIdealRing R]

/-- Any lattice over a PID is a free `R`-module.
Note that under our conditions, `NoZeroSMulDivisors R K` simply says that `algebraMap R K` is
injective. -/
instance free [NoZeroSMulDivisors R K] (M : Submodule R V) [IsLattice K M] : Module.Free R M := by
  have := NoZeroSMulDivisors.trans_faithfulSMul R K V
  -- any torsion free finite module over a PID is free
  infer_instance

/-- Any lattice has `R`-rank equal to the `K`-rank of `V`. -/
lemma rank' [IsFractionRing R K] (M : Submodule R V) [IsLattice K M] :
    Module.rank R M = Module.rank K V := by
  let b := Module.Free.chooseBasis R M
  rw [rank_eq_card_basis b, ← rank_eq_card_basis (b.extendOfIsLattice K)]

/-- Any `R`-lattice in `ι → K` has `#ι` as `R`-rank. -/
lemma rank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι → K))
    [IsLattice K M] : Module.rank R M = Fintype.card ι := by
  rw [IsLattice.rank' K M]
  simp

/-- `Module.finrank` version of `IsLattice.rank`. -/
lemma finrank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι → K))
    [IsLattice K M] : Module.finrank R M = Fintype.card ι :=
  Module.finrank_eq_of_rank_eq (IsLattice.rank_of_pi K M)

/-- The intersection of two lattices is a lattice. -/
instance inf [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V)
    [IsLattice K M] [IsLattice K N] : IsLattice K (M ⊓ N) where
  fg := by
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [← range_subtype (M ⊓ N)]
    apply Submodule.span_range_eq_top_of_injective_of_rank_le (M ⊓ N).injective_subtype
    have h := Submodule.rank_sup_add_rank_inf_eq M N
    rw [IsLattice.rank' K M, IsLattice.rank' K N, IsLattice.rank'] at h
    rw [Cardinal.eq_of_add_eq_add_left h (Module.rank_lt_aleph0 K V)]

end Field

end IsLattice

end Submodule
