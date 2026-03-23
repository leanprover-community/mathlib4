/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
/-!

# The Lie algebra `sl₂` and its representations

The Lie algebra `sl₂` is the unique simple Lie algebra of minimal rank, 1, and as such occupies a
distinguished position in the general theory. This file provides some basic definitions and results
about `sl₂`.

## Main definitions:
* `IsSl2Triple`: a structure representing a triple of elements in a Lie algebra which satisfy the
  standard relations for `sl₂`.
* `IsSl2Triple.HasPrimitiveVectorWith`: a structure representing a primitive vector in a
  representation of a Lie algebra relative to a distinguished `sl₂` triple.
* `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`: the eigenvalue of a primitive vector must be a
  natural number if the representation is finite-dimensional.

-/

@[expose] public section

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule Module Set

variable {L} in
/-- An `sl₂` triple within a Lie ring `L` is a triple of elements `h`, `e`, `f` obeying relations
which ensure that the Lie subalgebra they generate is equivalent to `sl₂`. -/
structure IsSl2Triple (h e f : L) : Prop where
  h_ne_zero : h ≠ 0
  lie_e_f : ⁅e, f⁆ = h
  lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
  lie_h_f_nsmul : ⁅h, f⁆ = -(2 • f)

namespace IsSl2Triple

variable {L M}
variable {h e f : L}

lemma symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where
  h_ne_zero := by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]

@[simp] lemma symm_iff : IsSl2Triple (-h) f e ↔ IsSl2Triple h e f :=
  ⟨fun t ↦ neg_neg h ▸ t.symm, symm⟩

lemma lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]

lemma lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h, f⁆ = -((2 : R) • f) := by
  simp [t.lie_h_f_nsmul, two_smul]

lemma e_ne_zero (t : IsSl2Triple h e f) : e ≠ 0 := by
  have := t.h_ne_zero
  contrapose! this
  simpa [this] using t.lie_e_f.symm

lemma f_ne_zero (t : IsSl2Triple h e f) : f ≠ 0 := by
  have := t.h_ne_zero
  contrapose! this
  simpa [this] using t.lie_e_f.symm

variable {R}

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a vector is said to be
primitive if it is a simultaneous eigenvector for the action of both `h` and `e`, and the eigenvalue
for `e` is zero. -/
structure HasPrimitiveVectorWith (t : IsSl2Triple h e f) (m : M) (μ : R) : Prop where
  ne_zero : m ≠ 0
  lie_h : ⁅h, m⁆ = μ • m
  lie_e : ⁅e, m⁆ = 0

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a simultaneous
eigenvector for the action of both `h` and `e` necessarily has eigenvalue zero for `e`. -/
lemma HasPrimitiveVectorWith.mk' [IsAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
    (hm : m ≠ 0) (hm' : ⁅h, m⁆ = μ • m) (he : ⁅e, m⁆ = ρ • m) :
    HasPrimitiveVectorWith t m μ where
  ne_zero := hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie, ← t.lie_h_e_nsmul, lie_lie, hm', lie_smul, he, lie_smul, hm',
      smul_smul, smul_smul, mul_comm ρ μ, sub_self]

variable (R) in
open Submodule in
/-- The subalgebra associated to an `sl₂` triple. -/
def toLieSubalgebra (t : IsSl2Triple h e f) :
    LieSubalgebra R L where
  __ := span R {e, f, h}
  lie_mem' {x y} hx hy := by
    simp only [carrier_eq_coe, SetLike.mem_coe] at hx hy ⊢
    induction hx using span_induction with
    | zero => simp
    | add u v hu hv hu' hv' => simpa only [add_lie] using add_mem hu' hv'
    | smul t u hu hu' => simpa only [smul_lie] using smul_mem _ t hu'
    | mem u hu =>
      induction hy using span_induction with
      | zero => simp
      | add u v hu hv hu' hv' => simpa only [lie_add] using add_mem hu' hv'
      | smul t u hv hv' => simpa only [lie_smul] using smul_mem _ t hv'
      | mem v hv =>
        push _ ∈ _ at hu hv
        rcases hu with rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl <;> (try simp only [lie_self, zero_mem])
        · rw [t.lie_e_f]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_e_nsmul, neg_mem_iff]
          apply nsmul_mem <| subset_span _
          simp
        · rw [← lie_skew, t.lie_e_f, neg_mem_iff]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_f_nsmul, neg_neg]
          apply nsmul_mem <| subset_span _
          simp
        · rw [t.lie_h_e_nsmul]
          apply nsmul_mem <| subset_span _
          simp
        · rw [t.lie_h_f_nsmul, neg_mem_iff]
          apply nsmul_mem <| subset_span _
          simp

lemma mem_toLieSubalgebra_iff {x : L} {t : IsSl2Triple h e f} :
    x ∈ t.toLieSubalgebra R ↔ ∃ c₁ c₂ c₃ : R, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp_rw [t.lie_e_f, toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

namespace HasPrimitiveVectorWith

variable {m : M} {μ : R} {t : IsSl2Triple h e f}
local notation "ψ " n => ((toEnd R L M f) ^ n) m

-- Although this is true by definition, we include this lemma (and the assumption) to mirror the API
-- for `lie_h_pow_toEnd_f` and `lie_e_pow_succ_toEnd_f`.
set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma lie_f_pow_toEnd_f (P : HasPrimitiveVectorWith t m μ) (n : ℕ) :
    ⁅f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

variable (P : HasPrimitiveVectorWith t m μ)
include P

lemma lie_h_pow_toEnd_f (n : ℕ) :
    ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, t.lie_lie_smul_f R, ← neg_smul, ih, lie_smul, smul_lie, ← add_smul]
    congr
    ring

lemma lie_e_pow_succ_toEnd_f (n : ℕ) :
    ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, Module.End.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie e, t.lie_e_f,
      lie_h_pow_toEnd_f P, ih, lie_smul, lie_f_pow_toEnd_f P, ← add_smul,
      Nat.cast_add, Nat.cast_one]
    congr
    ring

/-- The eigenvalue of a primitive vector must be a natural number if the representation is
finite-dimensional. -/
lemma exists_nat [IsNoetherian R M] [IsTorsionFree R M] [IsDomain R] [CharZero R] :
    ∃ n : ℕ, μ = n := by
  suffices ∃ n : ℕ, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂, lie_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_left <| Nat.cast_add_one_ne_zero n
  have hs : (range <| fun (n : ℕ) ↦ μ - 2 * n).Infinite := by
    rw [infinite_range_iff (fun n m ↦ by simp)]; infer_instance
  by_contra! contra
  exact hs ((toEnd R L M h).eigenvectors_linearIndependent
    {μ - 2 * n | n : ℕ}
    (fun ⟨s, hs⟩ ↦ ψ Classical.choose hs)
    (fun ⟨r, hr⟩ ↦ by simp [lie_h_pow_toEnd_f P, Classical.choose_spec hr, contra,
      Module.End.hasEigenvector_iff])).finite

lemma pow_toEnd_f_ne_zero_of_eq_nat [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {n : ℕ} (hn : μ = n) {i} (hi : i ≤ n) : (ψ i) ≠ 0 := by
  intro H
  induction i
  · exact P.ne_zero (by simpa using H)
  · next i IH =>
    have : ((i + 1) * (n - i) : ℤ) • (toEnd R L M f ^ i) m = 0 := by
      have := congr_arg (⁅e, ·⁆) H
      simpa [← Int.cast_smul_eq_zsmul R, P.lie_e_pow_succ_toEnd_f, hn] using this
    rw [← Int.cast_smul_eq_zsmul R, smul_eq_zero, Int.cast_eq_zero, mul_eq_zero, sub_eq_zero,
      Nat.cast_inj, ← @Nat.cast_one ℤ, ← Nat.cast_add, Nat.cast_eq_zero] at this
    simp only [add_eq_zero, one_ne_zero, and_false, false_or] at this
    exact (hi.trans_eq (this.resolve_right (IH (i.le_succ.trans hi)))).not_gt i.lt_succ_self

lemma pow_toEnd_f_eq_zero_of_eq_nat [IsDomain R] [CharZero R] [IsNoetherian R M] [IsTorsionFree R M]
    {n : ℕ} (hn : μ = n) : (ψ (n + 1)) = 0 := by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : ℤ) < m + 2 * (n + 1) := by lia
  exact this.ne (Int.cast_injective (α := R) <| by simpa [sub_eq_iff_eq_add] using hm)

end HasPrimitiveVectorWith

variable {m : M} {μ : R}
local notation "φ " n => ((toEnd R L M e) ^ n) m

lemma lie_e_pow_toEnd_e (n : ℕ) :
    ⁅e, φ n⁆ = φ (n + 1) := by
  simp [pow_succ']

lemma lie_h_pow_toEnd_e (t : IsSl2Triple h e f)
    (hm : ⁅h, m⁆ = μ • m) (n : ℕ) :
    ⁅h, φ n⁆ = (μ + 2 * n) • φ n := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, IsSl2Triple.lie_h_e_smul R t, smul_lie, ih, lie_smul, ← add_smul]
    congr 1
    ring

section ComplexIrreducible

variable {L : Type*} (M : Type*) [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
variable {h e f : L} (t : IsSl2Triple h e f)

-- ℂ is algebraically closed and M fin-dim so h has eigenvalue μ and eigen-vector m in M.
-- e acting on m raises the eigenvalue of m
-- this must stop at some n otherwise the span would be of infinite dimension
lemma exists_primitiveVector (t : IsSl2Triple h e f)
    [FiniteDimensional ℂ M] [Nontrivial M] :
    ∃ (μ : ℂ) (m : M), m ≠ 0 ∧ t.HasPrimitiveVectorWith m μ := by
  -- Get an eigenvalue μ₀ and eigenvector m₀ for h.
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (toEnd ℂ L M h)
  obtain ⟨m₀, hm₀⟩ := hμ₀.exists_hasEigenvector
  have h_m₀_ne : m₀ ≠ 0 := by
    exact hm₀.2
  let evals : ℕ → ℂ := fun n ↦ μ₀ + 2 * (n : ℂ)
  let e_vecs : ℕ → M := fun n ↦ ((toEnd ℂ L M e)^n) m₀
  -- prove that e_vecs vanishes at some k
  have e_exists_k_zero : ∃ (k : Nat), k ≠ 0 ∧ ((toEnd ℂ L M e)^k) m₀ = 0  := by
    by_contra! contra
    have h_indep :=
      Module.End.eigenvectors_linearIndependent
      (toEnd ℂ L M h)
      (Set.range evals)
      (fun ⟨μ, hμ⟩ ↦ e_vecs (Classical.choose hμ))
      (by
        rintro ⟨μ, hμ⟩
        dsimp only
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        let v := e_vecs (Classical.choose hμ)
        --obtain the n such that μ = μ₀ + 2n and v = e^n m₀
        let n := Classical.choose hμ
        have h_n_def : Classical.choose hμ = n := by rfl
        have h_μ_μ0 : μ₀ + 2 * (n : ℂ) = μ := Classical.choose_spec hμ
        -- prove that v = e_vecs (Classical.choose hμ) is the eigen vector for μ
        have h_v_μ : ⁅h, v⁆ = μ•v := by
          unfold v e_vecs
          have h_lie := t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n
          rw [h_μ_μ0] at h_lie
          unfold n at h_lie
          exact h_lie
        -- prove that v ≠ 0
        have h_v_ne : v ≠ 0 := by
          by_cases h_n : n = 0
          · unfold v
            rw [h_n_def, h_n]
            simp [e_vecs]
            push_neg
            exact h_m₀_ne
          · apply contra
            exact h_n
        exact ⟨h_v_μ,h_v_ne⟩
      )
    have h_inj : Function.Injective evals := by
      intro a b hab
      dsimp only [evals] at hab
      simp_all only [zero_lt_one, End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, ne_eq, add_right_inj,
        mul_eq_mul_left_iff, Nat.cast_inj, OfNat.ofNat_ne_zero, or_false, evals, e_vecs]
    have h_infty : (Set.range evals).Infinite := Set.infinite_range_of_injective h_inj
    have := h_indep.finite
    exact h_infty (Set.toFinite _)
  -- use the well-ordering principle of ℕ to find the primitive vector
  have h_exists_zero : ∃ (n : ℕ), e_vecs n = 0 := by
      rcases e_exists_k_zero with ⟨k, _, hk⟩
      exact ⟨k, hk⟩
  classical
  let N := Nat.find h_exists_zero
  have hN_zero : e_vecs N = 0 := Nat.find_spec h_exists_zero
  have hN_min : ∀ m < N, e_vecs m ≠ 0 := fun m hm ↦ Nat.find_min h_exists_zero hm
  -- verify that N-1 corresponds to the primitive vector
  let n_prim := N - 1
  let m_prim := e_vecs n_prim
  let μ_prim := evals n_prim
  have : n_prim < N := by simp_all only [zero_lt_one, End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, ne_eq,
    Nat.exists_ne_zero, Nat.lt_find_iff, Std.le_refl, not_false_eq_true, implies_true, tsub_lt_self_iff,
    nonpos_iff_eq_zero, pow_zero, End.one_apply, and_self, e_vecs, N, n_prim]

  have m_prim_ne : m_prim ≠ 0 := hN_min n_prim this
  have m_prim_eq : t.HasPrimitiveVectorWith m_prim μ_prim := by
    refine ⟨m_prim_ne, ?_, ?_⟩
    · dsimp only [m_prim, μ_prim, evals, e_vecs]
      exact t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n_prim
    · simp only [m_prim, e_vecs]
      have h_eq : n_prim + 1 = N := by omega
      rw [lie_e_pow_toEnd_e n_prim, h_eq]
      exact hN_zero
  exact ⟨μ_prim, m_prim, m_prim_ne, m_prim_eq⟩

/-- The `ℂ`-span of the f-tower `{f^k(m) | k ∈ ℕ}` for a primitive vector `m`. -/
def fTowerSubmodule (t : IsSl2Triple h e f)
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    Submodule ℂ M :=
    Submodule.span ℂ (Set.range (fun i : ℕ => ((toEnd ℂ L M f) ^ i) m))

-- f-tower invariant under the Lie action of h.
lemma fTowerSubmodule_lie_h_mem
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) -- m is the primitive vector with eigenvalue μ
    {v : M} (hv : v ∈ fTowerSubmodule M t P) :
    ⁅h, v⁆ ∈ fTowerSubmodule M t P := by
  unfold fTowerSubmodule
  induction hv using Submodule.span_induction with
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [lie_add] using add_mem ihx ihy
    | smul t x hx hx' => simpa only [lie_smul] using Submodule.smul_mem _ t hx'
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      dsimp
      rw [P.lie_h_pow_toEnd_f]
      apply SMulMemClass.smul_mem
      apply Submodule.mem_span_of_mem
      simp_all only [mem_range, exists_apply_eq_apply]

-- f-tower invariant under the Lie action of f.
lemma fTowerSubmodule_lie_f_mem
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    {v : M} (hv : v ∈ fTowerSubmodule M t P) :
    ⁅f, v⁆ ∈ fTowerSubmodule M t P := by
  unfold fTowerSubmodule
  induction hv using Submodule.span_induction with
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [lie_add] using add_mem ihx ihy
    | smul t x hx hx' => simpa only [lie_smul] using Submodule.smul_mem _ t hx'
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      dsimp
      rw [P.lie_f_pow_toEnd_f]
      apply Submodule.mem_span_of_mem --⁅f, v⁆ ∈ basis → ⁅f, v⁆ ∈ span
      simp_all only [mem_range, exists_apply_eq_apply]

-- f-tower invariant under the Lie action of e.
lemma fTowerSubmodule_lie_e_mem
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    {v : M} (hv : v ∈ fTowerSubmodule M t P) :
    ⁅e, v⁆ ∈ fTowerSubmodule M t P := by
  unfold fTowerSubmodule
  induction hv using Submodule.span_induction with
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [lie_add] using add_mem ihx ihy
    | smul t x hx hx' => simpa only [lie_smul] using Submodule.smul_mem _ t hx'
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      dsimp
      cases n
      · simp_all only [pow_zero, End.one_apply]
        rw [P.lie_e]
        simp_all only [zero_mem]
      · rw [P.lie_e_pow_succ_toEnd_f]
        apply SMulMemClass.smul_mem
        apply Submodule.mem_span_of_mem
        simp_all only [mem_range, exists_apply_eq_apply]

-- f-tower invariant under sl₂ℂ
-- i.e. f-tower invariant under all of L when L is generated by the sl₂ triple.
lemma fTowerSubmodule_lie_mem
    (hL : t.toLieSubalgebra ℂ = ⊤)
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    (x : L) {v : M} (hv : v ∈ fTowerSubmodule M t P) :
    ⁅x, v⁆ ∈ fTowerSubmodule M t P := by
  have hx_mem : x ∈ t.toLieSubalgebra ℂ := by
    rw[hL]
    simp
  rw [mem_toLieSubalgebra_iff] at hx_mem
  obtain ⟨c₁,c₂,c₃,hx_eq⟩ := hx_mem
  rw [hx_eq]
  simp only [add_lie,smul_lie]
  rw [t.lie_e_f]
  apply add_mem
  · apply add_mem
    · apply Submodule.smul_mem
      exact fTowerSubmodule_lie_e_mem M t P hv
    · apply Submodule.smul_mem
      exact fTowerSubmodule_lie_f_mem M t P hv
  · apply Submodule.smul_mem
    exact fTowerSubmodule_lie_h_mem M t P hv

/-- The `fTowerSubmodule` equipped with the structure of a Lie submodule. -/
def fTowerLieSubmodule (hL : t.toLieSubalgebra ℂ = ⊤)
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    LieSubmodule ℂ L M :=
  {
    fTowerSubmodule M t P with
    lie_mem := fun {x v} hv => fTowerSubmodule_lie_mem M t hL P x hv
  }

-- the f-tower spans M, using the irreducibility of representation
lemma fTowerLieSubmodule_eq_top
    [LieModule.IsIrreducible ℂ L M]
    (hL : t.toLieSubalgebra ℂ = ⊤)
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    fTowerLieSubmodule M t hL P = ⊤ := by
    -- prove that the primitive vector 0 ≠ m ∈ M so M ≠ ⊥
  have hm_mem : m ∈ fTowerSubmodule M t P := by
    rw [fTowerSubmodule]
    apply Submodule.mem_span_of_mem
    simp_all only [mem_range]
    use 0
    rfl
  have hfTower_ne : fTowerSubmodule M t P ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    use m
    exact ⟨hm_mem, P.ne_zero⟩
  rcases eq_bot_or_eq_top (fTowerLieSubmodule M t hL P) with h_bot | h_top
  · by_contra!
    have h_bot_sub : fTowerSubmodule M t P = ⊥ := congr_arg LieSubmodule.toSubmodule h_bot
    exact hfTower_ne h_bot_sub
  · exact h_top


-- {f^k(m)} is linearly independent
lemma fTower_linearIndependent
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    LinearIndependent ℂ (fun i : {n : ℕ | ((toEnd ℂ L M f) ^ n) m ≠ 0} =>
      ((toEnd ℂ L M f) ^ (i : ℕ)) m) := by
  -- similar to the approche used in exists_primitiveVector, but this time
  -- we consider the action of f instead of e
  let domain : Type := {n : ℕ // ((toEnd ℂ L M f) ^ n) m ≠ 0}
  -- In contrast to e, f lowers the weight (eigenvalue) of the primitive vector.
  let evals : domain → ℂ := fun n ↦ μ - 2 * (n.1 : ℂ)
  let e_vecs : domain → M := fun n ↦ ((toEnd ℂ L M f) ^ n.1) m
  have h_indep :=
    Module.End.eigenvectors_linearIndependent
    (toEnd ℂ L M h)
    (Set.range evals)
    (fun ⟨γ, hγ⟩ ↦ e_vecs (Classical.choose hγ))
    (by
      rintro ⟨γ, hγ⟩
      dsimp only
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      let n : domain := Classical.choose hγ
      have h_γ_eq : evals n = γ := Classical.choose_spec hγ
      let v := e_vecs n
      have h_v_ne : v ≠ 0 := n.property
      have h_v_eq : (toEnd ℂ L M h) v = γ • v := by
        rw [← h_γ_eq]
        unfold evals
        simp only [toEnd_apply_apply, ne_eq]
        rw [P.lie_h_pow_toEnd_f]
      exact ⟨h_v_eq, h_v_ne⟩
    )
  -- we still need to pull back the index from the set of eigenvalues to domain
  -- this part is proposed by Gemini3.1 pro
  have h_evals_inj : Function.Injective evals := by
    intro a b hab
    dsimp [evals] at hab
    simp_all only [ne_eq, sub_right_inj, mul_eq_mul_left_iff, Nat.cast_inj,
    OfNat.ofNat_ne_zero, or_false, domain, evals, e_vecs]
    obtain ⟨val, property⟩ := a
    obtain ⟨val_1, property_1⟩ := b
    subst hab
    simp_all only [ne_eq]
  let g : domain → Set.range evals := fun n ↦ ⟨evals n, Set.mem_range_self n⟩
  have hg_inj : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    have h_eq : evals a = evals b := by
      apply_fun Subtype.val at hab
      exact hab
    exact h_evals_inj h_eq
  -- pull back the index family
  have h_indep_domain := h_indep.comp g hg_inj
  convert h_indep_domain using 1
  ext n
  dsimp
  congr
  apply h_evals_inj
  exact (Classical.choose_spec (Set.mem_range_self n)).symm

/-- The weight space of a given weight `μ` with respect to the Cartan element `h` of the `sl₂` triple.
`ℂ` may be later generalized to any algebraically closed field of characteristic 0. -/

abbrev weightSpace (t : IsSl2Triple h e f) (μ : ℂ) := End.eigenspace (toEnd ℂ L M h) μ
-- {f^k(m)} form a basis of M
-- each weight space corresponds to at most a single base vector hence has dimension ≤ 1.
lemma finrank_weightSpace_le_one_of_fTower
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    (h_spans : fTowerSubmodule M t P = ⊤)
    {weight : ℂ} :
    finrank ℂ (weightSpace M t weight) ≤ 1 := by
  by_cases h_fin : Module.Finite ℂ (weightSpace M t weight)
  · haveI : Module.Finite ℂ (weightSpace M t weight) := h_fin
    rw [finrank_le_one_iff]
    by_cases h_bot : weightSpace M t weight = ⊥
    · simp [h_bot]
    -- separate the case to obtain a non zero vector u
    · obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_bot
      use ⟨u, hu_mem⟩
      rintro ⟨w, hw_mem⟩
      simp [Subtype.ext_iff, Submodule.coe_smul]
      have hu_mem_fTower : u ∈ fTowerSubmodule M t P := by
        rw [h_spans]
        simp only [Submodule.mem_top]
      have hw_mem_fTower : w ∈ fTowerSubmodule M t P := by
        rw [h_spans]
        simp only [Submodule.mem_top]
      rw [fTowerSubmodule] at hu_mem_fTower hw_mem_fTower

      -- represent u and w in the form of linear composition of f^i(m)
      obtain ⟨cu, hu_sum⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu_mem_fTower
      obtain ⟨cw, hw_sum⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw_mem_fTower
      rw [Module.End.mem_eigenspace_iff] at hu_mem hw_mem
      -- substitute u and w in the hu_mem and hw_mem with their sum form
      rw [← hu_sum] at hu_mem
      rw [← hw_sum] at hw_mem
      -- put h inside the sum so that it acts on (((toEnd ℂ L M) f ^ x) m)
      simp [Finsupp.sum, map_sum, map_smul, Finset.smul_sum] at hu_mem hw_mem
      simp_rw [P.lie_h_pow_toEnd_f] at hu_mem hw_mem
      simp_rw [smul_smul] at hu_mem hw_mem
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hu_mem hw_mem
      simp_rw [← sub_smul] at hu_mem hw_mem

      -- Note: The code below largely relies on the help of Gemini 3.1 Pro.
      -- Define a predicate `p` for non-zero vectors.
      let p : ℕ → Prop := fun n ↦ ((toEnd ℂ L M) f ^ n) m ≠ 0
      -- Provide a decidability instance for filtering.
      haveI : DecidablePred p := Classical.decPred p

      -- Show the sum remains zero after filtering out zero vectors.
      have hu_filter : ∑ x ∈ cu.support.filter p, (cu x * (μ - 2 * ↑x) - weight * cu x) • ((toEnd ℂ L M) f ^ x) m = 0 := by
        rw [← hu_mem]
        apply Finset.sum_subset (Finset.filter_subset p cu.support)
        intro x hx hx_not_mem
        have hpx : ¬ p x := fun h ↦ hx_not_mem (Finset.mem_filter.mpr ⟨hx, h⟩)
        have hpx_eq : ((toEnd ℂ L M) f ^ x) m = 0 := by
          by_contra h_contra
          exact hpx h_contra
        rw [hpx_eq, smul_zero]

      -- Obtain the `linearIndependent_iff` formulation.
      have h_indep := fTower_linearIndependent M t P
      have h_lin_iff := linearIndependent_iff'.mp h_indep

      -- Bridge the type gap between `Finset ℕ` and `Finset {n // p n}`.
      have H_map : Finset.map (Function.Embedding.subtype p) (cu.support.subtype p) = cu.support.filter p := by
        ext x
        rw [Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨a, ha, ha_eq⟩
          rw [Finset.mem_subtype] at ha
          rw [← ha_eq]
          exact ⟨ha, a.prop⟩
        · rintro ⟨hx, hpx⟩
          refine ⟨⟨x, hpx⟩, ?_, rfl⟩
          rw [Finset.mem_subtype]
          exact hx

      -- Rewrite the sum over the subtype.
      -- Use explicit coercions to prevent typeclass inference timeouts.
      have hu_subtype : ∑ n ∈ cu.support.subtype p, (cu (n : ℕ) * (μ - 2 * ((n : ℕ) : ℂ)) - weight * cu (n : ℕ)) • ((toEnd ℂ L M) f ^ (n : ℕ)) m = 0 := by
        have h_sum_map := Finset.sum_map (cu.support.subtype p) (Function.Embedding.subtype p) (fun x ↦ (cu x * (μ - 2 * (x : ℂ)) - weight * cu x) • ((toEnd ℂ L M) f ^ x) m)
        rw [H_map] at h_sum_map
        exact Eq.trans h_sum_map.symm hu_filter

      -- Separate instantiation and application to avoid timeouts.
      have hu_coeff_subtype : ∀ i ∈ cu.support.subtype p, cu (i : ℕ) * (μ - 2 * ((i : ℕ) : ℂ)) - weight * cu (i : ℕ) = 0 := by
        intro i hi
        -- Explicitly provide the coefficient function to ensure syntactic equality.
        have H := h_lin_iff (cu.support.subtype p) (fun n ↦ cu (n : ℕ) * (μ - 2 * ((n : ℕ) : ℂ)) - weight * cu (n : ℕ)) hu_subtype
        exact H i hi

      -- Pull the coefficient condition back to `ℕ`.
      have hu_coeff : ∀ x ∈ cu.support, ((toEnd ℂ L M) f ^ x) m ≠ 0 → cu x * (μ - 2 * (x : ℂ)) - weight * cu x = 0 := by
        intro x hx h_nonzero
        -- Resolve the subset membership condition.
        exact hu_coeff_subtype ⟨x, h_nonzero⟩ (Finset.mem_subtype.mpr hx)

      -- ==========================================================
      -- === 2. Repeat the same filtering and extraction for `w` ===
      -- ==========================================================
      have hw_filter : ∑ x ∈ cw.support.filter p, (cw x * (μ - 2 * ↑x) - weight * cw x) • ((toEnd ℂ L M) f ^ x) m = 0 := by
        rw [← hw_mem]
        apply Finset.sum_subset (Finset.filter_subset p cw.support)
        intro x hx hx_not_mem
        have hpx : ¬ p x := fun h ↦ hx_not_mem (Finset.mem_filter.mpr ⟨hx, h⟩)
        have hpx_eq : ((toEnd ℂ L M) f ^ x) m = 0 := by
          by_contra h_contra
          exact hpx h_contra
        rw [hpx_eq, smul_zero]

      have H_map_w : Finset.map (Function.Embedding.subtype p) (cw.support.subtype p) = cw.support.filter p := by
        ext x
        rw [Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨a, ha, ha_eq⟩
          rw [Finset.mem_subtype] at ha
          rw [← ha_eq]
          exact ⟨ha, a.prop⟩
        · rintro ⟨hx, hpx⟩
          refine ⟨⟨x, hpx⟩, ?_, rfl⟩
          rw [Finset.mem_subtype]
          exact hx

      have hw_subtype : ∑ n ∈ cw.support.subtype p, (cw (n : ℕ) * (μ - 2 * ((n : ℕ) : ℂ)) - weight * cw (n : ℕ)) • ((toEnd ℂ L M) f ^ (n : ℕ)) m = 0 := by
        have h_sum_map := Finset.sum_map (cw.support.subtype p) (Function.Embedding.subtype p) (fun x ↦ (cw x * (μ - 2 * (x : ℂ)) - weight * cw x) • ((toEnd ℂ L M) f ^ x) m)
        rw [H_map_w] at h_sum_map
        exact Eq.trans h_sum_map.symm hw_filter

      have hw_coeff_subtype : ∀ i ∈ cw.support.subtype p, cw (i : ℕ) * (μ - 2 * ((i : ℕ) : ℂ)) - weight * cw (i : ℕ) = 0 := by
        intro i hi
        have H := h_lin_iff (cw.support.subtype p) (fun n ↦ cw (n : ℕ) * (μ - 2 * ((n : ℕ) : ℂ)) - weight * cw (n : ℕ)) hw_subtype
        exact H i hi

      have hw_coeff : ∀ x ∈ cw.support, ((toEnd ℂ L M) f ^ x) m ≠ 0 → cw x * (μ - 2 * (x : ℂ)) - weight * cw x = 0 := by
        intro x hx h_nonzero
        exact hw_coeff_subtype ⟨x, h_nonzero⟩ (Finset.mem_subtype.mpr hx)

      -- ==========================================================
      -- === 3. Isolate the unique index `K` and show `u` and `w` are collinear ===
      -- ==========================================================
      have h_exists_K : ∃ K, cu K ≠ 0 ∧ ((toEnd ℂ L M) f ^ K) m ≠ 0 := by
        by_contra! h_contra
        have hu_zero : u = 0 := by
          rw [← hu_sum]
          change ∑ x ∈ cu.support, cu x • ((toEnd ℂ L M) f ^ x) m = 0
          apply Finset.sum_eq_zero
          intro x _
          by_cases h_f : ((toEnd ℂ L M) f ^ x) m = 0
          · rw [h_f, smul_zero]
          · -- Deduce `cu x = 0` by contradiction.
            have h_cu_zero : cu x = 0 := by
              by_contra hc
              -- `cu x ≠ 0` implies `f^x m = 0`, contradicting `h_f`.
              exact h_f (h_contra x hc)
            rw [h_cu_zero, zero_smul]
        exact hu_ne hu_zero

      obtain ⟨K, hK_cu, hK_f_ne_zero⟩ := h_exists_K

      have h_weight_eq : μ - 2 * (K : ℂ) = weight := by
        have h_eq := hu_coeff K (Finsupp.mem_support_iff.mpr hK_cu) hK_f_ne_zero
        rw [sub_eq_zero, mul_comm weight, mul_right_inj' hK_cu] at h_eq
        exact h_eq

      -- Simplify `u`: all terms except the `K`-th term vanish.
      have hu_simp : u = cu K • ((toEnd ℂ L M) f ^ K) m := by
        rw [← hu_sum]
        change ∑ x ∈ cu.support, cu x • ((toEnd ℂ L M) f ^ x) m = _
        have hK_mem : K ∈ cu.support := Finsupp.mem_support_iff.mpr hK_cu
        -- Show that `K` is not in the erased support.
        have h_not_mem : K ∉ cu.support.erase K := fun h ↦ (Finset.mem_erase.mp h).1 rfl
        rw [← Finset.insert_erase hK_mem, Finset.sum_insert h_not_mem]
        have h_erase_zero : ∑ x ∈ cu.support.erase K, cu x • ((toEnd ℂ L M) f ^ x) m = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hx_ne : x ≠ K := (Finset.mem_erase.mp hx).1
          have hx_mem : x ∈ cu.support := (Finset.mem_erase.mp hx).2
          by_cases h_f : ((toEnd ℂ L M) f ^ x) m = 0
          · rw [h_f, smul_zero]
          · have h_eq := hu_coeff x hx_mem h_f
            rw [← h_weight_eq] at h_eq
            have h_cu_zero : cu x = 0 := by
              have h1 : cu x * (μ - 2 * ↑x) - (μ - 2 * ↑K) * cu x = 0 := h_eq
              have h2 : cu x * (2 * (↑K - ↑x)) = 0 := by
                calc
                  cu x * (2 * (↑K - ↑x)) = cu x * (μ - 2 * ↑x) - (μ - 2 * ↑K) * cu x := by ring
                  _ = 0 := h1
              cases mul_eq_zero.mp h2 with
              | inl h => exact h
              | inr h =>
                have h_diff : (K : ℂ) - (x : ℂ) = 0 := by
                  cases mul_eq_zero.mp h with
                  | inl h2 => norm_num at h2
                  | inr h_diff => exact h_diff
                have h_eq_nat : K = x := by exact_mod_cast sub_eq_zero.mp h_diff
                exact (hx_ne h_eq_nat.symm).elim
            rw [h_cu_zero, zero_smul]
        rw [h_erase_zero, add_zero]

      -- Simplify `w`: similarly, all non-`K` terms vanish.
      have hw_simp : w = cw K • ((toEnd ℂ L M) f ^ K) m := by
        rw [← hw_sum]
        change ∑ x ∈ cw.support, cw x • ((toEnd ℂ L M) f ^ x) m = _
        by_cases hK_mem_w : K ∈ cw.support
        · have h_not_mem_w : K ∉ cw.support.erase K := fun h ↦ (Finset.mem_erase.mp h).1 rfl
          rw [← Finset.insert_erase hK_mem_w, Finset.sum_insert h_not_mem_w]
          have h_erase_zero : ∑ x ∈ cw.support.erase K, cw x • ((toEnd ℂ L M) f ^ x) m = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            have hx_ne : x ≠ K := (Finset.mem_erase.mp hx).1
            have hx_mem : x ∈ cw.support := (Finset.mem_erase.mp hx).2
            by_cases h_f : ((toEnd ℂ L M) f ^ x) m = 0
            · rw [h_f, smul_zero]
            · have h_eq := hw_coeff x hx_mem h_f
              rw [← h_weight_eq] at h_eq
              have h_cw_zero : cw x = 0 := by
                have h1 : cw x * (μ - 2 * ↑x) - (μ - 2 * ↑K) * cw x = 0 := h_eq
                have h2 : cw x * (2 * (↑K - ↑x)) = 0 := by
                  calc
                    cw x * (2 * (↑K - ↑x)) = cw x * (μ - 2 * ↑x) - (μ - 2 * ↑K) * cw x := by ring
                    _ = 0 := h1
                cases mul_eq_zero.mp h2 with
                | inl h => exact h
                | inr h =>
                  have h_diff : (K : ℂ) - (x : ℂ) = 0 := by
                    cases mul_eq_zero.mp h with
                    | inl h2 => norm_num at h2
                    | inr h_diff => exact h_diff
                  have h_eq_nat : K = x := by exact_mod_cast sub_eq_zero.mp h_diff
                  exact (hx_ne h_eq_nat.symm).elim
              rw [h_cw_zero, zero_smul]
          rw [h_erase_zero, add_zero]
        · have h_w_zero : ∑ x ∈ cw.support, cw x • ((toEnd ℂ L M) f ^ x) m = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            have hx_ne : x ≠ K := by
              rintro rfl
              exact hK_mem_w hx
            by_cases h_f : ((toEnd ℂ L M) f ^ x) m = 0
            · rw [h_f, smul_zero]
            · have h_eq := hw_coeff x hx h_f
              rw [← h_weight_eq] at h_eq
              have h_cw_zero : cw x = 0 := by
                have h1 : cw x * (μ - 2 * ↑x) - (μ - 2 * ↑K) * cw x = 0 := h_eq
                have h2 : cw x * (2 * (↑K - ↑x)) = 0 := by
                  calc
                    cw x * (2 * (↑K - ↑x)) = cw x * (μ - 2 * ↑x) - (μ - 2 * ↑K) * cw x := by ring
                    _ = 0 := h1
                cases mul_eq_zero.mp h2 with
                | inl h => exact h
                | inr h =>
                  have h_diff : (K : ℂ) - (x : ℂ) = 0 := by
                    cases mul_eq_zero.mp h with
                    | inl h2 => norm_num at h2
                    | inr h_diff => exact h_diff
                  have h_eq_nat : K = x := by exact_mod_cast sub_eq_zero.mp h_diff
                  exact (hx_ne h_eq_nat.symm).elim
              rw [h_cw_zero, zero_smul]
          have hcwK_zero : cw K = 0 := by
            by_contra hc
            exact hK_mem_w (Finsupp.mem_support_iff.mpr hc)
          rw [h_w_zero, hcwK_zero, zero_smul]

      -- Conclude by providing the scalar ratio.
      use (cw K) / (cu K)
      rw [hu_simp, hw_simp]
      simp only [smul_smul]
      congr 1
      exact div_mul_cancel₀ (cw K) hK_cu
    -- finrank = 0 by definition if weightspace has infinite dimension
  · rw [finrank_of_infinite_dimensional h_fin]
    exact zero_le_one

--The non-trivial weight space of a fin-dim irreducible representation of sl(2,ℂ) has dimension 1.
theorem finrank_weightSpace_eq_one_of_isIrreducible
    (t : IsSl2Triple h e f)
    (hL : t.toLieSubalgebra ℂ = ⊤) --lie algebra sl(2,ℂ)
    [FiniteDimensional ℂ M] [LieModule.IsIrreducible ℂ L M] --fin-dim irrep
    {μ : ℂ} (h_nontrivial : t.weightSpace M μ ≠ ⊥) : --non trivial weight space
    finrank ℂ ( t.weightSpace M μ) = 1 := by
  haveI : Nontrivial M := by
    rw [nontrivial_iff]
    by_contra h_triv
    push_neg at h_triv
    apply h_nontrivial
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · intro _; exact h_triv x 0
    · intro h; rw [h]; exact Submodule.zero_mem _
  -- Get a primitive vector
  obtain ⟨μ₀, m₀, hm₀_ne, P⟩ := exists_primitiveVector M t
  -- The f-tower spans M
  have h_top_lie := fTowerLieSubmodule_eq_top M t hL P
  -- Each weight space has dimension ≤ 1
  have h_le : finrank ℂ (t.weightSpace M μ) ≤ 1 := by
    have h_top : fTowerSubmodule M t P = ⊤ := congr_arg LieSubmodule.toSubmodule h_top_lie
    exact finrank_weightSpace_le_one_of_fTower M t P h_top
  -- The given weight space has dimension ≥ 1 (since it's non-trivial)
  have h_ge : 1 ≤ finrank ℂ (t.weightSpace M μ) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h_eq
    apply h_nontrivial
    rwa [Submodule.finrank_eq_zero] at h_eq
  exact le_antisymm h_le h_ge

end ComplexIrreducible

end IsSl2Triple
