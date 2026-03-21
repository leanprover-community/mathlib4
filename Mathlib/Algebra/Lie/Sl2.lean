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

-- define endomorphism for e
variable {m : M} {μ : R}
local notation "φ " n => ((toEnd R L M e) ^ n) m

lemma lie_e_pow_toEnd_e (hm : ⁅h, m⁆ = μ • m) (n : ℕ) :
    ⁅e, φ n⁆ = φ (n + 1) := by
  simp [pow_succ']

-- symmetric to the proof of lie_h_pow_toEnd_f
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

-- ℂ is algebraically closed and M fin-dim so h has egval μ and egvec m in M.
-- e acting on m raises the eigenvalue of m
-- this must stop at some n otherwise the span goes to infinite dim
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
    -- contradiction :
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
      rw [lie_e_pow_toEnd_e hm₀.apply_eq_smul n_prim, h_eq]
      exact hN_zero
  exact ⟨μ_prim, m_prim, m_prim_ne, m_prim_eq⟩

--The ℂ span of the f-tower {f^k(m) | k ∈ ℕ} for a primitive vector m.
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
  sorry

-- f-tower invariant under the Lie action of e.
lemma fTowerSubmodule_lie_e_mem
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    {v : M} (hv : v ∈ fTowerSubmodule M t P) :
    ⁅e, v⁆ ∈ fTowerSubmodule M t P := by
  sorry

-- f-tower invariant under sl₂ℂ
-- i.e. f-tower invariant under all of L when L is generated by the sl₂ triple.
lemma fTowerSubmodule_lie_mem
    (hL : t.toLieSubalgebra ℂ = ⊤)
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    (x : L) {v : M} (hv : v ∈ fTowerSubmodule M t P) :
    ⁅x, v⁆ ∈ fTowerSubmodule M t P := by
  sorry

-- the f-tower spans M, using the irreducibility of representation
lemma fTowerSubmodule_eq_top
    [LieModule.IsIrreducible ℂ L M]
    (hL : t.toLieSubalgebra ℂ = ⊤)
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    fTowerSubmodule M t P = ⊤ := by
  sorry

-- {f^k(m)} is linearly independent
lemma fTower_linearIndependent
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    LinearIndependent ℂ (fun i : {n : ℕ | ((toEnd ℂ L M f) ^ n) m ≠ 0} =>
      ((toEnd ℂ L M f) ^ (i : ℕ)) m) := by
  sorry

-- ℂ may be later generalized to any algebraically closed field of chr 0.
abbrev weightSpace (t : IsSl2Triple h e f) (μ : ℂ) := End.eigenspace (toEnd ℂ L M h) μ

--  {f^k(m)} form a basis of M
-- each weight space has dimension ≤ 1.
lemma finrank_weightSpace_le_one_of_fTower
    {μ : ℂ} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    (h_spans : fTowerSubmodule M t P = ⊤)
    {weight : ℂ} :
    finrank ℂ (t.weightSpace M weight) ≤ 1 := by
  sorry

--The non-trivial weight space of a fin-dim irreducible representation of sl(2,ℂ) has dimension 1.
theorem finrank_weightSpace_eq_one_of_isIrreducible
    (t : IsSl2Triple h e f)
    (hL : t.toLieSubalgebra ℂ = ⊤) --lie algebra of sl(2,ℂ)
    [FiniteDimensional ℂ M] [LieModule.IsIrreducible ℂ L M] --fin-dim irrep
    {μ : ℂ} (h_nontrivial : t.weightSpace M μ ≠ ⊥) : --non trivial weight space
    finrank ℂ ( t.weightSpace M μ) = 1 := by
  sorry

end ComplexIrreducible

end IsSl2Triple
