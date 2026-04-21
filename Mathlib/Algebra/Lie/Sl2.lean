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
  contrapose this
  simpa [this] using t.lie_e_f.symm

lemma f_ne_zero (t : IsSl2Triple h e f) : f ≠ 0 := by
  have := t.h_ne_zero
  contrapose this
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


section IsAlgClosedIrreducible

variable {L M : Type*}
(K : Type*) [Field K]
[LieRing L] [LieAlgebra K L]
[AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable {h e f : L} {t : IsSl2Triple h e f}

lemma exists_primitiveVector (t : IsSl2Triple h e f)
    [IsAlgClosed K] [CharZero K] [FiniteDimensional K M] [Nontrivial M] :
    ∃ (μ : K) (m : M), m ≠ 0 ∧ HasPrimitiveVectorWith t m μ := by
  obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (toEnd K L M h)
  obtain ⟨m₀, hm₀⟩ := hμ₀.exists_hasEigenvector
  let evals : ℕ → K := fun n ↦ μ₀ + 2 * (n : K)
  let e_vecs : ℕ → M := fun n ↦ ((toEnd K L M e) ^ n) m₀
  have h_exists_zero : ∃ (k : ℕ), e_vecs k = 0 := by
    by_contra! contra
    have h_inj : Function.Injective evals := fun a b hab ↦ by
      simpa [evals, add_right_inj, mul_eq_mul_left_iff, Nat.cast_inj] using hab
    have h_indep := Module.End.eigenvectors_linearIndependent
      (toEnd K L M h) (Set.range evals) (fun ⟨γ, hγ⟩ ↦ e_vecs (Classical.choose hγ)) (by
        rintro ⟨γ, hγ⟩
        let n := Classical.choose hγ
        refine ⟨?_, contra n⟩
        rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply]
        change ⁅h, e_vecs n⁆ = γ • e_vecs n
        rw [← Classical.choose_spec hγ]
        exact t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n)
    haveI := h_indep.finite
    exact (Set.infinite_range_of_injective h_inj) (Set.toFinite _)
  obtain ⟨n, hn_ne, hn_zero⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hm₀.2 h_exists_zero
  refine ⟨evals n, e_vecs n, hn_ne, {
    ne_zero := hn_ne
    lie_h := t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n
    lie_e := by
      rw [lie_e_pow_toEnd_e n]
      exact hn_zero
  }⟩

/-- The `K`-span of the f-tower `{f^k(m) | k ∈ ℕ}` for a vector `m`, not necessarily primitive -/
def fTowerSubmodule (f : L) (m : M) : Submodule K M :=
  Submodule.span K (Set.range (fun i : ℕ => ((toEnd K L M f) ^ i) m))

-- f-tower invariant under the Lie action of f.
lemma fTowerSubmodule_lie_f_mem
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    {v : M} (hv : v ∈ fTowerSubmodule K f m) :
    ⁅f, v⁆ ∈ fTowerSubmodule K f m := by
  unfold fTowerSubmodule
  induction hv using Submodule.span_induction with
  | zero => simp only [lie_zero, zero_mem]
  | add _ _ _ _ ihx ihy => simpa only [lie_add] using add_mem ihx ihy
  | smul c _ _ hx' => simpa only [lie_smul] using Submodule.smul_mem _ c hx'
  | mem _ hx =>
    obtain ⟨n, rfl⟩ := hx
    rw [P.lie_f_pow_toEnd_f]
    exact Submodule.subset_span ⟨_, rfl⟩

-- f-tower invariant under the Lie action of h.
lemma fTowerSubmodule_lie_h_mem
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    {v : M} (hv : v ∈ fTowerSubmodule K f m) :
    ⁅h, v⁆ ∈ fTowerSubmodule K f m := by
  unfold fTowerSubmodule
  induction hv using Submodule.span_induction with
  | zero => simp only [lie_zero, zero_mem]
  | add _ _ _ _ ihx ihy => simpa only [lie_add] using add_mem ihx ihy
  | smul c _ _ hx' => simpa only [lie_smul] using Submodule.smul_mem _ c hx'
  | mem _ hx =>
    obtain ⟨n, rfl⟩ := hx
    rw [P.lie_h_pow_toEnd_f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

-- f-tower invariant under the Lie action of e.
lemma fTowerSubmodule_lie_e_mem
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    {v : M} (hv : v ∈ fTowerSubmodule K f m) :
    ⁅e, v⁆ ∈ fTowerSubmodule K f m := by
  unfold fTowerSubmodule
  induction hv using Submodule.span_induction with
  | zero => simp only [lie_zero, zero_mem]
  | add _ _ _ _ ihx ihy => simpa only [lie_add] using add_mem ihx ihy
  | smul c _ _ hx' => simpa only [lie_smul] using Submodule.smul_mem _ c hx'
  | mem _ hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n
    · simp only [pow_zero, End.one_apply, P.lie_e, zero_mem]
    · rw [P.lie_e_pow_succ_toEnd_f]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The f-tower is invariant under `sl₂(K)` -/
lemma fTowerSubmodule_lie_mem
    (hL : t.toLieSubalgebra K = ⊤)
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ)
    (x : L)
    {v : M} (hv : v ∈ fTowerSubmodule K f m) :
    ⁅x, v⁆ ∈ fTowerSubmodule K f m := by
  have hx_mem : x ∈ t.toLieSubalgebra K := by
    rw[hL]
    simp only [LieSubalgebra.mem_top]
  rw [mem_toLieSubalgebra_iff] at hx_mem
  obtain ⟨c₁,c₂,c₃,hx_eq⟩ := hx_mem
  rw [hx_eq]
  simp only [add_lie,smul_lie]
  rw [t.lie_e_f]
  apply add_mem
  · apply add_mem
    · apply Submodule.smul_mem
      exact fTowerSubmodule_lie_e_mem K P hv
    · apply Submodule.smul_mem
      exact fTowerSubmodule_lie_f_mem K P hv
  · apply Submodule.smul_mem
    exact fTowerSubmodule_lie_h_mem K P hv

/-- The `fTowerSubmodule` equipped with the structure of a Lie submodule. -/
def fTowerLieSubmodule (hL : t.toLieSubalgebra K = ⊤)
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    LieSubmodule K L M := {
      fTowerSubmodule K f m with
      lie_mem := fun {x _} hv => fTowerSubmodule_lie_mem K hL P x hv
    }

lemma fTowerLieSubmodule_eq_top
    [LieModule.IsIrreducible K L M]
    (hL : t.toLieSubalgebra K = ⊤)
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    fTowerLieSubmodule K hL P = ⊤ := by
  have hm_mem : m ∈ fTowerSubmodule K f m := by
    rw [fTowerSubmodule]
    apply Submodule.mem_span_of_mem
    simp only [mem_range]
    use 0
    rfl
  have hfTower_ne : fTowerSubmodule K f m ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    use m
    exact ⟨hm_mem, P.ne_zero⟩
  rcases eq_bot_or_eq_top (fTowerLieSubmodule K hL P) with h_bot | h_top
  · by_contra!
    have h_bot_sub : fTowerSubmodule K f m = ⊥ := congr_arg LieSubmodule.toSubmodule h_bot
    exact hfTower_ne h_bot_sub
  · exact h_top

lemma fTowerSubmodule_eq_top [LieModule.IsIrreducible K L M]
    (hL : t.toLieSubalgebra K = ⊤)
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    fTowerSubmodule K f m = ⊤ :=
  congr_arg LieSubmodule.toSubmodule (fTowerLieSubmodule_eq_top K hL P)

lemma fTower_linearIndependent
    [CharZero K]
    {μ : K} {m : M} (P : t.HasPrimitiveVectorWith m μ) :
    LinearIndependent K (fun i : {n : ℕ | ((toEnd K L M f) ^ n) m ≠ 0} =>
      ((toEnd K L M f) ^ (i : ℕ)) m) := by
  let domain : Type := {n : ℕ // ((toEnd K L M f) ^ n) m ≠ 0}
  let evals : domain → K := fun n ↦ μ - 2 * (n.1 : K)
  let e_vecs : domain → M := fun n ↦ ((toEnd K L M f) ^ n.1) m
  have h_evals_inj : Function.Injective evals := fun a b hab ↦ Subtype.ext <| by
    dsimp [evals] at hab
    simp only [sub_right_inj, mul_eq_mul_left_iff] at hab
    exact_mod_cast hab.resolve_right (by norm_num)
  have h_indep := Module.End.eigenvectors_linearIndependent
    (toEnd K L M h) (Set.range evals) (fun ⟨γ, hγ⟩ ↦ e_vecs (Classical.choose hγ)) (by
      rintro ⟨γ, hγ⟩
      dsimp only
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      let n := Classical.choose hγ
      have hn_eq : evals n = γ := Classical.choose_spec hγ
      refine ⟨?_, n.property⟩
      change (toEnd K L M h) (e_vecs n) = γ • e_vecs n
      rw [← hn_eq]
      dsimp only [e_vecs, evals]
      rw [toEnd_apply_apply, P.lie_h_pow_toEnd_f]
    )
  let g : domain → Set.range evals := fun n ↦ ⟨evals n, Set.mem_range_self n⟩
  have hg_inj : Function.Injective g := fun a b hab ↦
    h_evals_inj (congr_arg Subtype.val hab)
  convert h_indep.comp g hg_inj using 1
  ext n
  exact congr_arg e_vecs (h_evals_inj (Classical.choose_spec (Set.mem_range_self n)).symm)

/-- The weight space of a given weight `μ` with respect to the Cartan element `h` of the `sl₂`
triple. -/
abbrev weightSpace (h : L) (μ : K) := End.eigenspace (toEnd K L M h) μ

/-- Each weight space containing an element f^N m of f-tower is non trivial -/
lemma fTower_weightSpace_nontrivial
  (t : IsSl2Triple h e f) {μ₀ : K} {m₀ : M} (P : t.HasPrimitiveVectorWith m₀ μ₀)
      (i : {n : ℕ | ((toEnd K L M f) ^ n) m₀ ≠ 0}) :
      weightSpace (M := M) K h (μ₀ - 2 * (i.val : K)) ≠ ⊥ := by
    intro h_bot
    have h_mem : ((toEnd K L M f) ^ (i.val : ℕ)) m₀ ∈
      weightSpace (M := M) K h (μ₀ - 2 * (i.val : K)) := by
      rw [Module.End.mem_eigenspace_iff]
      exact P.lie_h_pow_toEnd_f i.val
    rw [h_bot, Submodule.mem_bot] at h_mem
    exact i.property h_mem

/-- The weight spaces with weights `μ₀ - 2n` corresponding to the non-zero elements of the
`f`-tower form an independent family of submodules. -/
lemma fTower_weightSpace_independent
    [CharZero K]
    {μ₀ : K} {m₀ : M} : iSupIndep (fun (i : {n : ℕ | ((toEnd K L M f) ^ n) m₀ ≠ 0}) ↦
    weightSpace (M := M) K h (μ₀ - 2 * (i.val : K))) := by
  have h_inj : Function.Injective (fun (i : {n : ℕ | ((toEnd K L M f) ^ n) m₀ ≠ 0})
  ↦ μ₀ - 2 * (i.val : K)) := by
    intro i j hij
    simp only [sub_right_inj, mul_eq_mul_left_iff, Nat.cast_inj, OfNat.ofNat_ne_zero, or_false]
    at hij
    ext
    exact hij
  have h_indep := Module.End.eigenspaces_iSupIndep (toEnd K L M h)
  exact h_indep.comp h_inj

lemma exists_mem_fTower_of_weightSpace_ne_bot
    (t : IsSl2Triple h e f) (hL : t.toLieSubalgebra K = ⊤)
    [LieModule.IsIrreducible K L M]
    {μ₀ : K} {m₀ : M} (P : t.HasPrimitiveVectorWith m₀ μ₀)
    {μ : K} (h_nontrivial : weightSpace (M := M) K h μ ≠ ⊥) :
    ∃ k : ℕ, ((toEnd K L M f) ^ k) m₀ ≠ 0 ∧ μ = μ₀ - 2 * (k : K):= by
  by_contra! contra
  let S := {n : ℕ | ((toEnd K L M f) ^ n) m₀ ≠ 0}
  have H_span : ⊤ ≤ ⨆ (i : S), weightSpace (M := M) K h (μ₀ - 2 * (i.val : K)) := by
    rw [← fTowerSubmodule_eq_top K hL P, fTowerSubmodule]
    rw [Submodule.span_le]
    rintro x ⟨n, rfl⟩
    by_cases h_zero : ((toEnd K L M f) ^ n) m₀ = 0
    · simp only [h_zero, SetLike.mem_coe, zero_mem]
    · let i : S := ⟨n, h_zero⟩
      have h_mem : ((toEnd K L M f) ^ n) m₀ ∈ weightSpace (M := M) K h (μ₀ - 2 * (i.val : K)) := by
        rw [Module.End.mem_eigenspace_iff]
        exact P.lie_h_pow_toEnd_f n
      have h_le : weightSpace (M := M) K h (μ₀ - 2 * (i.val : K)) ≤ ⨆ (j : S), weightSpace (M := M)
       K h (μ₀ - 2 * (j.val : K)) :=
       le_iSup (fun (j : S) ↦ weightSpace (M := M) K h (μ₀ - 2 * (j.val : K))) i
      exact h_le h_mem
  have H_top : ⨆ (i : S), weightSpace (M := M) K h (μ₀ - 2 * (i.val : K)) = ⊤
  := top_le_iff.mp H_span
  have H_indep := Module.End.eigenspaces_iSupIndep (toEnd K L M h)
  have H_disjoint : Disjoint (weightSpace (M := M) K h μ) (⨆ (γ) (_ : γ ≠ μ),
  weightSpace (M := M) K h γ) := H_indep μ
  have H_le : (⨆ (i : S), weightSpace (M := M) K h (μ₀ - 2 * (i.val : K))) ≤ ⨆ (γ) (_ : γ ≠ μ),
  weightSpace (M := M) K h γ := by
    apply iSup_le
    intro i
    have h_ne : μ₀ - 2 * (i.val : K) ≠ μ := (contra i.val i.property).symm
    exact le_iSup₂ (f := fun γ _ ↦ weightSpace (M := M) K h γ) (μ₀ - 2 * (i.val : K)) h_ne
  have H_inter : weightSpace (M := M) K h μ ⊓ (⨆ (i : S),
  weightSpace (M := M) K h (μ₀ - 2 * (i.val : K))) ≤ ⊥ :=
    le_trans (inf_le_inf_left _ H_le) H_disjoint.le_bot
  rw [H_top, inf_top_eq] at H_inter
  exact h_nontrivial (eq_bot_iff.mpr H_inter)

/-- If `K` is an algebraically closed field with characteristic zero, then each non-trivial
weight space of a finite-dimensional irreducible representation of `sl(2,K)` has dimension 1. -/
theorem finrank_weightSpace_eq_one_of_isIrreducible
    (t : IsSl2Triple h e f)
    (hL : t.toLieSubalgebra K = ⊤)
    [IsAlgClosed K] [CharZero K]
    [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    {μ : K} (h_nontrivial : (weightSpace (M := M) K h μ) ≠ ⊥) :
    finrank K (weightSpace (M := M) K h μ) = 1 := by
  haveI : Nontrivial M := by
    obtain ⟨x, h_x_mem, h_x_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_nontrivial
    exact nontrivial_of_ne x 0 h_x_ne
  obtain ⟨μ₀, m₀, hm₀_ne, P⟩ := t.exists_primitiveVector (M:=M) K
  obtain ⟨k, hk_ne, hk_eq⟩ := exists_mem_fTower_of_weightSpace_ne_bot K t hL P h_nontrivial
  let S := {n : ℕ | ((toEnd K L M f) ^ n) m₀ ≠ 0}
  have hk_mem : k ∈ S := hk_ne
  let v : S → M := fun i ↦ ((toEnd K L M f) ^ (i : ℕ)) m₀
  have h_indep : LinearIndependent K v := fTower_linearIndependent K P
  have h_span : Submodule.span K (Set.range v) = ⊤ := by
    rw [← fTowerSubmodule_eq_top K hL P, fTowerSubmodule]
    refine le_antisymm (Submodule.span_mono <| by rintro _ ⟨i, rfl⟩; exact
      ⟨i.val, rfl⟩) (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    by_cases h_zero : ((toEnd K L M f) ^ i) m₀ = 0
    · simp only [h_zero, SetLike.mem_coe, zero_mem]
    · exact Submodule.subset_span ⟨⟨i, h_zero⟩, rfl⟩
  let b := Basis.mk h_indep h_span.ge
  have h_eq_span : weightSpace (M := M) K h (μ₀ - 2 * (k : K)) = K ∙ (v ⟨k, hk_mem⟩) := by
    apply le_antisymm
    · intro x hx
      have h_Dx : (toEnd K L M h) x = (μ₀ - 2 * (k : K)) • x := Module.End.mem_eigenspace_iff.mp hx
      haveI : Fintype S := FiniteDimensional.fintypeBasisIndex b
      let c := b.equivFun x
      have h_Dx_sum : (toEnd K L M h) x = b.equivFun.symm (fun i ↦ c i * (μ₀ - 2 * (i.val : K)))
      := by
        have h_x_eq : x = b.equivFun.symm c := (LinearEquiv.symm_apply_apply b.equivFun x).symm
        nth_rw 1 [h_x_eq]
        simp only [Basis.equivFun_symm_apply, map_sum]
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        have h_bi : b i = v i := Basis.mk_apply h_indep h_span.ge i
        rw [map_smul, h_bi, (rfl : (toEnd K L M h) (v i) = ⁅h, v i⁆)]
        dsimp
        rw [P.lie_h_pow_toEnd_f i.val, smul_smul]
      have h_equiv_Dx : b.equivFun ((toEnd K L M h) x) = fun i ↦ c i * (μ₀ - 2 * (i.val : K)) := by
        rw [h_Dx_sum, LinearEquiv.apply_symm_apply]
      have h_equiv_Dx_1 : b.equivFun ((toEnd K L M h) x) = fun i ↦ (μ₀ - 2 * (k : K)) * c i := by
        ext i; rw [h_Dx, map_smul, Pi.smul_apply, smul_eq_mul]
      have h_c_i : ∀ i : S, i ≠ ⟨k, hk_mem⟩ → c i = 0 := by
        intro i hi
        have H : c i * (μ₀ - 2 * (i.val : K)) = (μ₀ - 2 * (k : K)) * c i := by
          rw [← congr_fun h_equiv_Dx i, congr_fun h_equiv_Dx_1 i]
        have H2 : c i * (2 * (k : K) - 2 * (i.val : K)) = 0 := by
          calc c i * (2 * (k : K) - 2 * (i.val : K))
            _ = c i * (μ₀ - 2 * (i.val : K)) - c i * (μ₀ - 2 * (k : K)) := by ring
            _ = (μ₀ - 2 * (k : K)) * c i - c i * (μ₀ - 2 * (k : K)) := by rw [H]
            _ = 0 := by ring
        cases mul_eq_zero.mp H2 with
        | inl h_ci => exact h_ci
        | inr h_diff =>
          have h_k_eq_i_nat : k = i.val := by simpa only [sub_eq_zero, mul_eq_mul_left_iff,
            Nat.cast_inj, OfNat.ofNat_ne_zero, or_false] using h_diff
          exact False.elim (hi <| Subtype.ext h_k_eq_i_nat.symm)
      have h_x_final : x = c ⟨k, hk_mem⟩ • v ⟨k, hk_mem⟩ := by
        rw [(LinearEquiv.symm_apply_apply b.equivFun x).symm, Basis.equivFun_symm_apply]
        have h_bi : b ⟨k, hk_mem⟩ = v ⟨k, hk_mem⟩ := Basis.mk_apply h_indep h_span.ge ⟨k, hk_mem⟩
        rw [← h_bi]
        refine Finset.sum_eq_single
          _ (fun i _ hi ↦ ?_) (fun h ↦ False.elim (h <| Finset.mem_univ _))
        change c i • b i = 0
        rw [h_c_i i hi, zero_smul]
      exact Submodule.mem_span_singleton.mpr ⟨c ⟨k, hk_mem⟩, h_x_final.symm⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, End.mem_genEigenspace_one, toEnd_apply_apply]
      exact P.lie_h_pow_toEnd_f k
  rw [hk_eq, h_eq_span]
  exact finrank_span_singleton hk_ne

end IsAlgClosedIrreducible

end IsSl2Triple
