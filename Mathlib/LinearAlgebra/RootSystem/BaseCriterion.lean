/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Criterion for bases of root systems

Given a root pairing $P$, sufficient conditions for a subset of linearly indpendent roots $r_i$,
$i ∈ s$ to be a base for a finite root pairing are:
 1. $⟨c_j, r_i⟩ ≤ 0$ for all $i ≠ j$, where $c_j$ is the coroot corresponding to the root $r_j$.
 2. Every root $α$ can be written as $α = w • r_i$ for some $i ∈ s$ and $w$ is a product of
    reflections corresponding to elements of $s$.

This file provides a proof of this result as the definition: `RootPairing.Base.mk''`.
-/

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open FaithfulSMul (algebraMap_injective)
open Function Set Matrix

-- TODO Rewrite the absurd Claude proof below into something suitable for Mathlib.

namespace RootPairing

lemma exists_root_eq_smul_root_iff (P : RootPairing ι R M N) (s : Set ι) (i j : ι) :
    (∃ w ∈ Subgroup.closure (Equiv.reflection P '' s), P.root i = w • P.root j) ↔
      ∃ σ ∈ Subgroup.closure (P.reflectionPerm '' s), i = σ j := by
  constructor
  · rintro ⟨w, hw, hij⟩
    refine ⟨Equiv.indexHom P w, ?_, P.root.injective ?_⟩
    · have himg : (Equiv.indexHom P) '' (Equiv.reflection P '' s) = P.reflectionPerm '' s := by
        rw [image_image]; rfl
      rw [← himg, ← MonoidHom.map_closure]
      exact ⟨w, hw, rfl⟩
    · rw [hij]
      simp [Equiv.indexHom]
  · rintro ⟨σ, hσ, rfl⟩
    suffices ∃ w ∈ Subgroup.closure (Equiv.reflection P '' s), ∀ k, P.root (σ k) = w • P.root k by
      obtain ⟨w, hw, hk⟩ := this
      exact ⟨w, hw, hk j⟩
    clear j
    induction hσ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨Equiv.reflection P k, Subgroup.subset_closure ⟨k, hk, rfl⟩, fun i ↦ by simp⟩
    | one => exact ⟨1, one_mem _, fun i ↦ by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨wx, hwx, hx'⟩ := ihx
      obtain ⟨wy, hwy, hy'⟩ := ihy
      refine ⟨wx * wy, mul_mem hwx hwy, fun i ↦ ?_⟩
      rw [Equiv.Perm.mul_apply, hx' (y i), hy' i, mul_smul]
    | inv x hx ihx =>
      obtain ⟨w, hw, h'⟩ := ihx
      refine ⟨w⁻¹, inv_mem hw, fun i ↦ ?_⟩
      rw [eq_inv_smul_iff, ← h' (x⁻¹ i)]
      simp

variable [Finite ι] [CharZero R] [IsDomain R] (P : RootPairing ι R M N) [P.IsCrystallographic]

lemma exists_mul_diagonal_posDef (s : Finset ι) [DecidableEq ι]
    (h₀ : LinearIndepOn R P.root s) :
    ∃ d : s → ℤ, (∀ k, 0 < d k) ∧
      ((Matrix.of fun k l : s ↦ P.pairingIn ℤ k l) * diagonal d).PosDef := by
  have _i : Fintype ι := Fintype.ofFinite ι
  set B := P.posRootForm ℤ with hB
  set v : s → P.rootSpan ℤ := fun k ↦ P.rootSpanMem ℤ k with hv
  set d : s → ℤ := fun k ↦ B.rootLength k with hd
  set A : Matrix s s ℤ := (Matrix.of fun k l : s ↦ P.pairingIn ℤ k l) * diagonal d with hA
  have hli : LinearIndependent ℤ v := by
    refine LinearIndependent.of_comp (P.rootSpan ℤ).subtype ?_
    have aux : (P.rootSpan ℤ).subtype ∘ v = fun k : s ↦ P.root k := rfl
    rw [aux]
    exact h₀.linearIndependent.restrict_scalars' ℤ
  have key (k l : s) : A k l = 2 * B.posForm (v k) (v l) := by
    rw [hA, mul_diagonal]
    simp only [Matrix.of_apply, hd, hv]
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [map_mul, map_mul, algebraMap_pairingIn, B.algebraMap_rootLength, map_ofNat,
      B.algebraMap_posForm]
    exact (B.toInvariantForm.two_mul_apply_root_root k l).symm
  have hsymm : A.IsSymm := by
    ext k l
    rw [Matrix.transpose_apply, key, key, ← B.isSymm_posForm.eq (v k) (v l)]
    rfl
  refine ⟨d, fun k ↦ B.rootLength_pos k, ?_⟩
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa using hsymm) fun {x} hx ↦ ?_
  have expand : x ⬝ᵥ (A *ᵥ x) = 2 * B.posForm (∑ k, x k • v k) (∑ l, x l • v l) := by
    simp only [dotProduct, mulVec, key, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    have hs := B.isSymm_posForm.eq (v l) (v k)
    simp only [RingHom.id_apply] at hs
    rw [hs]
    ring
  rw [star_trivial, expand]
  have hne : ∑ k, x k • v k ≠ 0 := by
    contrapose! hx
    ext k
    simpa using (Fintype.linearIndependent_iff.mp hli) x hx k
  have := P.posRootForm_posForm_pos_of_ne_zero ℤ hne
  rw [← hB] at this
  positivity

open CartanMatrix in
lemma isFiniteCartan_pairingIn (s : Finset ι) [DecidableEq ι]
    (h₀' : LinearIndepOn R P.coroot s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0) :
    (Matrix.of fun k l : s ↦ P.pairingIn ℤ k l).IsFiniteCartan where
  diag k := P.pairingIn_same ℤ k
  offDiag_nonpos k l hkl := h₁ k.2 l.2 (by simpa using hkl)
  zero_comm k l := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    exact P.pairingIn_eq_zero_iff
  exists_posDef := by
    have hflip (k l : ι) : P.flip.pairingIn ℤ k l = P.pairingIn ℤ l k := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [algebraMap_pairingIn, algebraMap_pairingIn, pairing_flip]
    obtain ⟨d, hd, hd'⟩ := P.flip.exists_mul_diagonal_posDef s h₀'
    refine ⟨d, hd, ?_⟩
    have heq : Matrix.diagonal d * (Matrix.of fun k l : s ↦ P.pairingIn ℤ k l) =
        ((Matrix.of fun k l : s ↦ P.flip.pairingIn ℤ k l) * Matrix.diagonal d)ᵀ := by
      ext k l
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hflip, mul_comm]
    rw [heq, Matrix.PosDef.transpose_iff]
    exact hd'

omit [Finite ι] [CharZero R] [IsDomain R] in
/-- If every index is obtained from an index in `s` by applying reflections in `s`, then every root
is an integral combination of the roots indexed by `s`. -/
lemma root_mem_span_int_image (s : Finset ι)
    (h : ∀ i, ∃ σ ∈ Subgroup.closure (P.reflectionPerm '' s), ∃ j ∈ s, i = σ j)
    (i : ι) :
    P.root i ∈ Submodule.span ℤ (P.root '' s) := by
  set Q := Submodule.span ℤ (P.root '' s)
  let G : Subgroup (Equiv.Perm ι) :=
    { carrier := {σ | ∀ i, P.root (σ i) ∈ Q ↔ P.root i ∈ Q}
      one_mem' := fun i ↦ Iff.rfl
      mul_mem' := fun {a b} ha hb i ↦ (ha (b i)).trans (hb i)
      inv_mem' := fun {a} ha i ↦ by simpa using (ha (a⁻¹ i)).symm }
  have hle : Subgroup.closure (P.reflectionPerm '' s) ≤ G := by
    rw [Subgroup.closure_le]
    rintro - ⟨k, hk, rfl⟩
    have hk' : P.root k ∈ Q := Submodule.subset_span ⟨k, hk, rfl⟩
    have key (i : ι) :
        P.root (P.reflectionPerm k i) = P.root i - P.pairingIn ℤ i k • P.root k := by
      rw [P.root_reflectionPerm, P.reflection_apply_root, ← P.algebraMap_pairingIn ℤ]
      simp [Int.cast_smul_eq_zsmul]
    have aux (i : ι) (hi : P.root i ∈ Q) : P.root (P.reflectionPerm k i) ∈ Q := by
      rw [key]
      exact Submodule.sub_mem _ hi (Submodule.smul_mem _ _ hk')
    intro i
    refine ⟨fun hi ↦ ?_, aux i⟩
    simpa using aux _ hi
  obtain ⟨σ, hσ, j, hj, rfl⟩ := h i
  exact (hle hσ j).mpr (Submodule.subset_span ⟨j, hj, rfl⟩)

omit [Finite ι] [IsDomain R] in
/-- The pairing of a root with a simple coroot, expressed in terms of the coefficients of the
root relative to the simple roots and the Cartan matrix. -/
private lemma pairingIn_eq_sum (s : Finset ι) {i : ι} {c : s → ℤ}
    (hc : P.root i = ∑ k, c k • P.root k) (l : s) :
    P.pairingIn ℤ i (l : ι) = ∑ j, c j * P.pairingIn ℤ (j : ι) (l : ι) := by
  apply algebraMap_injective ℤ R
  have h := congrArg (fun x ↦ P.toLinearMap x (P.coroot l)) hc
  simpa [map_sum, ← P.algebraMap_pairingIn ℤ, Int.cast_smul_eq_zsmul] using h

omit [Finite ι] [IsDomain R] in
/-- Since the Cartan matrix of `s` is non-singular, the roots indexed by `s` are linearly
independent over `ℤ`. -/
private lemma eq_zero_of_sum_smul_root_eq_zero (s : Finset ι) [DecidableEq ι]
    (hA : (Matrix.of fun k l : s ↦ P.pairingIn ℤ k l).IsFiniteCartan)
    {c : s → ℤ} (hc : ∑ k, c k • P.root k = 0) :
    c = 0 := by
  have hpair (l : s) : ∑ k, c k * P.pairingIn ℤ (k : ι) (l : ι) = 0 := by
    apply algebraMap_injective ℤ R
    have h := congrArg (fun x ↦ P.toLinearMap x (P.coroot l)) hc
    simpa [map_sum, ← P.algebraMap_pairingIn ℤ, Int.cast_smul_eq_zsmul] using h
  obtain ⟨d, hd, hS⟩ := hA.transpose.exists_posDef
  by_contra hc'
  have key : (diagonal d * (Matrix.of fun k l : s ↦ P.pairingIn ℤ k l)ᵀ) *ᵥ c = 0 := by
    ext k
    simp only [mulVec, dotProduct, diagonal_mul, transpose_apply, Matrix.of_apply, Pi.zero_apply]
    simp_rw [show ∀ x : s, d k * P.pairingIn ℤ (x : ι) (k : ι) * c x
        = (c x * P.pairingIn ℤ (x : ι) (k : ι)) * d k from fun x ↦ by ring,
      ← Finset.sum_mul, hpair k, zero_mul]
  have h := hS.dotProduct_mulVec_pos hc'
  rw [key] at h
  simp at h

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] in
private lemma sum_smul_root_mem_closure (s : Finset ι) {c : s → ℤ} (hc : 0 ≤ c) :
    ∑ k, c k • P.root k ∈ AddSubmonoid.closure (P.root '' s) := by
  refine AddSubmonoid.sum_mem _ fun k _ ↦ ?_
  have h1 : 0 ≤ c k := hc k
  have h2 : c k • P.root (k : ι) = (c k).toNat • P.root (k : ι) := by
    rw [← natCast_zsmul, Int.toNat_of_nonneg h1]
  rw [h2]
  exact nsmul_mem (AddSubmonoid.subset_closure (Set.mem_image_of_mem _ k.2)) _

/-- If `αₖ`, `αₗ` are distinct simple roots then `αₖ - αₗ` is not a root.

Indeed if it were a root `β`, then `⟨β, αₖ^∨⟩ = 2 - ⟨αₗ, αₖ^∨⟩ ≥ 2` and so `⟨αₖ, β^∨⟩ = 1`.
Reflecting in `β` thus carries `αₖ` to `αₗ` and so `αₗ^∨ = αₖ^∨ - ⟨β, αₖ^∨⟩ β^∨`, which is
incompatible with the linear independence of the simple coroots. -/
private lemma root_sub_root_notMem_range (s : Finset ι)
    (hcs : ∀ i, P.coroot i ∈ Submodule.span ℤ (P.coroot '' s))
    (h₀' : LinearIndepOn R P.coroot s)
    (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
    {k l : ι} (hk : k ∈ s) (hl : l ∈ s) (hkl : k ≠ l) :
    P.root k - P.root l ∉ range P.root := by
  classical
  have _i : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rintro ⟨m, hm⟩
  have hu : P.pairingIn ℤ m k = 2 - P.pairingIn ℤ l k := by
    apply algebraMap_injective ℤ R
    rw [map_sub, algebraMap_pairingIn, algebraMap_pairingIn, map_ofNat,
      ← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing, hm, map_sub, LinearMap.sub_apply,
      P.root_coroot_eq_pairing, P.pairing_same]
  have hlk : P.pairingIn ℤ l k ≤ 0 := h₁ hl hk (Ne.symm hkl)
  have hmk : m ≠ k := by
    rintro rfl
    rw [eq_comm, sub_eq_self] at hm
    exact P.ne_zero l hm
  have hv : P.pairingIn ℤ k m = 1 := by
    have h4 := P.pairingIn_pairingIn_mem_set_of_isCrystallographic m k
    have h2 : ¬ (P.pairingIn ℤ m k = 2 ∧ P.pairingIn ℤ k m = 2) := fun h ↦
      hmk <| (P.pairingIn_two_two_iff ℤ m k).mp h
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h4
    omega
  have hrefl : P.reflectionPerm m k = l := by
    apply P.root.injective
    rw [P.root_reflectionPerm, P.reflection_apply_root, ← P.algebraMap_pairingIn ℤ, hv, hm]
    simp
  have hcoroot : P.coroot l = P.coroot k - P.pairingIn ℤ m k • P.coroot m := by
    have h := P.coroot_reflectionPerm m k
    rw [hrefl, P.coreflection_apply_coroot, ← P.algebraMap_pairingIn ℤ] at h
    simpa [Int.cast_smul_eq_zsmul] using h
  obtain ⟨e, he⟩ : ∃ e : s → ℤ, ∑ j, e j • P.coroot j = P.coroot m := by
    rw [Set.image_eq_range] at hcs
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hcs m)
  have huniq : ∀ c c' : s → ℤ,
      ∑ j, c j • P.coroot j = ∑ j, c' j • P.coroot j → c = c' :=
    fun c c' h ↦ funext fun j ↦
      Fintype.linearIndependent_iffₛ.mp (h₀'.restrict_scalars' ℤ) c c' h j
  have key : (Pi.single (⟨l, hl⟩ : s) 1 : s → ℤ)
      = Pi.single (⟨k, hk⟩ : s) 1 - P.pairingIn ℤ m k • e := by
    refine huniq _ _ ?_
    rw [Fintype.sum_single_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib,
      Fintype.sum_single_smul, one_smul, mul_smul, ← Finset.smul_sum, he]
    exact hcoroot
  have hk' := congrFun key ⟨k, hk⟩
  rw [Pi.single_eq_of_ne (by simpa using hkl), Pi.sub_apply, Pi.single_eq_same,
    Pi.smul_apply, smul_eq_mul] at hk'
  have hu2 : 2 ≤ P.pairingIn ℤ m k := by omega
  rcases le_or_gt (e ⟨k, hk⟩) 0 with h | h <;> nlinarith

/- Auxiliary result for `RootPairing.bar`, carrying an induction on the `ℓ¹` norm `∑ i, |cᵢ|` of
the coefficient vector, together with a choice of positive-definite symmetrisation
`S = A * diagonal d` of the Cartan matrix `A`.

The key facts used are that `(S *ᵥ c) i = ⟨β, αᵢ^∨⟩ * dᵢ` for a root `β = ∑ cᵢ αᵢ`, together with
the fact that `β - αₖ` is a root whenever `⟨β, αₖ^∨⟩ > 0` and `β ≠ αₖ`. Since `0 < c ⬝ᵥ S *ᵥ c`,
there is some `k` such that `cₖ` and `⟨β, αₖ^∨⟩` have the same (non-zero) sign; replacing `β` by
`-β` we may assume both are positive. Applying the inductive hypothesis to `β - αₖ` we may assume
that `cₖ = 1` and that `cⱼ ≤ 0` for `j ≠ k`. A second application of positive definiteness then
provides `l` such that `c l < 0` and `⟨β, αₗ^∨⟩ < 0`, and applying the inductive hypothesis to
`β + αₗ` we find that `β = αₖ - αₗ`, which is impossible. -/
private lemma nonneg_or_nonpos_aux (s : Finset ι) [DecidableEq ι] {A : Matrix s s ℤ}
    (hAdiag : ∀ k, A k k = 2)
    (hAoff : ∀ k l, k ≠ l → A k l ≤ 0)
    (hApair : ∀ (i : ι) (c : s → ℤ), P.root i = ∑ k, c k • P.root k →
      ∀ l : s, P.pairingIn ℤ i (l : ι) = ∑ j, c j * A j l)
    (huniq : ∀ c c' : s → ℤ, ∑ k, c k • P.root k = ∑ k, c' k • P.root k → c = c')
    (hsub : ∀ k l : s, k ≠ l → P.root k - P.root l ∉ range P.root)
    (d : s → ℤ) (hd : ∀ k, 0 < d k) (hS : (A * diagonal d).PosDef) (m : ℕ) :
    ∀ (i : ι) (c : s → ℤ), ∑ k, (c k).natAbs ≤ m →
      P.root i = ∑ k, c k • P.root k → 0 ≤ c ∨ c ≤ 0 := by
  have hsymm : (A * diagonal d).IsSymm := hS.isHermitian.isSymm
  have hmv : ∀ (v : s → ℤ) (i : s),
      ((A * diagonal d) *ᵥ v) i = (∑ j, v j * A j i) * d i := by
    intro v i
    have hd' (j : s) : A i j * d j = A j i * d i := by simpa using hsymm.apply j i
    simp_rw [mulVec_apply_eq_sum, mul_diagonal, hd', Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hpos : ∀ c : s → ℤ, c ≠ 0 → 0 < c ⬝ᵥ (A * diagonal d) *ᵥ c := fun c hc ↦ by
    simpa using hS.dotProduct_mulVec_pos hc
  have hsumneg : ∀ (c : s → ℤ) (l : s), ∑ j, (-c) j * A j l = -∑ j, c j * A j l := by
    intro c l
    simp
  have hsingle_sum :
      ∀ k : s, ∑ j, (Pi.single k 1 : s → ℤ) j • P.root (j : ι) = P.root k :=
    fun k ↦ by rw [Fintype.sum_single_smul, one_smul]
  have hsum_sub : ∀ (c : s → ℤ) (k : s),
      ∑ j, (c - Pi.single k 1 : s → ℤ) j • P.root (j : ι)
        = (∑ j, c j • P.root (j : ι)) - P.root k := by
    intro c k
    simp_rw [Pi.sub_apply, sub_smul]
    rw [Finset.sum_sub_distrib, hsingle_sum]
  have hsum_single_sub : ∀ k l : s,
      ∑ j, (Pi.single k 1 - Pi.single l 1 : s → ℤ) j • P.root (j : ι)
        = P.root k - P.root l := by
    intro k l
    simp_rw [Pi.sub_apply, sub_smul]
    rw [Finset.sum_sub_distrib, hsingle_sum, hsingle_sum]
  have hnegroot : ∀ (i : ι) (c : s → ℤ), P.root i = ∑ k, c k • P.root k →
      P.root (P.reflectionPerm i i) = ∑ k, (-c) k • P.root k := by
    intro i c hc
    rw [P.root_reflectionPerm, P.reflection_apply_self, hc]
    simp [← Finset.sum_neg_distrib]
  induction m with
  | zero =>
    intro i c hm hc
    refine Or.inl (Pi.le_def.mpr fun k ↦ ?_)
    have h0 : (c k).natAbs = 0 := Nat.le_zero.mp <| le_trans
      (Finset.single_le_sum (f := fun k ↦ (c k).natAbs) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ k)) hm
    simp only [Pi.zero_apply]
    grind
  | succ m ih =>
    have descent : ∀ (q : ι) (c : s → ℤ), ∑ k, (c k).natAbs ≤ m + 1 →
        P.root q = ∑ k, c k • P.root k → ∀ k : s, 0 < c k → 0 < ∑ j, c j * A j k →
        0 ≤ c ∨ (c k = 1 ∧ ∀ j, j ≠ k → c j ≤ 0) := by
      intro q c hm hc k hck huk
      by_cases hsingle : c = Pi.single k 1
      · refine Or.inl (Pi.le_def.mpr fun j ↦ ?_)
        rw [hsingle]
        simp only [Pi.zero_apply, Pi.single_apply]
        split <;> simp
      have hbne : q ≠ (k : ι) := by
        intro contra
        refine hsingle (huniq c (Pi.single k 1) ?_)
        rw [← hc, contra, hsingle_sum]
      have hpair : 0 < P.pairingIn ℤ q (k : ι) := by rw [hApair q c hc k]; exact huk
      obtain ⟨b, hb⟩ := P.root_sub_root_mem_of_pairingIn_pos hpair hbne
      have hb1 : P.root b = ∑ j, (c - Pi.single k 1 : s → ℤ) j • P.root j := by
        rw [hsum_sub, ← hc, hb]
      have hnat : ∑ j, ((c - Pi.single k 1 : s → ℤ) j).natAbs ≤ m := by
        have h1 : ∑ j ∈ Finset.univ.erase k, ((c - Pi.single k 1 : s → ℤ) j).natAbs
            = ∑ j ∈ Finset.univ.erase k, (c j).natAbs :=
          Finset.sum_congr rfl fun j hj ↦ by
            have hjk : j ≠ k := Finset.ne_of_mem_erase hj
            simp [hjk]
        have h2 := Finset.add_sum_erase Finset.univ
          (fun j ↦ ((c - Pi.single k 1 : s → ℤ) j).natAbs) (Finset.mem_univ k)
        have h3 := Finset.add_sum_erase Finset.univ (fun j ↦ (c j).natAbs) (Finset.mem_univ k)
        have h4 : ((c - Pi.single k 1 : s → ℤ) k).natAbs + 1 = (c k).natAbs := by
          simp only [Pi.sub_apply, Pi.single_eq_same]
          grind
        grind
      rcases ih b _ hnat hb1 with h | h
      · refine Or.inl (Pi.le_def.mpr fun j ↦ ?_)
        have := Pi.le_def.mp h j
        simp only [Pi.zero_apply, Pi.sub_apply, Pi.single_apply] at this ⊢
        split at this <;> grind
      · refine Or.inr ⟨?_, fun j hjk ↦ ?_⟩
        · have := Pi.le_def.mp h k
          simp only [Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same] at this
          grind
        · have := Pi.le_def.mp h j
          simp only [Pi.zero_apply, Pi.sub_apply, Pi.single_eq_of_ne hjk] at this
          grind
    have main : ∀ (q : ι) (c : s → ℤ), ∑ k, (c k).natAbs ≤ m + 1 →
        P.root q = ∑ k, c k • P.root k → ∀ k : s, 0 < c k → 0 < ∑ j, c j * A j k →
        0 ≤ c ∨ c ≤ 0 := by
      intro p c hm hc k hck huk
      rcases descent p c hm hc k hck huk with h | ⟨hck1, hcj⟩
      · exact Or.inl h
      by_cases hall : ∀ j, j ≠ k → c j = 0
      · refine Or.inl (Pi.le_def.mpr fun j ↦ ?_)
        rcases eq_or_ne j k with rfl | hjk
        · simp [hck1]
        · simp [hall j hjk]
      push Not at hall
      obtain ⟨q, hqk, hq0⟩ := hall
      have hcq : c q < 0 := lt_of_le_of_ne (hcj q hqk) hq0
      obtain ⟨l, hcl, hul⟩ : ∃ l, c l < 0 ∧ ∑ j, c j * A j l < 0 := by
        by_contra hcon
        push Not at hcon
        set γ : s → ℤ := Pi.single k 1 - c with hγ
        have hγk : γ k = 0 := by simp [hγ, hck1]
        have hγnonneg : ∀ j, 0 ≤ γ j := fun j ↦ by
          rcases eq_or_ne j k with rfl | hjk
          · simp [hγ, hck1]
          · have := hcj j hjk
            simp only [hγ, Pi.sub_apply, Pi.single_eq_of_ne hjk]
            grind
        have hγne : γ ≠ 0 := fun contra ↦ by
          have := congrFun contra q
          simp only [hγ, Pi.sub_apply, Pi.single_eq_of_ne hqk, Pi.zero_apply] at this
          grind
        have hcγ : c = Pi.single k 1 - γ := by simp [hγ]
        have hw : ∑ j, γ j * A j k ≤ 0 := by
          refine Finset.sum_nonpos fun j _ ↦ ?_
          rcases eq_or_ne j k with rfl | hjk
          · simp [hγk]
          · exact mul_nonpos_iff.mpr (Or.inl ⟨hγnonneg j, hAoff j k hjk⟩)
        have huw : (∑ j, c j * A j k) = 2 - ∑ j, γ j * A j k := by
          rw [hcγ]
          simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply, hAdiag]
        have hQle : c ⬝ᵥ (A * diagonal d) *ᵥ c ≤ (∑ j, c j * A j k) * d k := by
          simp only [dotProduct, hmv]
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), hck1, one_mul]
          have : ∑ i ∈ Finset.univ.erase k, c i * ((∑ j, c j * A j i) * d i) ≤ 0 := by
            refine Finset.sum_nonpos fun i hi ↦ ?_
            have hik : i ≠ k := Finset.ne_of_mem_erase hi
            have h1 : c i * ((∑ j, c j * A j i) * d i)
                = (c i * ∑ j, c j * A j i) * d i := by ring
            rw [h1]
            refine mul_nonpos_iff.mpr (Or.inr ⟨?_, (hd i).le⟩)
            rcases eq_or_lt_of_le (hcj i hik) with h2 | h2
            · simp [h2]
            · exact mul_nonpos_iff.mpr (Or.inr ⟨h2.le, hcon i h2⟩)
          linarith
        have hpolar : ∀ x y : s → ℤ, (x - y) ⬝ᵥ (A * diagonal d) *ᵥ (x - y)
            = x ⬝ᵥ (A * diagonal d) *ᵥ x - 2 * (x ⬝ᵥ (A * diagonal d) *ᵥ y)
              + y ⬝ᵥ (A * diagonal d) *ᵥ y := by
          intro x y
          rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
            hsymm.dotProduct_mulVec_comm (x := y) (y := x)]
          ring
        have hQeq : c ⬝ᵥ (A * diagonal d) *ᵥ c = 2 * d k
            - 2 * ((∑ j, γ j * A j k) * d k) + γ ⬝ᵥ (A * diagonal d) *ᵥ γ := by
          rw [hcγ, hpolar, single_dotProduct, single_dotProduct, hmv, hmv]
          simp [Pi.single_apply, hAdiag]
        have h1 := hpos c (fun contra ↦ by simp [contra] at hck1)
        have h2 := hpos γ hγne
        have h3 : (∑ j, γ j * A j k) * d k ≤ 0 :=
          mul_nonpos_iff.mpr (Or.inr ⟨hw, (hd k).le⟩)
        rw [huw] at hQle
        nlinarith
      have hnegm : ∑ j, ((-c) j).natAbs ≤ m + 1 := by simpa using hm
      rcases descent (P.reflectionPerm p p) (-c) hnegm (hnegroot p c hc) l (by simpa using hcl)
        (by rw [hsumneg]; linarith) with h | ⟨h1, h2⟩
      · refine Or.inr (Pi.le_def.mpr fun j ↦ ?_)
        have := Pi.le_def.mp h j
        simp only [Pi.zero_apply, Pi.neg_apply] at this ⊢
        grind
      · exfalso
        have hkl : k ≠ l := by rintro rfl; simp only [Pi.neg_apply] at h1; grind
        have hceq : c = Pi.single k 1 - Pi.single l 1 := by
          ext j
          simp only [Pi.sub_apply]
          rcases eq_or_ne j k with rfl | hjk
          · rw [Pi.single_eq_same, Pi.single_eq_of_ne hkl, hck1]; ring
          rcases eq_or_ne j l with rfl | hjl
          · have hj := h1
            simp only [Pi.neg_apply] at hj
            rw [Pi.single_eq_of_ne hjk, Pi.single_eq_same]
            grind
          · have hA := hcj j hjk
            have hB := h2 j hjl
            simp only [Pi.neg_apply] at hB
            rw [Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjl]
            grind
        refine hsub k l hkl ⟨p, ?_⟩
        rw [hc, hceq, hsum_single_sub]
    intro p c hm hc
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl le_rfl
    obtain ⟨k, hk⟩ : ∃ k, 0 < c k * ∑ j, c j * A j k := by
      by_contra hcon
      push Not at hcon
      have h1 : c ⬝ᵥ (A * diagonal d) *ᵥ c ≤ 0 := by
        simp only [dotProduct, hmv]
        refine Finset.sum_nonpos fun i _ ↦ ?_
        have h2 : c i * ((∑ j, c j * A j i) * d i) = (c i * ∑ j, c j * A j i) * d i := by ring
        rw [h2]
        exact mul_nonpos_iff.mpr (Or.inr ⟨hcon i, (hd i).le⟩)
      exact absurd (hpos c hc0) (not_lt.mpr h1)
    rcases lt_trichotomy (c k) 0 with h | h | h
    · have hu : ∑ j, c j * A j k < 0 := by nlinarith
      have := main (P.reflectionPerm p p) (-c) (by simpa using hm) (hnegroot p c hc) k
        (by simpa using h) (by rw [hsumneg]; linarith)
      rcases this with h' | h'
      · exact Or.inr (by simpa using neg_nonneg.mp (by simpa using h'))
      · exact Or.inl (by simpa using neg_nonpos.mp (by simpa using h'))
    · rw [h] at hk; simp at hk
    · exact main p c hm hc k h (by nlinarith)

variable (s : Finset ι)
  (h₀ : LinearIndepOn R P.root s)
  (h₀' : LinearIndepOn R P.coroot s)
  (h₁ : (s : Set ι).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0)
  (h₂ : ∀ i, ∃ᵉ (w ∈ Subgroup.closure (Equiv.reflection P '' s)) (j ∈ s), P.root i = w • P.root j)
include h₀' h₁ h₂

lemma bar (i : ι) :
     P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
    -P.root i ∈ AddSubmonoid.closure (P.root '' s) := by
  classical
  have h₂' : ∀ i, ∃ σ ∈ Subgroup.closure (P.reflectionPerm '' s),
      ∃ j ∈ s, i = σ j := by
    intro i
    obtain ⟨w, hw, j, hj, hij⟩ := h₂ i
    obtain ⟨σ, hσ, hσ'⟩ := (P.exists_root_eq_smul_root_iff s i j).mp ⟨w, hw, hij⟩
    exact ⟨σ, hσ, j, hj, hσ'⟩
  have hrs := P.root_mem_span_int_image s h₂'
  have hcs : ∀ i, P.coroot i ∈ Submodule.span ℤ (P.coroot '' s) :=
    P.flip.root_mem_span_int_image s h₂'
  have hA : (Matrix.of fun k l : s ↦ P.pairingIn ℤ k l).IsFiniteCartan :=
    P.isFiniteCartan_pairingIn s h₀' h₁
  obtain ⟨d, hd, hS⟩ := hA.transpose.exists_posDef
  have hS' : ((Matrix.of fun k l : s ↦ P.pairingIn ℤ k l) * diagonal d).PosDef := by
    rw [← Matrix.PosDef.transpose_iff]; simpa using hS
  have huniq : ∀ c c' : s → ℤ,
      ∑ k, c k • P.root k = ∑ k, c' k • P.root k → c = c' := by
    intro c c' h
    have hz : ∑ k, (c - c') k • P.root (k : ι) = 0 := by
      simp_rw [Pi.sub_apply, sub_smul]
      rw [Finset.sum_sub_distrib, h, sub_self]
    have h' := P.eq_zero_of_sum_smul_root_eq_zero s hA hz
    ext k
    simpa [sub_eq_zero] using congrFun h' k
  have hsub : ∀ k l : s, k ≠ l → P.root k - P.root l ∉ range P.root := fun k l hkl ↦
    P.root_sub_root_notMem_range s hcs h₀' h₁ k.2 l.2 (by simpa using hkl)
  obtain ⟨c, hc⟩ : ∃ c : s → ℤ, P.root i = ∑ k, c k • P.root k := by
    have h := hrs i
    rw [Set.image_eq_range] at h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
    exact ⟨c, hc.symm⟩
  rcases P.nonneg_or_nonpos_aux s hA.diag hA.offDiag_nonpos
      (fun i c hc l ↦ P.pairingIn_eq_sum s hc l) huniq hsub d hd hS' _ i c le_rfl hc with h | h
  · exact Or.inl (hc ▸ P.sum_smul_root_mem_closure s h)
  · refine Or.inr ?_
    have h1 : -P.root i = ∑ k, (-c) k • P.root k := by
      rw [hc]; simp [← Finset.sum_neg_distrib]
    rw [h1]
    exact P.sum_smul_root_mem_closure s (by simpa using h)

/-- A alternate condition for a subset of linearly independent (co)roots to form a base.

This is useful when constructing a root pairing from a realisation of a Cartan matrix. -/
public def Base.mk'' :
    P.Base where
  support := s
  linearIndepOn_root := h₀
  linearIndepOn_coroot := h₀'
  root_mem_or_neg_mem := P.bar s h₀' h₁ h₂
  coroot_mem_or_neg_mem i := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
    apply P.flip.bar s h₀ (fun j hj k hk hjk ↦ h₁ hk hj hjk.symm)
    intro j
    obtain ⟨w, hw, k, hk, hjk⟩ := h₂ j
    obtain ⟨σ, hσ, hσ'⟩ := (P.exists_root_eq_smul_root_iff s j k).mp ⟨w, hw, hjk⟩
    obtain ⟨w', hw', hw''⟩ := (P.flip.exists_root_eq_smul_root_iff s j k).mpr ⟨σ, hσ, hσ'⟩
    exact ⟨w', hw', k, hk, hw''⟩

@[simp] lemma Base.mk''_support :
    (Base.mk'' P s h₀ h₀' h₁ h₂).support = s := by
  rfl

end RootPairing
