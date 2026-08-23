/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!

# Realisations of Cartan Matrices

A realisation of a Cartan matrix indexed by `ι`, is a family of vectors `v` and covectors `f`,
both indexed by `ι`, such that `⟨fⱼ, vᵢ⟩ = Aᵢⱼ` for all `i j`. Such a realisation determines a
based root datum for which `v` and `f` are the simple roots and coroots.

We develop this theory here.

## Main definitions / results:
 * `CartanMatrix.Realisation`: the definition of a realisation of a Cartan matrix.
 * `CartanMatrix.Realisation.toRootPairing`: the root pairing obtain from a realisation of a Cartan
   matrix.
 * `Matrix.IsFiniteCartan.toRealisation`: a realisation associated to an invertible Cartan matrix.
 * `Matrix.IsFiniteCartan.toRootPairing`: a reduced, irreducible, crystallographic root system
   assocated to a Cartan matrix, with coefficients in any field of characteristic zero.

-/

noncomputable section

open Function Module Set
open Submodule (span subset_span)
open scoped Matrix

variable (n R M N : Type*) [Fintype n] [DecidableEq n] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace CartanMatrix

/-- A realisation of a Cartan matrix indexed by `ι` is a family of vectors `v` and covectors `f`,
both indexed by `ι`, such that `⟨fⱼ, vᵢ⟩ = Aᵢⱼ` for all `i j`. -/
structure Realisation where
  sRoot : n → M
  sCoroot : n → N
  matrix : Matrix n n ℤ
  isCartan : matrix.IsFiniteCartan
  pairing : M →ₗ[R] N →ₗ[R] R
  isPerfPair : pairing.IsPerfPair
  pairingMatrix (i j : n) : pairing (sRoot i) (sCoroot j) = matrix i j

variable {n R M N}

namespace Realisation

variable (rl : Realisation n R M N)

instance : rl.pairing.IsPerfPair := rl.isPerfPair

/-- The realisation obtained by interchanging the roles of `M` and `N`. -/
protected def flip : Realisation n R N M where
  matrix := rl.matrix.transpose
  isCartan := rl.isCartan.transpose
  pairing := rl.pairing.flip
  isPerfPair := inferInstance
  sRoot := rl.sCoroot
  sCoroot := rl.sRoot
  pairingMatrix := by simp [rl.pairingMatrix]

lemma lin_ind_sRoot [CharZero R] [IsDomain R] : LinearIndependent R rl.sRoot := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h : c ᵥ* (rl.matrix.map (Int.cast : ℤ → R)) = 0 := by
    funext j
    have h0 : rl.pairing (∑ i, c i • rl.sRoot i) (rl.sCoroot j) = 0 := by rw [hc]; simp
    rw [map_sum] at h0
    simpa [Matrix.vecMul, dotProduct, rl.pairingMatrix] using h0
  have key : (rl.matrix.map (Int.cast : ℤ → R)).det ≠ 0 := by
    have h : (rl.matrix.map (Int.cast : ℤ → R)).det = ((rl.matrix.det : ℤ) : R) := by
      simpa using (RingHom.map_det (Int.castRingHom R) rl.matrix).symm
    rw [h]
    exact_mod_cast rl.isCartan.det_ne_zero
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero key h)

lemma lin_ind_sCoroot [CharZero R] [IsDomain R] : LinearIndependent R rl.sCoroot :=
  rl.flip.lin_ind_sRoot

lemma injective_sRoot [CharZero R] [IsDomain R] : Injective rl.sRoot :=
  rl.lin_ind_sRoot.injective

lemma injective_sCoroot [CharZero R] [IsDomain R] : Injective rl.sCoroot :=
  rl.lin_ind_sCoroot.injective

@[simp] lemma pairing_sRoot_sCoroot_self (i : n) :
    rl.pairing (rl.sRoot i) (rl.sCoroot i) = 2 := by
  simp [rl.pairingMatrix, rl.isCartan.diag]

/-- The reflection associated to a simple root. -/
def reflection (i : n) : M ≃ₗ[R] M :=
  Module.reflection (x := rl.sRoot i) (f := rl.pairing.flip (rl.sCoroot i)) <| by simp

/-- The reflection associated to a simple coroot. -/
def coreflection (i : n) : N ≃ₗ[R] N :=
  rl.flip.reflection i

@[simp] lemma reflection_apply (i : n) (x : M) :
    rl.reflection i x = x - rl.pairing x (rl.sCoroot i) • rl.sRoot i := by
  simp [reflection, Module.reflection_apply]

@[simp] lemma coreflection_apply (i : n) (y : N) :
    rl.coreflection i y = y - rl.pairing (rl.sRoot i) y • rl.sCoroot i :=
  rl.flip.reflection_apply i y

@[simp] lemma flip_pairing : rl.flip.pairing = rl.pairing.flip := rfl

@[simp] lemma flip_sRoot : rl.flip.sRoot = rl.sCoroot := rfl

@[simp] lemma flip_sCoroot : rl.flip.sCoroot = rl.sRoot := rfl

@[simp] lemma flip_reflection (i : n) : rl.flip.reflection i = rl.coreflection i := rfl

@[simp] lemma flip_coreflection (i : n) : rl.flip.coreflection i = rl.reflection i := rfl

lemma pairing_reflection_left (i : n) (x : M) (y : N) :
    rl.pairing (rl.reflection i x) y = rl.pairing x (rl.coreflection i y) := by
  simp only [reflection_apply, coreflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

lemma pairing_reflection_coreflection (i : n) (x : M) (y : N) :
    rl.pairing (rl.reflection i x) (rl.coreflection i y) = rl.pairing x y := by
  simp only [reflection_apply, coreflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, pairing_sRoot_sCoroot_self]
  ring

/-- The Weyl group of a realisation. -/
def weylGroup :
    Subgroup ((M ≃ₗ[R] M) × (N ≃ₗ[R] N)) :=
  .closure (range fun i ↦ (rl.reflection i, rl.coreflection i))

lemma mem_weyl (i : n) :
    (rl.reflection i, rl.coreflection i) ∈ rl.weylGroup :=
  Subgroup.subset_closure <| mem_range_self i

lemma flip_weyl :
    rl.flip.weylGroup = rl.weylGroup.map (MulEquiv.prodComm.toMonoidHom) := by
  rw [weylGroup, weylGroup, MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(rl.reflection i, rl.coreflection i), ⟨i, rfl⟩, by simp⟩
  · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp⟩

@[simp] lemma mem_flip_weyl {w : (N ≃ₗ[R] N) × (M ≃ₗ[R] M)} :
    w ∈ rl.flip.weylGroup ↔ (w.2, w.1) ∈ rl.weylGroup := by
  obtain ⟨a, b⟩ := w
  simp [flip_weyl]

lemma map_fst_weyl :
    rl.weylGroup.map (MonoidHom.fst _ _) = .closure (range rl.reflection) := by
  rw [weylGroup, MonoidHom.map_closure]
  congr 1
  aesop

lemma map_snd_weyl :
    rl.weylGroup.map (MonoidHom.snd _ _) = .closure (range rl.coreflection) := by
  rw [weylGroup, MonoidHom.map_closure]
  congr 1
  aesop

lemma pairing_apply_apply_of_mem_weyl {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)}
    (hw : w ∈ rl.weylGroup) (x : M) (y : N) :
    rl.pairing (w.1 x) (w.2 y) = rl.pairing x y := by
  revert x y
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    exact rl.pairing_reflection_coreflection i
  | one => simp
  | mul u v _ _ hu hv => exact fun x y ↦ (hu (v.1 x) (v.2 y)).trans (hv x y)
  | inv u _ hu =>
    intro x y
    rw [← hu (u⁻¹.1 x) (u⁻¹.2 y)]
    simp

instance : SMul rl.weylGroup (M × N) where smul w p := (w.1.1 p.1, w.1.2 p.2)

lemma weylGroup_smul_def (w : rl.weylGroup) (p : M × N) : w • p = (w.1.1 p.1, w.1.2 p.2) := rfl

instance : DistribMulAction rl.weylGroup (M × N) where
  mul_smul := by simp [weylGroup_smul_def]
  one_smul := by simp [weylGroup_smul_def]
  smul_zero := by simp [weylGroup_smul_def]
  smul_add := by simp [weylGroup_smul_def]

/-- The orbit of the action of the Weyl group on the set of simple root, coroot pairs. -/
def idx : Set (M × N) := {(w.1 (rl.sRoot i), w.2 (rl.sCoroot i)) | (w ∈ rl.weylGroup) (i)}

open scoped Pointwise in
lemma idx_eq_smul :
    rl.idx = (univ : Set rl.weylGroup) • (range fun i ↦ (rl.sRoot i, rl.sCoroot i)) := by
  ext; simp [idx, weylGroup_smul_def, ← Set.image2_smul]

lemma mk_mem_idx {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw : w ∈ rl.weylGroup) (i : n) :
    (w.1 (rl.sRoot i), w.2 (rl.sCoroot i)) ∈ rl.idx :=
  ⟨w, hw, i, rfl⟩

lemma sPair_mem_idx (i : n) :
    (rl.sRoot i, rl.sCoroot i) ∈ rl.idx :=
  rl.mk_mem_idx (one_mem _) i

lemma apply_mem_idx {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw : w ∈ rl.weylGroup)
    {p : M × N} (hp : p ∈ rl.idx) :
    (w.1 p.1, w.2 p.2) ∈ rl.idx := by
  obtain ⟨v, hv, i, rfl⟩ := hp
  exact rl.mk_mem_idx (mul_mem hw hv) i

@[simp] lemma flip_idx : rl.flip.idx = Prod.swap '' rl.idx := by
  ext p
  constructor
  · rintro ⟨w, hw, i, rfl⟩
    exact ⟨_, rl.mk_mem_idx (rl.mem_flip_weyl.mp hw) i, rfl⟩
  · rintro ⟨-, ⟨w, hw, i, rfl⟩, rfl⟩
    exact ⟨(w.2, w.1), rl.mem_flip_weyl.mpr hw, i, rfl⟩

lemma pairing_fst_snd {p : M × N} (hp : p ∈ rl.idx) :
    rl.pairing p.1 p.2 = 2 := by
  obtain ⟨w, hw, i, rfl⟩ := hp
  simpa using rl.pairing_apply_apply_of_mem_weyl hw (rl.sRoot i) (rl.sCoroot i)

lemma exists_mem_weyl_of_mem_idx {p : M × N} (hp : p ∈ rl.idx) :
    ∃ w ∈ rl.weylGroup,
      (∀ x : M, w.1 x = x - rl.pairing x p.2 • p.1) ∧
      (∀ y : N, w.2 y = y - rl.pairing p.1 y • p.2) := by
  obtain ⟨v, hv, i, rfl⟩ := hp
  refine ⟨v * (rl.reflection i, rl.coreflection i) * v⁻¹,
    mul_mem (mul_mem hv (rl.mem_weyl i)) (inv_mem hv), fun x ↦ ?_, fun y ↦ ?_⟩
  · have h : rl.pairing x (v.2 (rl.sCoroot i)) = rl.pairing (v.1.symm x) (rl.sCoroot i) := by
      rw [← rl.pairing_apply_apply_of_mem_weyl hv (v.1.symm x) (rl.sCoroot i)]
      simp
    change v.1 (rl.reflection i (v.1.symm x)) = _
    simp [h]
  · have h : rl.pairing (v.1 (rl.sRoot i)) y = rl.pairing (rl.sRoot i) (v.2.symm y) := by
      rw [← rl.pairing_apply_apply_of_mem_weyl hv (rl.sRoot i) (v.2.symm y)]
      simp
    change v.2 (rl.coreflection i (v.2.symm y)) = _
    simp [h]

lemma mapsTo_preReflection_fst {p : M × N} (hp : p ∈ rl.idx) :
    MapsTo (preReflection p.1 (rl.pairing.flip p.2)) (Prod.fst '' rl.idx) (Prod.fst '' rl.idx) := by
  obtain ⟨w, hw, h₁, -⟩ := rl.exists_mem_weyl_of_mem_idx hp
  rintro - ⟨q, hq, rfl⟩
  exact ⟨_, rl.apply_mem_idx hw hq, by simp [preReflection_apply, h₁]⟩

lemma mapsTo_preReflection_snd {p : M × N} (hp : p ∈ rl.idx) :
    MapsTo (preReflection p.2 (rl.pairing p.1)) (Prod.snd '' rl.idx) (Prod.snd '' rl.idx) := by
  obtain ⟨w, hw, -, h₂⟩ := rl.exists_mem_weyl_of_mem_idx hp
  rintro - ⟨q, hq, rfl⟩
  exact ⟨_, rl.apply_mem_idx hw hq, by simp [preReflection_apply, h₂]⟩

@[simp] lemma reflection_symm (i : n) : (rl.reflection i).symm = rl.reflection i := rfl

@[simp] lemma coreflection_symm (i : n) : (rl.coreflection i).symm = rl.coreflection i := rfl

lemma apply_mem_span_of_mem_weyl {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw : w ∈ rl.weylGroup) :
    (∀ x ∈ span R (range rl.sRoot),
      w.1 x ∈ span R (range rl.sRoot) ∧ w.1.symm x ∈ span R (range rl.sRoot)) ∧
    (∀ y ∈ span R (range rl.sCoroot),
      w.2 y ∈ span R (range rl.sCoroot) ∧ w.2.symm y ∈ span R (range rl.sCoroot)) := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    have h₁ : ∀ x ∈ span R (range rl.sRoot), rl.reflection i x ∈ span R (range rl.sRoot) := by
      intro x hx
      exact sub_mem hx <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self i
    have h₂ : ∀ y ∈ span R (range rl.sCoroot),
        rl.coreflection i y ∈ span R (range rl.sCoroot) := by
      intro y hy
      exact sub_mem hy <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self i
    exact ⟨fun x hx ↦ ⟨h₁ x hx, h₁ x hx⟩, fun y hy ↦ ⟨h₂ y hy, h₂ y hy⟩⟩
  | one => exact ⟨fun x hx ↦ ⟨hx, hx⟩, fun y hy ↦ ⟨hy, hy⟩⟩
  | mul u v _ _ hu hv =>
    exact ⟨fun x hx ↦ ⟨(hu.1 _ (hv.1 x hx).1).1, (hv.1 _ (hu.1 x hx).2).2⟩,
      fun y hy ↦ ⟨(hu.2 _ (hv.2 y hy).1).1, (hv.2 _ (hu.2 y hy).2).2⟩⟩
  | inv u _ hu =>
    exact ⟨fun x hx ↦ ⟨(hu.1 x hx).2, (hu.1 x hx).1⟩,
      fun y hy ↦ ⟨(hu.2 y hy).2, (hu.2 y hy).1⟩⟩

lemma fst_mem_span {p : M × N} (hp : p ∈ rl.idx) :
    p.1 ∈ span R (range rl.sRoot) := by
  obtain ⟨w, hw, i, rfl⟩ := hp
  exact ((rl.apply_mem_span_of_mem_weyl hw).1 _ (subset_span (mem_range_self i))).1

lemma snd_mem_span {p : M × N} (hp : p ∈ rl.idx) :
    p.2 ∈ span R (range rl.sCoroot) := by
  replace hp : p.swap ∈ rl.flip.idx := by simpa
  simpa using rl.flip.fst_mem_span hp

/-- Pairs whose coroot is the integral combination `b` of the simple coroots and whose root is,
after scaling by `d i`, the corresponding `d`-weighted combination of the simple roots.

This is the graph of the map sending a coroot to its root, in coordinates.

TODO Think about this. -/
def coordSet (d : n → ℤ) : Set (M × N) :=
  {p | ∃ (i : n) (b : n → ℤ), p.2 = ∑ j, b j • rl.sCoroot j ∧
    d i • p.1 = ∑ j, (b j * d j) • rl.sRoot j}

lemma sPair_mem_coordSet {d : n → ℤ} (i : n) :
    (rl.sRoot i, rl.sCoroot i) ∈ rl.coordSet d := by
  refine ⟨i, Pi.single i 1, ?_, ?_⟩ <;>
  · simp [Pi.single_apply, ite_smul, ite_mul, Finset.sum_ite_eq']

lemma reflection_mem_coordSet {d : n → ℤ}
    (hd : ∀ i j, d i * rl.matrix i j = d j * rl.matrix j i) (i : n)
    {p : M × N} (hp : p ∈ rl.coordSet d) :
    (rl.reflection i p.1, rl.coreflection i p.2) ∈ rl.coordSet d := by
  obtain ⟨i₀, b, h2, h1⟩ := hp
  set z : ℤ := ∑ j, b j * rl.matrix i j with hz
  have hZ : ∑ j, b j * d j * rl.matrix j i = d i * z := by
    rw [hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by linear_combination b j * hd j i
  have hPx : (d i₀ : R) * rl.pairing p.1 (rl.sCoroot i) = ((d i * z : ℤ) : R) := by
    have h : (d i₀ : R) * rl.pairing p.1 (rl.sCoroot i) =
        rl.pairing (d i₀ • p.1) (rl.sCoroot i) := by
      simp [map_zsmul, zsmul_eq_mul]
    rw [h, h1, ← hZ, map_sum]
    simp only [LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, rl.pairingMatrix,
      zsmul_eq_mul]
    push_cast
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  refine ⟨i₀, b - z • Pi.single i 1, ?_, ?_⟩
  · have hPy : rl.pairing (rl.sRoot i) p.2 = (z : R) := by
      rw [h2]
      simp [rl.pairingMatrix, hz]
    rw [coreflection_apply, hPy, h2]
    simp [Pi.single_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, Finset.sum_ite_eq',
      Int.cast_smul_eq_zsmul]
  · have hsm : d i₀ • (rl.pairing p.1 (rl.sCoroot i) • rl.sRoot i) =
        ((d i * z : ℤ) : R) • rl.sRoot i := by
      rw [← smul_assoc, zsmul_eq_mul, hPx]
    rw [reflection_apply, smul_sub, h1, hsm, Int.cast_smul_eq_zsmul]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, sub_mul, sub_smul,
      Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [mul_comm]

lemma apply_mem_coordSet {d : n → ℤ} (hd : ∀ i j, d i * rl.matrix i j = d j * rl.matrix j i)
    {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw : w ∈ rl.weylGroup) :
    ∀ p ∈ rl.coordSet d, (w.1 p.1, w.2 p.2) ∈ rl.coordSet d ∧
      (w.1.symm p.1, w.2.symm p.2) ∈ rl.coordSet d := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact fun p hp ↦ ⟨rl.reflection_mem_coordSet hd i hp, rl.reflection_mem_coordSet hd i hp⟩
  | one => exact fun p hp ↦ ⟨hp, hp⟩
  | mul u v _ _ hu hv => exact fun p hp ↦ ⟨(hu _ (hv p hp).1).1, (hv _ (hu p hp).2).2⟩
  | inv u _ hu => exact fun p hp ↦ ⟨(hu p hp).2, (hu p hp).1⟩

lemma exists_coords [CharZero R] {d : n → ℤ} (hd : ∀ i j, d i * rl.matrix i j = d j * rl.matrix j i)
    {p : M × N} (hp : p ∈ rl.idx) :
    ∃ (i : n) (b : n → ℤ), b ⬝ᵥ (Matrix.diagonal d * rl.matrix) *ᵥ b = 2 * d i ∧
      p.2 = ∑ j, b j • rl.sCoroot j ∧ d i • p.1 = ∑ j, (b j * d j) • rl.sRoot j := by
  obtain ⟨i₀, b, h2, h1⟩ :
      p ∈ rl.coordSet d := by
    obtain ⟨w, hw, i, rfl⟩ := hp
    exact (rl.apply_mem_coordSet hd hw _ (rl.sPair_mem_coordSet i)).1
  refine ⟨i₀, b, ?_, h2, h1⟩
  have key : ((b ⬝ᵥ (Matrix.diagonal d * rl.matrix) *ᵥ b : ℤ) : R) = ((2 * d i₀ : ℤ) : R) := by
    have e1 : ((2 * d i₀ : ℤ) : R) = rl.pairing (d i₀ • p.1) p.2 := by
      rw [map_zsmul, LinearMap.smul_apply, rl.pairing_fst_snd hp, zsmul_eq_mul]
      push_cast
      ring
    rw [e1, h1, h2, map_sum]
    simp only [LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, map_sum, zsmul_eq_mul,
      rl.pairingMatrix, dotProduct, Matrix.mulVec, Matrix.diagonal_mul]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  exact_mod_cast key

variable [CharZero R] [IsDomain R] [IsTorsionFree R M] [IsTorsionFree R N]

instance : Finite rl.idx := by
  obtain ⟨d, hd_pos, hG⟩ := rl.isCartan.exists_posDef
  set G : Matrix n n ℤ := Matrix.diagonal d * rl.matrix with hGdef
  have hd : ∀ i j, d i * rl.matrix i j = d j * rl.matrix j i := hG.mul_comm_of_diagonal_mul
  choose i b hnorm h2 h1 using fun p : rl.idx ↦ rl.exists_coords hd p.2
  set K : ℤ := 2 * ∑ j, d j with hK
  have hbK : ∀ p : rl.idx, b p ⬝ᵥ G *ᵥ b p ≤ K := fun p ↦ by
    rw [hnorm p, hK]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ ↦ (hd_pos j).le) (Finset.mem_univ _)) (by norm_num)
  have _i : Finite ↥{c : n → ℤ | c ⬝ᵥ G *ᵥ c ≤ K} :=
    (hG.finite_setOf_dotProduct_mulVec_le K).to_subtype
  have _i : IsAddTorsionFree M := .of_isTorsionFree R M
  refine Finite.of_injective
    (fun p ↦ (i p, (⟨b p, hbK p⟩ : ↥{c : n → ℤ | c ⬝ᵥ G *ᵥ c ≤ K}))) ?_
  rintro p q hpq
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hpq
  obtain ⟨hi, hb⟩ := hpq
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have h : d (i p) • (p : M × N).1 = d (i p) • (q : M × N).1 := by
      rw [h1 p, hb, hi, ← h1 q]
    exact zsmul_right_injective (G := M) (hd_pos (i p)).ne' h
  · rw [h2 p, h2 q, hb]

omit [IsTorsionFree R M] [IsTorsionFree R N] in
lemma eq_zero_of_pairing_sRoot_eq_zero {v : N} (hv : v ∈ span R (range rl.sCoroot))
    (h : ∀ i, rl.pairing (rl.sRoot i) v = 0) :
    v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hv
  have hdet : (rl.matrix.map (Int.cast : ℤ → R)).det ≠ 0 := by
    have : (rl.matrix.map (Int.cast : ℤ → R)).det = ((rl.matrix.det : ℤ) : R) := by
      simpa using (RingHom.map_det (Int.castRingHom R) rl.matrix).symm
    rw [this]
    exact_mod_cast rl.isCartan.det_ne_zero
  suffices c = 0 by simp [this]
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet (funext fun i ↦ ?_)
  simpa [Matrix.mulVec, dotProduct, rl.pairingMatrix, mul_comm] using h i

omit [IsTorsionFree R N] in
lemma injOn_fst : InjOn Prod.fst rl.idx := by
  intro p hp q hq h
  have hfin : (Prod.fst '' rl.idx).Finite := Set.toFinite _
  have hx : p.1 ∈ span R (Prod.fst '' rl.idx) := subset_span ⟨p, hp, rfl⟩
  have hf₁ : (rl.pairing.flip p.2) p.1 = 2 := by simpa using rl.pairing_fst_snd hp
  have hg₁ : (rl.pairing.flip q.2) p.1 = 2 := by
    rw [h]; simpa using rl.pairing_fst_snd hq
  have hg₂ : MapsTo (preReflection p.1 (rl.pairing.flip q.2))
      (Prod.fst '' rl.idx) (Prod.fst '' rl.idx) := by
    rw [h]; exact rl.mapsTo_preReflection_fst hq
  have key := Dual.eq_of_preReflection_mapsTo' hfin hx hf₁ (rl.mapsTo_preReflection_fst hp) hg₁ hg₂
  refine Prod.ext h (sub_eq_zero.mp <| rl.eq_zero_of_pairing_sRoot_eq_zero
    (sub_mem (rl.snd_mem_span hp) (rl.snd_mem_span hq)) fun i ↦ ?_)
  have hi : rl.sRoot i ∈ span R (Prod.fst '' rl.idx) :=
    subset_span ⟨(rl.sRoot i, rl.sCoroot i), rl.sPair_mem_idx i, rfl⟩
  have := LinearMap.congr_fun key ⟨rl.sRoot i, hi⟩
  simp only [LinearMap.dualMap_apply, Submodule.subtype_apply, LinearMap.flip_apply] at this
  simp [this]

omit [IsTorsionFree R M] in
/-- Dually, a coroot determines its root. This is `injOn_fst` for the flipped realisation. -/
lemma injOn_snd : InjOn Prod.snd rl.idx := fun p hp q hq h ↦ by
  replace hp : p.swap ∈ rl.flip.idx := by simpa [flip_idx]
  replace hq : q.swap ∈ rl.flip.idx := by simpa [flip_idx]
  simpa using rl.flip.injOn_fst hp hq h

abbrev root : rl.idx ↪ M :=
  ⟨fun p ↦ (p : M × N).1, fun p q hpq ↦ Subtype.ext <| rl.injOn_fst p.2 q.2 hpq⟩

abbrev coroot : rl.idx ↪ N :=
  ⟨fun p ↦ (p : M × N).2, fun p q hpq ↦ Subtype.ext <| rl.injOn_snd p.2 q.2 hpq⟩

omit [IsTorsionFree R N] in
@[simp] lemma root_apply (p : rl.idx) : rl.root p = (p : M × N).1 := rfl

omit [IsTorsionFree R M] in
@[simp] lemma coroot_apply (p : rl.idx) : rl.coroot p = (p : M × N).2 := rfl

lemma mapsTo_reflection_root (i : rl.idx) :
    MapsTo (preReflection (rl.root i) (rl.pairing.flip (rl.coroot i)))
      (range rl.root) (range rl.root) := by
  obtain ⟨w, hw, h₁, -⟩ := rl.exists_mem_weyl_of_mem_idx i.2
  rw [show range rl.root = Prod.fst '' rl.idx by aesop]
  rintro - ⟨p, hp, rfl⟩
  exact ⟨_, rl.apply_mem_idx hw hp, by simp [preReflection_apply, h₁]⟩

lemma mapsTo_reflection_coroot (i : rl.idx) :
    MapsTo (preReflection (rl.coroot i) (rl.pairing (rl.root i)))
      (range rl.coroot) (range rl.coroot) := by
  obtain ⟨w, hw, -, h₂⟩ := rl.exists_mem_weyl_of_mem_idx i.2
  rw [show range rl.coroot = Prod.snd '' rl.idx by aesop]
  rintro - ⟨p, hp, rfl⟩
  exact ⟨_, rl.apply_mem_idx hw hp, by simp [preReflection_apply, h₂]⟩

variable {ι : Type*} (e : ι ≃ rl.idx)

/-- The root pairing associated to a realisation of a Cartan matrix. -/
def toRootPairing :
    RootPairing ι R M N :=
  have : Finite ι := e.finite_iff.mpr inferInstance
  .mk' rl.pairing (e.toEmbedding.trans rl.root) (e.toEmbedding.trans rl.coroot)
    (fun i ↦ rl.pairing_fst_snd (e i).2)
    (fun i ↦ by
      rw [show range (e.toEmbedding.trans rl.root) = range rl.root by simp]
      exact rl.mapsTo_reflection_root (e i))
    (fun i ↦ by
      rw [show range (e.toEmbedding.trans rl.coroot) = range rl.coroot by simp]
      exact rl.mapsTo_reflection_coroot (e i))

@[simp] lemma toRootPairing_root (i : ι) :
    (rl.toRootPairing e).root i = ((e i : M × N)).1 := rfl

@[simp] lemma toRootPairing_coroot (i : ι) :
    (rl.toRootPairing e).coroot i = ((e i : M × N)).2 := rfl

@[simp] lemma toRootPairing_toLinearMap :
    (rl.toRootPairing e).toLinearMap = rl.pairing := rfl

lemma toRootPairing_pairing (i j : ι) :
    (rl.toRootPairing e).pairing i j = rl.pairing ((e i : M × N)).1 ((e j : M × N)).2 := rfl

omit [IsDomain R] [IsTorsionFree R M] [IsTorsionFree R N] in
lemma exists_intCoords {p : M × N} (hp : p ∈ rl.idx) :
    ∃ c b : n → ℤ, p.1 = ∑ i, c i • rl.sRoot i ∧ p.2 = ∑ i, b i • rl.sCoroot i := by
  obtain ⟨d, -, hG⟩ := rl.isCartan.exists_posDef
  obtain ⟨-, b, -, hb, -⟩ := rl.exists_coords hG.mul_comm_of_diagonal_mul hp
  obtain ⟨d', -, hG'⟩ := rl.flip.isCartan.exists_posDef
  have hp' : p.swap ∈ rl.flip.idx := by rw [flip_idx]; exact ⟨p, hp, rfl⟩
  obtain ⟨-, c, -, hc, -⟩ := rl.flip.exists_coords hG'.mul_comm_of_diagonal_mul hp'
  exact ⟨c, b, by simpa using hc, hb⟩

lemma isCrystallographic_toRootPairing :
    (rl.toRootPairing e).IsCrystallographic where
  exists_value i j := by
    suffices ∀ {p q : M × N} (hp : p ∈ rl.idx) (hq : q ∈ rl.idx),
        ∃ z : ℤ, (z : R) = rl.pairing p.1 q.2 by
      obtain ⟨z, hz⟩ := this (e i).2 (e j).2
      exact ⟨z, by simpa [toRootPairing_pairing] using hz⟩
    intro p q hp hq
    obtain ⟨c, -, hc, -⟩ := rl.exists_intCoords hp
    obtain ⟨-, b, -, hb⟩ := rl.exists_intCoords hq
    refine ⟨∑ i, ∑ j, c i * b j * rl.matrix i j, ?_⟩
    rw [hc, hb, map_sum]
    simp only [LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, map_sum, zsmul_eq_mul,
      rl.pairingMatrix]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

omit [IsTorsionFree R M] [IsTorsionFree R N] in
lemma eq_one_or_neg_one_of_eq_zsmul_sRoot {p : M × N} (hp : p ∈ rl.idx) {z : ℤ} {m : n}
    (h : p.1 = (z : R) • rl.sRoot m) :
    z = 1 ∨ z = -1 := by
  obtain ⟨w, hw, l, hwl⟩ := hp
  obtain ⟨c, -, hc, -⟩ := rl.exists_intCoords (rl.mk_mem_idx (inv_mem hw) m)
  have h1 : rl.sRoot l = ∑ k, ((z * c k : ℤ) : R) • rl.sRoot k := by
    have h2 : w.1 (rl.sRoot l) = (z : R) • rl.sRoot m := by rw [← h, ← hwl]
    have h3 : rl.sRoot l = (z : R) • w.1.symm (rl.sRoot m) := by
      rw [← map_smul, ← h2, LinearEquiv.symm_apply_apply]
    rw [h3, show w.1.symm (rl.sRoot m) = ∑ k, c k • rl.sRoot k from hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul R, smul_smul]
    push_cast
    ring_nf
  have h4 := Fintype.linearIndependent_iffₛ.mp rl.lin_ind_sRoot
    (fun k ↦ ((z * c k : ℤ) : R)) (fun k ↦ if k = l then 1 else 0) (by simpa using h1.symm) l
  simp only [ite_eq_left] at h4
  exact Int.eq_one_or_neg_one_of_mul_eq_one (v := c l) (by exact_mod_cast h4)

lemma isReduced_toRootPairing :
    (rl.toRootPairing e).IsReduced where
  eq_or_eq_neg i j hij := by
    simp only [toRootPairing_root] at hij ⊢
    set p : M × N := (↑(e i) : M × N) with hp'
    set q : M × N := (↑(e j) : M × N) with hq'
    have hp : p ∈ rl.idx := (e i).2
    have hq : q ∈ rl.idx := (e j).2
    have hq0 : q.1 ≠ 0 := by
      intro contra
      have h2 := rl.pairing_fst_snd hq
      rw [contra] at h2
      simp at h2
    rw [LinearIndependent.pair_iff] at hij
    push Not at hij
    obtain ⟨s, t, hst, hst0⟩ := hij
    have hs : s ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add, smul_eq_zero] at hst
      rcases hst with rfl | h
      · exact hst0 rfl rfl
      · exact hq0 h
    obtain ⟨w, hw, l, hwl⟩ := hq
    obtain ⟨c, -, hγ₀, -⟩ := rl.exists_intCoords (rl.apply_mem_idx (inv_mem hw) hp)
    have hγ : w.1.symm p.1 = ∑ k, c k • rl.sRoot k := hγ₀
    have hlq : w.1 (rl.sRoot l) = q.1 := by rw [← hwl]
    have hql : w.1.symm q.1 = rl.sRoot l := by rw [← hlq, LinearEquiv.symm_apply_apply]
    have hrel : ∑ k, (s * ((c k : R)) + (if k = l then t else 0)) • rl.sRoot k = 0 := by
      have h0 : w.1.symm (s • p.1 + t • q.1) = 0 := by rw [hst, map_zero]
      rw [map_add, map_smul, map_smul, hγ, hql] at h0
      rw [← h0, Finset.smul_sum]
      simp only [add_smul, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← Int.cast_smul_eq_zsmul R, smul_smul]
    have hcoeff := Fintype.linearIndependent_iff.mp rl.lin_ind_sRoot _ hrel
    have hck : ∀ k, k ≠ l → (c k : R) = 0 := by
      intro k hk
      have h3 := hcoeff k
      simp only [hk, reduceIte, add_zero, mul_eq_zero] at h3
      tauto
    have hγ' : w.1.symm p.1 = ((c l : ℤ) : R) • rl.sRoot l := by
      rw [hγ, Finset.sum_eq_single l]
      · rw [Int.cast_smul_eq_zsmul]
      · intro k _ hk
        rw [← Int.cast_smul_eq_zsmul R, hck k hk, zero_smul]
      · simp
    have hpm1 := rl.eq_one_or_neg_one_of_eq_zsmul_sRoot (rl.apply_mem_idx (inv_mem hw) hp) hγ'
    have hpq : p.1 = ((c l : ℤ) : R) • q.1 := by
      conv_lhs => rw [show p.1 = w.1 (w.1.symm p.1) by simp]
      rw [hγ', map_smul, hlq]
    rcases hpm1 with h1 | h1 <;> rw [h1] at hpq <;>
      simp only [Int.cast_one, one_smul, Int.cast_neg, neg_smul] at hpq
    · exact Or.inl hpq
    · exact Or.inr hpq

lemma isRootSystem_toRootPairing
    (hr : span R (range rl.sRoot) = ⊤)
    (hc : span R (range rl.sCoroot) = ⊤) :
    (rl.toRootPairing e).IsRootSystem where
  span_root_eq_top := by
    rw [eq_top_iff, ← hr]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨i, rfl⟩
    exact Submodule.subset_span ⟨e.symm ⟨_, rl.sPair_mem_idx i⟩, by simp⟩
  span_coroot_eq_top := by
    rw [eq_top_iff, ← hc]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨i, rfl⟩
    exact Submodule.subset_span ⟨e.symm ⟨_, rl.sPair_mem_idx i⟩, by simp⟩

lemma isIrreducible_toRootPairing [Nonempty n] {ι k V W : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (rl : Realisation n k V W) (e : ι ≃ rl.idx)
    (hr : span k (range rl.sRoot) = ⊤)
    (hc : span k (range rl.sCoroot) = ⊤)
    (hA' : rl.matrix.IsIndecomposable) :
    (rl.toRootPairing e).IsIrreducible := by
  classical
  have _i : Inhabited n := Classical.inhabited_of_nonempty inferInstance
  have _i : Nontrivial V := by
    refine nontrivial_of_ne (rl.sRoot default) 0 fun contra ↦ ?_
    simpa [contra] using rl.pairing_sRoot_sCoroot_self default
  set P := rl.toRootPairing e with hP
  have _i : P.IsRootSystem := rl.isRootSystem_toRootPairing e hr hc
  -- the index of the `a`-th simple root
  set f : n → ι := fun a ↦ e.symm ⟨(rl.sRoot a, rl.sCoroot a), rl.sPair_mem_idx a⟩ with hf
  have hroot : ∀ a, P.root (f a) = rl.sRoot a := by simp [hP, hf]
  have hpair : ∀ a b, P.pairing (f a) (f b) = (rl.matrix a b : k) := by
    intro a b
    rw [hP, toRootPairing_pairing, hf]
    simp only [Equiv.apply_symm_apply]
    exact rl.pairingMatrix a b
  have hcoroot' : ∀ (a : n) (x : V), P.coroot' (f a) x = rl.pairing x (rl.sCoroot a) := by
    intro a x
    simp [hP, RootPairing.coroot', hf]
  refine RootPairing.IsIrreducible.mk' P fun q hq hq0 ↦ ?_
  refine RootPairing.eq_top_of_mem_invtSubmodule_of_forall_eq_univ P q hq0 hq
    fun Φ hΦ hΦq hΦker ↦ ?_
  -- the simple roots lying in `q` give a block decomposition of `rl.matrix`
  set b : n → ℕ := fun a ↦ if f a ∈ Φ then 1 else 0 with hb
  have hbt : rl.matrix.BlockTriangular b := by
    intro i j hij
    have h1 : f i ∈ Φ := by by_contra h; simp [hb, h] at hij
    have h2 : f j ∉ Φ := by intro h; simp [hb, h, h1] at hij
    have h3 : P.coroot' (f j) (P.root (f i)) = 0 := hΦker (f j) h2 (hΦq ⟨f i, h1, rfl⟩)
    rw [RootPairing.root_coroot'_eq_pairing, hpair] at h3
    exact_mod_cast h3
  obtain ⟨v, hv⟩ :=
    (Matrix.isIndecomposable_iff_blockTriangular_const (α := ℕ) rl.matrix).mp hA' b hbt
  rcases eq_or_ne v 0 with rfl | hv0
  · -- no simple root meets `q`, so `q` is trivial
    refine absurd ?_ hq0
    have hfa : ∀ a, f a ∉ Φ := fun a h ↦ by simpa [hb, h] using congr_fun hv a
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : rl.pairing x = 0 := by
      refine LinearMap.ext_on hc ?_
      rintro - ⟨a, rfl⟩
      have h4 := hΦker (f a) (hfa a) hx
      rw [LinearMap.mem_ker, hcoroot'] at h4
      simpa using h4
    have h5 := (LinearMap.IsPerfPair.bijective_left rl.pairing).injective (a₁ := x) (a₂ := 0)
    simpa using h5 (by simpa using hx0)
  · -- every simple root lies in `q`, so `q = ⊤` and hence `Φ` is everything
    have hfa : ∀ a, f a ∈ Φ := by
      intro a
      by_contra h
      exact hv0 (by simpa [hb, h] using (congr_fun hv a).symm)
    have hqtop : q = ⊤ := by
      rw [eq_top_iff, ← hr]
      refine Submodule.span_le.mpr ?_
      rintro - ⟨a, rfl⟩
      exact hΦq ⟨f a, hfa a, hroot a⟩
    rw [Set.eq_univ_iff_forall]
    intro j
    by_contra hj
    have h1 : P.coroot' j (P.root j) = 0 := hΦker j hj (hqtop ▸ Submodule.mem_top)
    rw [RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same] at h1
    exact two_ne_zero h1

end Realisation

end CartanMatrix

namespace Matrix.IsFiniteCartan

variable {n R M N} {A : Matrix n n ℤ} (hA : A.IsFiniteCartan)

/-- If Cartan matrix is invertible in `R` then it has a canonical realisation. -/
def toRealisation (hAI : Invertible <| A.map (Int.cast : ℤ → R)) :
    CartanMatrix.Realisation n R (n → R) (n → R) where
  matrix := A
  isCartan := hA
  pairing := ((toLinearEquiv' _ hAI).trans (dotProductEquiv R n)).flip
  isPerfPair := LinearEquiv.instIsPerfPair _
  sRoot i := Pi.single i 1
  sCoroot i := Pi.single i 1
  pairingMatrix := by simp [toLinearEquiv']

variable (k : Type*) [Field k] [CharZero k]
  {ι : Type*} (e : ι ≃ (hA.toRealisation (hA.isUnit_map k).invertible).idx)

private lemma span_range_sRoot_eq_top :
    span k (range (hA.toRealisation (hA.isUnit_map k).invertible).sRoot) = ⊤ := by
  suffices (hA.toRealisation (hA.isUnit_map k).invertible).sRoot = Pi.basisFun k n by simp [this]
  ext; simp [toRealisation]

/-- Given a field `k` of chacteristic zero and Cartan matrix `A`, this is a reduced
crystrallographic root system over `k`. It carries a natural base with Cartan matrix `A`. -/
def toRootPairing := (hA.toRealisation (hA.isUnit_map k).invertible).toRootPairing e

lemma isReduced_toRootPairing :
    (hA.toRootPairing k e).IsReduced :=
  CartanMatrix.Realisation.isReduced_toRootPairing _ e

lemma isCrystallographic_toRootPairing :
    (hA.toRootPairing k e).IsCrystallographic :=
  CartanMatrix.Realisation.isCrystallographic_toRootPairing _ e

lemma isRootSystem_toRootPairing :
    (hA.toRootPairing k e).IsRootSystem :=
  CartanMatrix.Realisation.isRootSystem_toRootPairing _ e (hA.span_range_sRoot_eq_top k)
    (hA.transpose.span_range_sRoot_eq_top k)

lemma isIrreducible_toRootPairing [Nonempty n] (hA' : A.IsIndecomposable) :
    (hA.toRootPairing k e).IsIrreducible :=
  CartanMatrix.Realisation.isIrreducible_toRootPairing _ e (hA.span_range_sRoot_eq_top k)
    (hA.transpose.span_range_sRoot_eq_top k) hA'

end Matrix.IsFiniteCartan
