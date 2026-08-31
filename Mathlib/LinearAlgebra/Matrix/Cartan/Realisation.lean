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

Let `R` be an integral domain of characteristic zero, and let `M` and `N` be `R`-modules in perfect
pairing. Then, given vectors `r₁, r₂, …, rₗ` in `M` and `c₁, c₂, …, cₗ` in `N`, the following two
propositions are equivalent:
1. The vectors `rᵢ`, `cᵢ` are the simple roots and coroots of a finite, reduced, crystrallographic
   root pairing (i.e., a root datum except we do not require `R = ℤ`).
2. The matrix `Aᵢⱼ = ⟨cⱼ, rᵢ⟩` is a finite-type Cartan matrix.

The definition `RootPairing` formalises item 1 above. Here we introduce `CartanMatrix.Realisation`
to formalise item 2.

## Main definitions / results:
 * `CartanMatrix.Realisation`: the definition of a realisation of a Cartan matrix.
 * `CartanMatrix.Realisation.toRootPairing`: the root pairing obtain from a realisation of a Cartan
   matrix.
 * `Matrix.IsFiniteCartan.toRealisation`: a realisation associated to an invertible Cartan matrix.
 * `Matrix.IsFiniteCartan.toRootPairing`: a reduced, irreducible, crystallographic root system
   assocated to a Cartan matrix, with coefficients in any field of characteristic zero.

-/

public noncomputable section

open Function Matrix Module Set
open Submodule (span subset_span)

variable (n R M N : Type*) [Fintype n] [DecidableEq n] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace CartanMatrix

/-- A realisation of a Cartan matrix indexed by `ι` is a family of vectors `v` and covectors `f`,
both indexed by `ι`, such that `⟨fⱼ, vᵢ⟩ = Aᵢⱼ` for all `i j`. -/
structure Realisation where
  /-- The simple roots. -/
  sRoot : n → M
  /-- The simple coroots. -/
  sCoroot : n → N
  /-- The Cartan matrix. -/
  matrix : Matrix n n ℤ
  isCartan : matrix.IsFiniteCartan
  /-- The perfect pairing. -/
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
  refine Fintype.linearIndependent_iff.mpr fun v hv ↦ ?_
  set A := (Int.castRingHom R).mapMatrix rl.matrix with A_def
  replace hv : v ᵥ* A = 0 := by
    ext j
    have : rl.pairing (∑ i, v i • rl.sRoot i) (rl.sCoroot j) = 0 := by simp [hv]
    simpa [Matrix.vecMul, dotProduct, rl.pairingMatrix, A_def] using this
  have hdet : A.det ≠ 0 := by
    rw [← (Int.castRingHom R).map_det rl.matrix]
    simpa using rl.isCartan.det_ne_zero
  simp [Matrix.eq_zero_of_vecMul_eq_zero hdet hv]

lemma lin_ind_sCoroot [CharZero R] [IsDomain R] : LinearIndependent R rl.sCoroot :=
  rl.flip.lin_ind_sRoot

lemma injective_sRoot [CharZero R] [IsDomain R] : Injective rl.sRoot :=
  rl.lin_ind_sRoot.injective

lemma injective_sCoroot [CharZero R] [IsDomain R] : Injective rl.sCoroot :=
  rl.lin_ind_sCoroot.injective

@[simp] lemma pairing_sRoot_sCoroot_self (i : n) :
    rl.pairing (rl.sRoot i) (rl.sCoroot i) = 2 := by
  simp [rl.pairingMatrix, rl.isCartan.diag]

lemma exist_int_eq_pairing_of_mem_span_int {x : M} (hx : x ∈ span ℤ (range rl.sRoot))
    {y : N} (hy : y ∈ span ℤ (range rl.sCoroot)) :
    ∃ z : ℤ, rl.pairing x y = z := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem u v hu hv => obtain ⟨i, rfl⟩ := hu; obtain ⟨j, rfl⟩ := hv; simp [rl.pairingMatrix]
  | zero_left u hu => exact ⟨0, by simp⟩
  | zero_right u hu => exact ⟨0, by simp⟩
  | add_left u₁ u₂ v _ _ _ h₁ h₂ =>
    obtain ⟨z, hz⟩ := h₁
    obtain ⟨w, hw⟩ := h₂
    exact ⟨z + w, by simp [hz, hw]⟩
  | add_right u v₁ v₂ _ _ _ h₁ h₂ =>
    obtain ⟨z, hz⟩ := h₁
    obtain ⟨w, hw⟩ := h₂
    exact ⟨z + w, by simp [hz, hw]⟩
  | smul_left z u v _ _ h =>
    obtain ⟨w, hw⟩ := h
    exact ⟨z * w, by simp [hw]⟩
  | smul_right z u v _ _ h =>
    obtain ⟨w, hw⟩ := h
    exact ⟨z * w, by simp [hw]⟩

/-- The reflection associated to a simple root. -/
def reflection (i : n) : M ≃ₗ[R] M :=
  Module.reflection (x := rl.sRoot i) (f := rl.pairing.flip (rl.sCoroot i)) <| by simp

/-- The reflection associated to a simple coroot. -/
def coreflection (i : n) : N ≃ₗ[R] N :=
  rl.flip.reflection i

lemma reflection_apply (i : n) (x : M) :
    rl.reflection i x = x - rl.pairing x (rl.sCoroot i) • rl.sRoot i := by
  simp [reflection, Module.reflection_apply]

lemma coreflection_apply (i : n) (y : N) :
    rl.coreflection i y = y - rl.pairing (rl.sRoot i) y • rl.sCoroot i :=
  rl.flip.reflection_apply i y

@[simp]
lemma reflection_same (i : n) (x : M) :
    rl.reflection i (rl.reflection i x) = x :=
  Module.involutive_reflection (by simp) x

@[simp]
lemma coreflection_same (i : n) (y : N) :
    rl.coreflection i (rl.coreflection i y) = y :=
  rl.flip.reflection_same i y

@[simp] lemma flip_pairing : rl.flip.pairing = rl.pairing.flip := by rfl

@[simp] lemma flip_sRoot : rl.flip.sRoot = rl.sCoroot := by rfl

@[simp] lemma flip_sCoroot : rl.flip.sCoroot = rl.sRoot := by rfl

@[simp] lemma flip_reflection (i : n) : rl.flip.reflection i = rl.coreflection i := by rfl

@[simp] lemma flip_coreflection (i : n) : rl.flip.coreflection i = rl.reflection i := by rfl

lemma eq_zero_iff_forall_pairing_sRoot_eq_zero [CharZero R] [IsDomain R]
    {y : N} (hy : y ∈ span R (range rl.sCoroot)) :
    y = 0 ↔ ∀ i, rl.pairing (rl.sRoot i) y = 0 := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  suffices c = 0 by simp [this]
  set A := (Int.castRingHom R).mapMatrix rl.matrix with A_def
  have hdet : A.det ≠ 0 := by
    rw [← (Int.castRingHom R).map_det rl.matrix]
    simpa using rl.isCartan.det_ne_zero
  refine eq_zero_of_mulVec_eq_zero hdet (funext fun i ↦ ?_)
  simpa [A_def, Matrix.mulVec, dotProduct, rl.pairingMatrix, mul_comm] using h i

lemma eq_zero_iff_forall_pairing_sCoroot_eq_zero [CharZero R] [IsDomain R]
    {x : M} (hx : x ∈ span R (range rl.sRoot)) :
    x = 0 ↔ ∀ i, rl.pairing x (rl.sCoroot i) = 0 :=
  rl.flip.eq_zero_iff_forall_pairing_sRoot_eq_zero hx

lemma pairing_reflection_left (i : n) (x : M) (y : N) :
    rl.pairing (rl.reflection i x) y = rl.pairing x (rl.coreflection i y) := by
  simp only [reflection_apply, coreflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, mul_comm]

lemma pairing_reflection_coreflection (i : n) (x : M) (y : N) :
    rl.pairing (rl.reflection i x) (rl.coreflection i y) = rl.pairing x y := by
  rw [rl.pairing_reflection_left, coreflection_same]

/-- The Weyl group of a realisation. -/
def weylGroup :
    Subgroup ((M ≃ₗ[R] M) × (N ≃ₗ[R] N)) :=
  .closure (range fun i ↦ (rl.reflection i, rl.coreflection i))

lemma mem_weyl (i : n) :
    (rl.reflection i, rl.coreflection i) ∈ rl.weylGroup :=
  Subgroup.subset_closure <| mem_range_self i

lemma flip_weyl :
    rl.flip.weylGroup = rl.weylGroup.map (MulEquiv.prodComm.toMonoidHom) := by
  simp [weylGroup, MonoidHom.map_closure, ← image_univ, ← image_comp]

@[simp] lemma mem_flip_weyl {w : (N ≃ₗ[R] N) × (M ≃ₗ[R] M)} :
    w ∈ rl.flip.weylGroup ↔ (w.2, w.1) ∈ rl.weylGroup := by
  obtain ⟨a, b⟩ := w
  simp [flip_weyl]

lemma map_fst_weyl :
    rl.weylGroup.map (MonoidHom.fst _ _) = .closure (range rl.reflection) := by
  simp [weylGroup, MonoidHom.map_closure, ← image_univ, ← image_comp]

lemma map_snd_weyl :
    rl.weylGroup.map (MonoidHom.snd _ _) = .closure (range rl.coreflection) := by
  simp [weylGroup, MonoidHom.map_closure, ← image_univ, ← image_comp]

@[simp] lemma reflection_inv (i : n) : (rl.reflection i)⁻¹ = rl.reflection i := by rfl

@[simp] lemma coreflection_inv (i : n) : (rl.coreflection i)⁻¹ = rl.coreflection i := by rfl

@[elab_as_elim]
lemma weylGroup.induction {pred : (g : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)) → g ∈ rl.weylGroup → Prop}
    (mem : ∀ i, pred (rl.reflection i, rl.coreflection i) (rl.mem_weyl i))
    (one : pred 1 (one_mem _))
    (mul : ∀ x y hx hy, pred x hx → pred y hy → pred (x * y) (mul_mem hx hy))
    {w} (hw : w ∈ rl.weylGroup) :
    pred w hw := by
  set S := (range fun i ↦ (rl.reflection i, rl.coreflection i)) with S_def
  have : rl.weylGroup.toSubmonoid = .closure S := by
    suffices S = S⁻¹ by rw [weylGroup, Subgroup.closure_toSubmonoid, ← this, union_self]
    ext; simp [S_def, ← inv_eq_iff_eq_inv]
  let pred' : (g : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)) →
      g ∈ Submonoid.closure S → Prop :=
    fun g hg ↦ pred g <| by change g ∈ rl.weylGroup.toSubmonoid; rwa [this]
  replace hw' : w ∈ Submonoid.closure S := by rwa [← this]
  suffices pred' w hw' from this
  clear hw
  induction hw' using Submonoid.closure_induction with
  | mem u hu => obtain ⟨i, rfl⟩ := hu; exact mem i
  | one => exact one
  | mul u v hu hv hu' hv' => rw [← this] at hu hv; exact mul u v hu hv hu' hv'

lemma pairing_apply_apply_of_mem_weyl {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)}
    (hw : w ∈ rl.weylGroup) (x : M) (y : N) :
    rl.pairing (w.1 x) (w.2 y) = rl.pairing x y := by
  induction hw using weylGroup.induction generalizing x y with
  | mem i => exact rl.pairing_reflection_coreflection i x y
  | one => simp
  | mul u v _ _ hu hv => simp [hu, hv]

lemma mapsTo_span_int_range_sRoot {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw : w ∈ rl.weylGroup) :
    MapsTo w.1 (span ℤ (range rl.sRoot)) (span ℤ (range rl.sRoot)) := by
  induction hw using weylGroup.induction with
  | mem i =>
    intro x hx
    obtain ⟨z, hz⟩ : ∃ z : ℤ, rl.pairing x (rl.sCoroot i) = z :=
      rl.exist_int_eq_pairing_of_mem_span_int hx <| subset_span <| mem_range_self i
    simp only [reflection_apply, hz, Int.cast_smul_eq_zsmul, SetLike.mem_coe]
    exact sub_mem hx <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self i
  | one => intro x hx; simpa using hx
  | mul u v _ _ hu hv => exact fun x hx ↦ hu (hv hx)

instance : SMul rl.weylGroup (M × N) where smul w p := (w.1.1 p.1, w.1.2 p.2)

lemma weylGroup_smul_def (w : rl.weylGroup) (p : M × N) : w • p = (w.1.1 p.1, w.1.2 p.2) := rfl

instance : DistribMulAction rl.weylGroup (M × N) where
  mul_smul := by simp [weylGroup_smul_def]
  one_smul := by simp [weylGroup_smul_def]
  smul_zero := by simp [weylGroup_smul_def]
  smul_add := by simp [weylGroup_smul_def]

/-- Taking the Weyl-group orbits of all `(simple root, simple coroot)` pairs, yields a natural
indexing set for the roots and coroots for the root pairing corresponding to a realisation. -/
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
  ext
  constructor
  · rintro ⟨w, hw, i, rfl⟩
    exact ⟨_, rl.mk_mem_idx (rl.mem_flip_weyl.mp hw) i, rfl⟩
  · rintro ⟨-, ⟨w, hw, i, rfl⟩, rfl⟩
    exact ⟨(w.2, w.1), rl.mem_flip_weyl.mpr hw, i, rfl⟩

lemma pairing_fst_snd {p : M × N} (hp : p ∈ rl.idx) :
    rl.pairing p.1 p.2 = 2 := by
  obtain ⟨w, hw, i, rfl⟩ := hp
  simpa using rl.pairing_apply_apply_of_mem_weyl hw (rl.sRoot i) (rl.sCoroot i)

lemma fst_mem_span {p : M × N} (hp : p ∈ rl.idx) :
    p.1 ∈ span R (range rl.sRoot) := by
  obtain ⟨w, hw, i, rfl⟩ := hp
  exact Submodule.span_subset_span ℤ R _ <|
    rl.mapsTo_span_int_range_sRoot hw <| subset_span <| mem_range_self i

lemma snd_mem_span {p : M × N} (hp : p ∈ rl.idx) :
    p.2 ∈ span R (range rl.sCoroot) := by
  replace hp : p.swap ∈ rl.flip.idx := by simpa
  simpa using rl.flip.fst_mem_span hp

lemma idx_subset_span_int_sprod_span_int :
    rl.idx ⊆ (span ℤ <| range rl.sRoot) ×ˢ (span ℤ <| range rl.sCoroot) := by
  rintro p ⟨w, hw, i, rfl⟩
  refine ⟨rl.mapsTo_span_int_range_sRoot hw <| subset_span <| mem_range_self i, ?_⟩
  exact rl.flip.mapsTo_span_int_range_sRoot (w := (w.2, w.1)) (rl.mem_flip_weyl.mpr hw) <|
    subset_span <| mem_range_self i

variable [CharZero R] [IsDomain R]

-- TODO Sort out this lemma (and much of the below)
lemma exists_coords {d : n → ℤ} (hd : (diagonal d * rl.matrix).IsSymm)
    {p : M × N} (hp : p ∈ rl.idx) :
    ∃ (i : n) (b : n → ℤ),
      b ⬝ᵥ (diagonal d * rl.matrix) *ᵥ b = 2 * d i ∧
      p.2 = ∑ j, b j • rl.sCoroot j ∧
      d i • p.1 = ∑ j, (b j * d j) • rl.sRoot j := by
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, (d i : R) * rl.pairing p.1 (rl.sCoroot j) =
      (d j : R) * rl.pairing (rl.sRoot j) p.2 := by
    obtain ⟨w, hw, i, rfl⟩ := hp
    have hd' (i j : n) : (d i : R) * (rl.matrix i j : R) = (d j : R) * (rl.matrix j i : R) := by
      have : d i * rl.matrix i j = d j * rl.matrix j i := by simpa using hd.apply j i
      exact_mod_cast congrArg (Int.cast (R := R)) this
    suffices ∀ {v : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)}, v ∈ rl.weylGroup → ∀ q : M × N,
        (∀ j, (d i : R) * rl.pairing q.1 (rl.sCoroot j) =
          (d j : R) * rl.pairing (rl.sRoot j) q.2) →
        ∀ j, (d i : R) * rl.pairing (v.1 q.1) (rl.sCoroot j) =
          (d j : R) * rl.pairing (rl.sRoot j) (v.2 q.2) by
      exact ⟨i, this hw (rl.sRoot i, rl.sCoroot i) fun j ↦ by
        simpa [rl.pairingMatrix] using hd' i j⟩
    intro v hv
    induction hv using weylGroup.induction with
    | mem k =>
      intro q hq j
      simp only [reflection_apply, coreflection_apply, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, rl.pairingMatrix]
      linear_combination hq j - (rl.matrix k j : R) * hq k + rl.pairing (rl.sRoot k) q.2 * hd' j k
    | one => exact fun q hq ↦ hq
    | mul u v _ _ hu hv => exact fun q hq ↦ hu (v.1 q.1, v.2 q.2) (hv q hq)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (rl.idx_subset_span_int_sprod_span_int hp).2
  have h2 : p.2 = ∑ j, b j • rl.sCoroot j := hb.symm
  have hbd : (fun j ↦ b j * d j) = b ᵥ* diagonal d := funext fun j ↦ (vecMul_diagonal b d j).symm
  have hvecMul (c : n → ℤ) (k : n) :
      rl.pairing (∑ j, c j • rl.sRoot j) (rl.sCoroot k) = (((c ᵥ* rl.matrix) k : ℤ) : R) := by
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, rl.pairingMatrix,
      zsmul_eq_mul, Matrix.vecMul, dotProduct]
    push_cast
    rfl
  have hmulVec (k : n) : rl.pairing (rl.sRoot k) p.2 = (((rl.matrix *ᵥ b) k : ℤ) : R) := by
    rw [h2]
    simp only [map_sum, map_zsmul, rl.pairingMatrix, zsmul_eq_mul, Matrix.mulVec, dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have h1 : d i • p.1 = ∑ j, (b j * d j) • rl.sRoot j := by
    have hmem : d i • p.1 - ∑ j, (b j * d j) • rl.sRoot j ∈ span R (range rl.sRoot) := by
      simp only [← Int.cast_smul_eq_zsmul R]
      exact sub_mem (Submodule.smul_mem _ _ (rl.fst_mem_span hp))
        (Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (subset_span (mem_range_self j)))
    rw [← sub_eq_zero, rl.eq_zero_iff_forall_pairing_sCoroot_eq_zero (by simpa using hmem)]
    intro k
    simp only [map_sub, LinearMap.sub_apply, sub_eq_zero]
    rw [hvecMul, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, hi k, hmulVec]
    have : d k * (rl.matrix *ᵥ b) k = ((fun j ↦ b j * d j) ᵥ* rl.matrix) k := by
      rw [hbd, vecMul_vecMul, ← mulVec_transpose, hd.eq, ← mulVec_mulVec, mulVec_diagonal]
    exact_mod_cast congrArg (Int.cast (R := R)) this
  refine ⟨i, b, ?_, h2, h1⟩
  have hdiag : b ⬝ᵥ (diagonal d * rl.matrix) *ᵥ b = (fun j ↦ b j * d j) ⬝ᵥ rl.matrix *ᵥ b := by
    rw [hbd, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have hdot (c : n → ℤ) :
      rl.pairing (∑ j, c j • rl.sRoot j) p.2 = ((c ⬝ᵥ rl.matrix *ᵥ b : ℤ) : R) := by
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, hmulVec,
      zsmul_eq_mul, dotProduct]
    push_cast
    rfl
  have hnorm : ((b ⬝ᵥ (diagonal d * rl.matrix) *ᵥ b : ℤ) : R) = ((2 * d i : ℤ) : R) := by
    rw [hdiag, ← hdot, ← h1, map_zsmul, LinearMap.smul_apply, rl.pairing_fst_snd hp, zsmul_eq_mul]
    push_cast
    ring
  exact_mod_cast hnorm

instance : Finite rl.idx := by
  obtain ⟨d, hd_pos, hG⟩ := rl.isCartan.exists_posDef
  set G : Matrix n n ℤ := Matrix.diagonal d * rl.matrix with hGdef
  have hd : (Matrix.diagonal d * rl.matrix).IsSymm := by have := hG.isHermitian; aesop
  choose i b hnorm h2 h1 using fun p : rl.idx ↦ rl.exists_coords hd p.2
  set K : ℤ := 2 * ∑ j, d j with hK
  have hbK : ∀ p : rl.idx, b p ⬝ᵥ G *ᵥ b p ≤ K := fun p ↦ by
    rw [hnorm p, hK]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ ↦ (hd_pos j).le) (Finset.mem_univ _)) (by norm_num)
  have _i : Finite ↥{c : n → ℤ | c ⬝ᵥ G *ᵥ c ≤ K} :=
    (hG.finite_setOf_dotProduct_mulVec_le K).to_subtype
  have : IsReflexive R M := .of_isPerfPair rl.pairing
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

-- TODO drop (or _maybe_ restate) but wait till we see how used below
omit [CharZero R] [IsDomain R] in
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
    simp [reflection_apply, h]
  · have h : rl.pairing (v.1 (rl.sRoot i)) y = rl.pairing (rl.sRoot i) (v.2.symm y) := by
      rw [← rl.pairing_apply_apply_of_mem_weyl hv (rl.sRoot i) (v.2.symm y)]
      simp
    change v.2 (rl.coreflection i (v.2.symm y)) = _
    simp [coreflection_apply, h]

omit [CharZero R] [IsDomain R] in
lemma mapsTo_preReflection_fst {p : M × N} (hp : p ∈ rl.idx) :
    MapsTo (preReflection p.1 (rl.pairing.flip p.2)) (Prod.fst '' rl.idx) (Prod.fst '' rl.idx) := by
  obtain ⟨w, hw, h₁, -⟩ := rl.exists_mem_weyl_of_mem_idx hp
  rintro - ⟨q, hq, rfl⟩
  exact ⟨_, rl.apply_mem_idx hw hq, by simp [preReflection_apply, h₁]⟩

omit [CharZero R] [IsDomain R] in
lemma mapsTo_preReflection_snd {p : M × N} (hp : p ∈ rl.idx) :
    MapsTo (preReflection p.2 (rl.pairing p.1)) (Prod.snd '' rl.idx) (Prod.snd '' rl.idx) := by
  obtain ⟨w, hw, -, h₂⟩ := rl.exists_mem_weyl_of_mem_idx hp
  rintro - ⟨q, hq, rfl⟩
  exact ⟨_, rl.apply_mem_idx hw hq, by simp [preReflection_apply, h₂]⟩

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
  have : IsReflexive R M := .of_isPerfPair rl.pairing
  have key := Dual.eq_of_preReflection_mapsTo' hfin hx hf₁ (rl.mapsTo_preReflection_fst hp) hg₁ hg₂
  refine Prod.ext h (sub_eq_zero.mp <| (rl.eq_zero_iff_forall_pairing_sRoot_eq_zero
    (sub_mem (rl.snd_mem_span hp) (rl.snd_mem_span hq))).mpr fun i ↦ ?_)
  have hi : rl.sRoot i ∈ span R (Prod.fst '' rl.idx) :=
    subset_span ⟨(rl.sRoot i, rl.sCoroot i), rl.sPair_mem_idx i, rfl⟩
  have := LinearMap.congr_fun key ⟨rl.sRoot i, hi⟩
  simp only [LinearMap.dualMap_apply, Submodule.subtype_apply, LinearMap.flip_apply] at this
  simp [this]

lemma injOn_snd : InjOn Prod.snd rl.idx := by
  intro p hp q hq h
  replace hp : p.swap ∈ rl.flip.idx := by simpa [flip_idx]
  replace hq : q.swap ∈ rl.flip.idx := by simpa [flip_idx]
  simpa using rl.flip.injOn_fst hp hq h

/-- The roots of a realisation of a Cartan matrix. -/
abbrev root : rl.idx ↪ M :=
  ⟨fun p ↦ (p : M × N).1, fun p q hpq ↦ Subtype.ext <| rl.injOn_fst p.2 q.2 hpq⟩

/-- The coroots of a realisation of a Cartan matrix. -/
abbrev coroot : rl.idx ↪ N :=
  ⟨fun p ↦ (p : M × N).2, fun p q hpq ↦ Subtype.ext <| rl.injOn_snd p.2 q.2 hpq⟩

@[simp] lemma root_apply (p : rl.idx) : rl.root p = (p : M × N).1 := rfl

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

-- TODO Consider dropping `ι`, `e` and introducing `RootPairing.reindex` for the application
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
    (rl.toRootPairing e).root i = ((e i : M × N)).1 := by rfl

@[simp] lemma toRootPairing_coroot (i : ι) :
    (rl.toRootPairing e).coroot i = ((e i : M × N)).2 := by rfl

@[simp] lemma toRootPairing_toLinearMap :
    (rl.toRootPairing e).toLinearMap = rl.pairing := by rfl

lemma toRootPairing_pairing (i j : ι) :
    (rl.toRootPairing e).pairing i j = rl.pairing ((e i : M × N)).1 ((e j : M × N)).2 := by rfl

lemma isCrystallographic_toRootPairing :
    (rl.toRootPairing e).IsCrystallographic where
  exists_value i j := by
    obtain ⟨hp, -⟩ := rl.idx_subset_span_int_sprod_span_int (e i).2
    obtain ⟨-, hq⟩ := rl.idx_subset_span_int_sprod_span_int (e j).2
    obtain ⟨z, hz⟩ := rl.exist_int_eq_pairing_of_mem_span_int hp hq
    exact ⟨z, by simp [toRootPairing_pairing, hz]⟩

lemma eq_one_or_neg_one_of_eq_zsmul_sRoot {p : M × N} (hp : p ∈ rl.idx) {z : ℤ} {m : n}
    (h : p.1 = (z : R) • rl.sRoot m) :
    z = 1 ∨ z = -1 := by
  obtain ⟨w, hw, l, hwl⟩ := hp
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (rl.idx_subset_span_int_sprod_span_int (rl.mk_mem_idx (inv_mem hw) m)).1
  have h1 : rl.sRoot l = ∑ k, ((z * c k : ℤ) : R) • rl.sRoot k := by
    have h2 : w.1 (rl.sRoot l) = (z : R) • rl.sRoot m := by rw [← h, ← hwl]
    have h3 : rl.sRoot l = (z : R) • w.1.symm (rl.sRoot m) := by
      rw [← map_smul, ← h2, LinearEquiv.symm_apply_apply]
    rw [h3, show w.1.symm (rl.sRoot m) = ∑ k, c k • rl.sRoot k from hc.symm, Finset.smul_sum]
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
    have : IsReflexive R M := .of_isPerfPair rl.pairing
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
    obtain ⟨c, hγ₀⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (rl.idx_subset_span_int_sprod_span_int (rl.apply_mem_idx (inv_mem hw) hp)).1
    have hγ : w.1.symm p.1 = ∑ k, c k • rl.sRoot k := hγ₀.symm
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
