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
   root pairing (i.e., a reduced root datum except we do not require `R = ℤ`).
2. The matrix `Aᵢⱼ = ⟨cⱼ, rᵢ⟩` is a finite-type Cartan matrix.

The definition `RootPairing` formalises item 1 above. Here we introduce `CartanMatrix.Realisation`
to formalise item 2.

## Main definitions / results:
 * `CartanMatrix.Realisation`: the definition of a realisation of a Cartan matrix.
 * `CartanMatrix.Realisation.toRootPairing`: the root pairing defined by a realisation of a Cartan
   matrix.
 * `Matrix.IsFiniteCartan.toRealisation`: a realisation associated to an invertible Cartan matrix.
 * `Matrix.IsFiniteCartan.toRootPairing`: a reduced, irreducible, crystallographic root system
   assocated to a Cartan matrix, with coefficients in any field of characteristic zero.

-/

public noncomputable section

open Function Matrix Module Prod Set
open Submodule (span subset_span)

variable (n R M N : Type*) [Fintype n] [DecidableEq n] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace CartanMatrix

/-- A realisation of a Cartan matrix indexed by `n` is a family of vectors `v` and covectors `f`,
both indexed by `n`, such that `⟨fⱼ, vᵢ⟩ = Aᵢⱼ` for all `i j`. -/
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

attribute [simp] Realisation.pairingMatrix

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
  pairingMatrix := by simp

lemma lin_ind_sRoot [CharZero R] [IsDomain R] : LinearIndependent R rl.sRoot := by
  refine Fintype.linearIndependent_iff.mpr fun v hv ↦ ?_
  set A := (Int.castRingHom R).mapMatrix rl.matrix with A_def
  replace hv : v ᵥ* A = 0 := by
    ext j
    have : rl.pairing (∑ i, v i • rl.sRoot i) (rl.sCoroot j) = 0 := by simp [hv]
    simpa [Matrix.vecMul, dotProduct, A_def] using this
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

lemma pairing_sRoot_sCoroot_self (i : n) :
    rl.pairing (rl.sRoot i) (rl.sCoroot i) = 2 := by
  simp [rl.isCartan.diag]

lemma exist_int_eq_pairing_of_mem_span_int {x : M} (hx : x ∈ span ℤ (range rl.sRoot))
    {y : N} (hy : y ∈ span ℤ (range rl.sCoroot)) :
    ∃ z : ℤ, rl.pairing x y = z := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem u v hu hv => obtain ⟨i, rfl⟩ := hu; obtain ⟨j, rfl⟩ := hv; simp
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
  Module.reflection (x := rl.sRoot i) (f := rl.pairing.flip (rl.sCoroot i)) <| by
    simp [rl.isCartan.diag]

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
  Module.involutive_reflection (by simp [rl.isCartan.diag]) x

@[simp]
lemma coreflection_same (i : n) (y : N) :
    rl.coreflection i (rl.coreflection i y) = y :=
  rl.flip.reflection_same i y

@[simp] lemma flip_pairing : rl.flip.pairing = rl.pairing.flip := by rfl

@[simp] lemma flip_sRoot : rl.flip.sRoot = rl.sCoroot := by rfl

@[simp] lemma flip_sCoroot : rl.flip.sCoroot = rl.sRoot := by rfl

@[simp] lemma flip_reflection (i : n) : rl.flip.reflection i = rl.coreflection i := by rfl

@[simp] lemma flip_coreflection (i : n) : rl.flip.coreflection i = rl.reflection i := by rfl

lemma eq_iff_forall_pairing_sRoot_eq [CharZero R] [IsDomain R]
    {y₁ y₂ : N} (hy : y₁ - y₂ ∈ span R (range rl.sCoroot)) :
    y₁ = y₂ ↔ ∀ i, rl.pairing (rl.sRoot i) y₁ = rl.pairing (rl.sRoot i) y₂ := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  suffices ∀ y ∈ span R (range rl.sCoroot), (∀ i, (rl.pairing (rl.sRoot i)) y = 0) → y = 0 by
    rw [← sub_eq_zero]; aesop
  intro y hy h
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  suffices c = 0 by simp [this]
  set A := (Int.castRingHom R).mapMatrix rl.matrix with A_def
  have hdet : A.det ≠ 0 := by
    rw [← (Int.castRingHom R).map_det rl.matrix]
    simpa using rl.isCartan.det_ne_zero
  refine eq_zero_of_mulVec_eq_zero hdet (funext fun i ↦ ?_)
  simpa [A_def, Matrix.mulVec, dotProduct, mul_comm] using h i

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
  .closure (range <| Function.prod rl.reflection rl.coreflection)

lemma mem_weyl (i : n) :
    (rl.reflection i, rl.coreflection i) ∈ rl.weylGroup :=
  Subgroup.subset_closure <| mem_range_self i

instance : SMul rl.weylGroup (M × N) where smul w p := (w.1.1 p.1, w.1.2 p.2)

lemma weylGroup_smul_def (w : rl.weylGroup) (p : M × N) : w • p = (w.1.1 p.1, w.1.2 p.2) := rfl

instance : DistribMulAction rl.weylGroup (M × N) where
  mul_smul := by simp [weylGroup_smul_def]
  one_smul := by simp [weylGroup_smul_def]
  smul_zero := by simp [weylGroup_smul_def]
  smul_add := by simp [weylGroup_smul_def]

lemma flip_weyl :
    rl.flip.weylGroup = rl.weylGroup.map (MulEquiv.prodComm.toMonoidHom) := by
  simp [weylGroup, MonoidHom.map_closure, ← image_univ, ← image_comp, prod_def]

@[simp] lemma mem_flip_weyl {w : (N ≃ₗ[R] N) × (M ≃ₗ[R] M)} :
    w ∈ rl.flip.weylGroup ↔ (w.2, w.1) ∈ rl.weylGroup := by
  obtain ⟨a, b⟩ := w
  simp [flip_weyl]

@[simp] lemma reflection_inv (i : n) : (rl.reflection i)⁻¹ = rl.reflection i := by rfl

@[simp] lemma coreflection_inv (i : n) : (rl.coreflection i)⁻¹ = rl.coreflection i := by rfl

@[elab_as_elim]
lemma weylGroup.induction {pred : (g : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)) → g ∈ rl.weylGroup → Prop}
    (mem : ∀ i, pred (rl.reflection i, rl.coreflection i) (rl.mem_weyl i))
    (one : pred 1 (one_mem _))
    (mul : ∀ x y hx hy, pred x hx → pred y hy → pred (x * y) (mul_mem hx hy))
    {w} (hw : w ∈ rl.weylGroup) :
    pred w hw := by
  set S := (range <| Function.prod rl.reflection rl.coreflection) with S_def
  have : rl.weylGroup.toSubmonoid = .closure S := by
    suffices S = S⁻¹ by rw [weylGroup, Subgroup.closure_toSubmonoid, ← this, union_self]
    ext; simp [S_def, ← inv_eq_iff_eq_inv]
  let pred' : (g : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)) → g ∈ Submonoid.closure S → Prop :=
    fun g hg ↦ pred g <| by rwa [← Subgroup.mem_toSubmonoid, this]
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

lemma exists_zsum_eq_of_mem_weylGroup {d : n → ℤ} (hd : (rl.matrix * diagonal d).IsSymm)
    {w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw : w ∈ rl.weylGroup) (c : n → ℤ) :
    letI S := rl.matrix * diagonal d
    ∃ c' : n → ℤ, w.1 (∑ j, c j • rl.sRoot j) = ∑ j, c' j • rl.sRoot j ∧
      c' ⬝ᵥ S *ᵥ c' = c ⬝ᵥ S *ᵥ c := by
  set A := rl.matrix with A_def
  set S := A * diagonal d with S_def
  induction hw using weylGroup.induction generalizing c with
  | mem i =>
    set t : ℤ := ∑ j, c j * A j i with t_def
    have ht : rl.pairing (∑ j, c j • rl.sRoot j) (rl.sCoroot i) = t := by simp [A_def, t_def]
    have hSt : (S *ᵥ c) i = t * d i := by
      replace hd (j : n) : A i j * d j = A j i * d i := by simpa [S_def] using hd.apply j i
      simp_rw [mulVec_apply_eq_sum, t_def, S_def, mul_diagonal, hd, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    refine ⟨c - Pi.single i t, ?_, ?_⟩
    · rw [reflection_apply, ht]
      simp [sub_smul, Int.cast_smul_eq_zsmul]
    · have : Pi.single i t ⬝ᵥ S *ᵥ Pi.single i t = t * (t * (2 * d i)) := by
        simp [S_def, A_def, rl.isCartan.diag]
      rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        hd.dotProduct_mulVec_comm (y := Pi.single i t), single_dotProduct, hSt, this]
      ring
  | one => exact ⟨c, by simp, rfl⟩
  | mul u v _ _ hu hv =>
    obtain ⟨c₁, hc₁, hcc₁⟩ := hv c
    obtain ⟨c₂, hc₂, hcc₂⟩ := hu c₁
    exact ⟨c₂, by simp [← hc₁, ← hc₂], by rw [hcc₂, hcc₁]⟩

lemma finite_setOf_mem_weylGroup_apply_sRoot :
    {w.1 (rl.sRoot i) | (w ∈ rl.weylGroup) (i)}.Finite := by
  obtain ⟨d, hd, hS⟩ := rl.isCartan.transpose.exists_posDef
  set S := rl.matrix * diagonal d with S_def
  replace hS : S.PosDef := by rw [S_def, ← PosDef.transpose_iff]; simpa using hS
  refine ((hS.finite_setOf_dotProduct_mulVec_le S.trace).image
    fun c ↦ ∑ j, c j • rl.sRoot j).subset ?_
  rintro - ⟨w, hw, i, rfl⟩
  obtain ⟨c, hc, hQ⟩ := rl.exists_zsum_eq_of_mem_weylGroup hS.isHermitian.isSymm hw (Pi.single i 1)
  refine ⟨c, ?_, ?_⟩
  · rw [mem_ofPred_eq, hQ, single_dotProduct, one_mul, Matrix.mulVec_single_one, Matrix.col_apply]
    exact Finset.single_le_sum (fun _ _ ↦ hS.diag_pos.le) (Finset.mem_univ i)
  · simp [← hc]

lemma eq_of_mem_weylGroup_of_forall_apply_sRoot_eq [CharZero R] [IsDomain R]
    {w₁ w₂ : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)} (hw₁ : w₁ ∈ rl.weylGroup) (hw₂ : w₂ ∈ rl.weylGroup)
    (h : ∀ i, w₁.1 (rl.sRoot i) = w₂.1 (rl.sRoot i)) :
    w₁ = w₂ := by
  suffices ∀ w ∈ rl.weylGroup, (∀ i, w.1 (rl.sRoot i) = rl.sRoot i) → w = 1 from
    (inv_mul_eq_one.mp <| this (w₂⁻¹ * w₁) (mul_mem (inv_mem hw₂) hw₁) <| by simp [h]).symm
  clear! w₁ w₂
  intro w hw
  have key (y : N) : w.2 y - y ∈ span R (range rl.sCoroot) := by
    induction hw using weylGroup.induction generalizing y with
    | mem i =>
      rw [rl.coreflection_apply, sub_sub_cancel_left, neg_mem_iff]
      exact Submodule.smul_mem _ _ <| subset_span <| mem_range_self i
    | one => simp
    | mul a b _ _ ha hb => simpa using add_mem (ha <| b.2 y) (hb y)
  intro hw'
  replace hw' (y : N) : w.2 y = y := by
    simp_rw [rl.eq_iff_forall_pairing_sRoot_eq (key y),
      ← rl.pairing_apply_apply_of_mem_weyl hw (rl.sRoot _) y]
    aesop
  have hw'' (x : M) : w.1 x = x := by
    refine (LinearMap.IsPerfPair.bijective_left rl.pairing).injective <| LinearMap.ext fun y ↦ ?_
    simpa [hw' y] using rl.pairing_apply_apply_of_mem_weyl hw x y
  exact Prod.ext (LinearEquiv.ext hw'') (LinearEquiv.ext hw')

instance [CharZero R] [IsDomain R] : Finite rl.weylGroup := by
  set f : rl.weylGroup → n → M := fun w i ↦ (w : (M ≃ₗ[R] M) × (N ≃ₗ[R] N)).1 (rl.sRoot i)
  have hinj : Injective f := fun w w' hww' ↦
    Subtype.ext <| rl.eq_of_mem_weylGroup_of_forall_apply_sRoot_eq w.2 w'.2 fun i ↦ congr_fun hww' i
  rw [← finite_univ_iff]
  refine .of_finite_image ?_ hinj.injOn
  exact (Finite.pi fun _ ↦ rl.finite_setOf_mem_weylGroup_apply_sRoot).subset <| by grind

/-- Taking the Weyl-group orbits of all `(simple root, simple coroot)` pairs, yields a natural
indexing set for the roots and coroots for the root pairing corresponding to a realisation. -/
def idx : Set (M × N) := {(w.1 (rl.sRoot i), w.2 (rl.sCoroot i)) | (w ∈ rl.weylGroup) (i)}

open scoped Pointwise in
lemma idx_eq_smul :
    rl.idx = (univ : Set rl.weylGroup) • (range <| Function.prod rl.sRoot rl.sCoroot) := by
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

@[simp] lemma flip_idx : rl.flip.idx = swap '' rl.idx := by
  ext
  constructor
  · rintro ⟨w, hw, i, rfl⟩
    exact ⟨_, rl.mk_mem_idx (rl.mem_flip_weyl.mp hw) i, rfl⟩
  · rintro ⟨-, ⟨w, hw, i, rfl⟩, rfl⟩
    exact ⟨(w.2, w.1), rl.mem_flip_weyl.mpr hw, i, rfl⟩

lemma pairing_fst_snd {p : M × N} (hp : p ∈ rl.idx) :
    rl.pairing p.1 p.2 = 2 := by
  obtain ⟨w, hw, i, rfl⟩ := hp
  simpa [rl.isCartan.diag] using rl.pairing_apply_apply_of_mem_weyl hw (rl.sRoot i) (rl.sCoroot i)

lemma idx_subset_span_int_sprod_span_int :
    rl.idx ⊆ (span ℤ <| range rl.sRoot) ×ˢ (span ℤ <| range rl.sCoroot) := by
  rintro p ⟨w, hw, i, rfl⟩
  refine ⟨rl.mapsTo_span_int_range_sRoot hw <| subset_span <| mem_range_self i, ?_⟩
  exact rl.flip.mapsTo_span_int_range_sRoot (w := (w.2, w.1)) (rl.mem_flip_weyl.mpr hw) <|
    subset_span <| mem_range_self i

instance : Finite rl.idx := by
  refine ((rl.finite_setOf_mem_weylGroup_apply_sRoot.prod
    rl.flip.finite_setOf_mem_weylGroup_apply_sRoot).subset ?_).to_subtype
  rintro - ⟨w, hw, i, rfl⟩
  exact ⟨⟨w, hw, i, rfl⟩, ⟨(w.2, w.1), rl.mem_flip_weyl.mpr hw, i, rfl⟩⟩

/-- The (co)reflection determined by a root / coroot pair. -/
def reflectionPair {p : M × N} (hp : p ∈ rl.idx) : (M ≃ₗ[R] M) × (N ≃ₗ[R] N) :=
  ⟨Module.reflection (x := p.1) (f := rl.pairing.flip p.2) (by simpa using rl.pairing_fst_snd hp),
   Module.reflection (rl.pairing_fst_snd hp)⟩

lemma reflectionPair_mem {p : M × N} (hp : p ∈ rl.idx) :
    rl.reflectionPair hp ∈ rl.weylGroup := by
  obtain ⟨w, hw, i, rfl⟩ := id hp
  suffices rl.reflectionPair hp = w * (rl.reflection i, rl.coreflection i) * w⁻¹ by
    rw [this]
    exact mul_mem (mul_mem hw <| rl.mem_weyl i) (inv_mem hw)
  have h₁ (x : M) : rl.pairing (w.1.symm x) (rl.sCoroot i) = rl.pairing x (w.2 (rl.sCoroot i)) := by
    simpa using (rl.pairing_apply_apply_of_mem_weyl hw (w.1.symm x) (rl.sCoroot i)).symm
  have h₂ (y : N) : rl.pairing (rl.sRoot i) (w.2.symm y) = rl.pairing (w.1 (rl.sRoot i)) y := by
    simpa using (rl.pairing_apply_apply_of_mem_weyl hw (rl.sRoot i) (w.2.symm y)).symm
  ext
  · simp [reflectionPair, Module.reflection_apply, rl.reflection_apply, h₁]
  · simp [reflectionPair, Module.reflection_apply, rl.coreflection_apply, h₂]

variable [CharZero R] [IsDomain R]

lemma injOn_fst : InjOn fst rl.idx := by
  rintro ⟨x, y₁⟩ hp ⟨-, y₂⟩ hq rfl
  have : IsReflexive R M := .of_isPerfPair rl.pairing
  have hfin : (fst '' rl.idx).Finite := Set.toFinite _
  have hy₁ : (rl.pairing.flip y₁) x = 2 := by simpa using rl.pairing_fst_snd hp
  have hy₂ : (rl.pairing.flip y₂) x = 2 := by simpa using rl.pairing_fst_snd hq
  have aux {p : M × N} (hp : p ∈ rl.idx) :
      MapsTo (preReflection p.1 (rl.pairing.flip p.2)) (fst '' rl.idx) (fst '' rl.idx) := by
    rintro - ⟨q, hq, rfl⟩
    exact ⟨_, rl.apply_mem_idx (rl.reflectionPair_mem hp) hq, rfl⟩
  have key := Dual.eq_of_preReflection_mapsTo' hfin (subset_span ⟨(x, y₁), by simpa⟩)
    hy₁ (by simpa using aux hp) hy₂ (by simpa using aux hq)
  have hsub : y₁ - y₂ ∈ span R (range rl.sCoroot) :=
    sub_mem (Submodule.span_subset_span ℤ R _ (rl.idx_subset_span_int_sprod_span_int hp).2)
      (Submodule.span_subset_span ℤ R _ (rl.idx_subset_span_int_sprod_span_int hq).2)
  suffices ∀ i, (rl.pairing (rl.sRoot i)) y₁ = (rl.pairing (rl.sRoot i)) y₂ from
    Prod.ext rfl <| (rl.eq_iff_forall_pairing_sRoot_eq hsub).mpr this
  intro i
  simpa using LinearMap.congr_fun key ⟨rl.sRoot i, subset_span ⟨_, rl.sPair_mem_idx i, rfl⟩⟩

lemma injOn_snd : InjOn snd rl.idx := by
  intro p hp q hq h
  replace hp : p.swap ∈ rl.flip.idx := by simpa [flip_idx]
  replace hq : q.swap ∈ rl.flip.idx := by simpa [flip_idx]
  simpa using rl.flip.injOn_fst hp hq h

/-- The root pairing associated to a realisation of a Cartan matrix. -/
def toRootPairing :
    RootPairing rl.idx R M N :=
  .mk' rl.pairing
    ⟨fun p ↦ (p : M × N).1, fun i j h ↦ Subtype.ext <| rl.injOn_fst i.2 j.2 h⟩
    ⟨fun p ↦ (p : M × N).2, fun i j h ↦ Subtype.ext <| rl.injOn_snd i.2 j.2 h⟩
    (fun i ↦ rl.pairing_fst_snd i.property)
    (by
      rintro ⟨p, hp⟩ - ⟨⟨q, hq⟩, rfl⟩
      exact ⟨⟨_, rl.apply_mem_idx (rl.reflectionPair_mem hp) hq⟩, rfl⟩)
    (by
      rintro ⟨p, hp⟩ - ⟨⟨q, hq⟩, rfl⟩
      exact ⟨⟨_, rl.apply_mem_idx (rl.reflectionPair_mem hp) hq⟩, rfl⟩)

@[simp] lemma toRootPairing_root (i : rl.idx) :
    rl.toRootPairing.root i = i.val.fst := by rfl

@[simp] lemma toRootPairing_coroot (i : rl.idx) :
    rl.toRootPairing.coroot i = i.val.snd := by rfl

@[simp] lemma toRootPairing_toLinearMap :
    rl.toRootPairing.toLinearMap = rl.pairing := by rfl

lemma toRootPairing_pairing (i j : rl.idx) :
    rl.toRootPairing.pairing i j = rl.pairing i.val.fst j.val.snd := by rfl

instance : rl.toRootPairing.IsCrystallographic where
  exists_value i j := by
    obtain ⟨hp, -⟩ := rl.idx_subset_span_int_sprod_span_int i.2
    obtain ⟨-, hq⟩ := rl.idx_subset_span_int_sprod_span_int j.2
    obtain ⟨z, hz⟩ := rl.exist_int_eq_pairing_of_mem_span_int hp hq
    exact ⟨z, by simp [toRootPairing_pairing, hz]⟩

lemma eq_one_or_neg_one_of_eq_zsmul_sRoot {p : M × N} (hp : p ∈ rl.idx) {z : ℤ} {j : n}
    (h : p.1 = z • rl.sRoot j) :
    z = 1 ∨ z = -1 := by
  obtain ⟨w, hw, i, rfl⟩ := hp
  replace hw := (rl.idx_subset_span_int_sprod_span_int <| rl.mk_mem_idx (inv_mem hw) j).1
  obtain ⟨c, hc : ∑ k, c k • rl.sRoot k = w.1.symm (rl.sRoot j)⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := c i)
  replace h : rl.sRoot i = z • w.1.symm (rl.sRoot j) := by simp [← map_zsmul, ← h]
  have : ∑ k, (z • c) k • rl.sRoot k = rl.sRoot i := by simp [h, ← hc, Finset.smul_sum, mul_smul]
  simpa using Fintype.linearIndependent_iffₛ.mp (rl.lin_ind_sRoot.restrict_scalars' ℤ) (z • c)
    (Pi.single i 1) (by rw [this, Fintype.sum_single_smul, one_smul]) i

instance : rl.toRootPairing.IsReduced where
  eq_or_eq_neg := by
    have : IsReflexive R M := .of_isPerfPair rl.pairing
    rintro ⟨⟨x₁, y₁⟩, hxy₁⟩ ⟨⟨x₂, y₂⟩, hxy₂⟩ hli
    obtain ⟨w, hw, i, hi⟩ := id hxy₂
    replace hi : w.1 (rl.sRoot i) = x₂ := by aesop
    suffices x₁ = x₂ ∨ x₁ = -x₂ by aesop
    obtain ⟨s, t, hst, hst0⟩ : ∃ s t : R, s • x₁ + t • x₂ = 0 ∧ (s = 0 → t ≠ 0) := by
      aesop (add simp LinearIndependent.pair_iff)
    have hs : s ≠ 0 := by have : x₂ ≠ 0 := rl.toRootPairing.ne_zero ⟨_, hxy₂⟩; aesop
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (rl.idx_subset_span_int_sprod_span_int (rl.apply_mem_idx (inv_mem hw) hxy₁)).1
    replace hc : w.1.symm x₁ = ∑ k, (c k : R) • rl.sRoot k := by
      simpa [Int.cast_smul_eq_zsmul] using hc.symm
    have hsum : ∑ k, (s * (c k : R) + if k = i then t else 0) • rl.sRoot k = 0 := by
      have : w.1.symm (s • x₁ + t • x₂) = 0 := by rw [hst, map_zero]
      simpa [hc, ← hi, Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    replace hsum := Fintype.linearIndependent_iff.mp rl.lin_ind_sRoot _ hsum
    have hxi' : w.1.symm x₁ = (c i) • rl.sRoot i := by
      rw [← Int.cast_smul_eq_zsmul R, hc, Finset.sum_eq_single i (fun k _ hk ↦ ?_) (by simp)]
      have := hsum k
      aesop
    have hxc : x₁ = (c i) • x₂ := by simpa [hi] using w.1.congr_arg hxi'
    have hi' : c i = 1 ∨ c i = -1 :=
      rl.eq_one_or_neg_one_of_eq_zsmul_sRoot (rl.apply_mem_idx (inv_mem hw) hxy₁) hxi'
    aesop

lemma isRootSystem_toRootPairing
    (hr : span R (range rl.sRoot) = ⊤)
    (hc : span R (range rl.sCoroot) = ⊤) :
    rl.toRootPairing.IsRootSystem where
  span_root_eq_top := by
    rw [eq_top_iff, ← hr]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨_, rl.sPair_mem_idx i⟩, by simp⟩
  span_coroot_eq_top := by
    rw [eq_top_iff, ← hc]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨_, rl.sPair_mem_idx i⟩, by simp⟩

lemma isIrreducible_toRootPairing [Nonempty n] {k V W : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (rl : Realisation n k V W)
    (hr : span k (range rl.sRoot) = ⊤) (hc : span k (range rl.sCoroot) = ⊤)
    (hA' : rl.matrix.IsIndecomposable) :
    rl.toRootPairing.IsIrreducible := by
  classical
  inhabit n
  have : Nontrivial V := nontrivial_of_ne (rl.sRoot default) 0 fun contra ↦ by
    simpa [contra] using rl.pairing_sRoot_sCoroot_self default
  have : rl.toRootPairing.IsRootSystem := rl.isRootSystem_toRootPairing hr hc
  refine .mk' _ fun q hq hq' ↦ ?_
  refine RootPairing.eq_top_of_mem_invtSubmodule_of_forall_eq_univ _ q hq' hq fun Φ _ hΦq hΦker ↦ ?_
  let f (i : n) : rl.idx := ⟨(rl.sRoot i, rl.sCoroot i), rl.sPair_mem_idx i⟩
  have hf (i j : n) : rl.toRootPairing.pairing (f i) (f j) = rl.matrix i j := rl.pairingMatrix i j
  replace hA' : (∀ i, f i ∈ Φ) ∨ (∀ i, f i ∉ Φ) := by
    have hbt : rl.matrix.BlockTriangular fun i ↦ if f i ∈ Φ then 1 else 0 := fun i j hij ↦ by
      have : rl.toRootPairing.coroot' (f j) (rl.toRootPairing.root (f i)) = 0 :=
        hΦker (f j) (by aesop) (hΦq ⟨f i, by aesop, rfl⟩)
      rwa [RootPairing.root_coroot'_eq_pairing, hf, Int.cast_eq_zero] at this
    obtain ⟨v, hv⟩ := rl.matrix.isIndecomposable_iff_blockTriangular_const.mp hA' _ hbt
    rcases eq_or_ne v 0 with rfl | hv'
    · exact Or.inr fun i hi ↦ by simpa [hi] using congr_fun hv i
    · exact Or.inl fun i ↦ by contrapose! hv'; simpa [hv'] using (congr_fun hv i).symm
  rcases hA' with hfΦ | hfΦ
  · obtain ⟨rfl⟩ : q = ⊤ := by
      rw [eq_top_iff, ← hr, Submodule.span_le]
      rintro - ⟨i, rfl⟩
      exact hΦq ⟨f i, hfΦ i, rfl⟩
    refine Set.eq_univ_of_forall fun j ↦ ?_
    contrapose! hΦker
    exact ⟨j, hΦker, by simpa using rl.toRootPairing.coroot'_ne_zero j⟩
  · exfalso
    apply hq'
    refine q.eq_bot_iff.mpr fun x hx ↦ ?_
    replace hx : rl.pairing x = 0 := LinearMap.ext_on hc <| by
      rintro - ⟨i, rfl⟩
      exact hΦker (f i) (hfΦ i) hx
    exact (LinearMap.IsPerfPair.bijective_left rl.pairing).injective <| by simp [hx]

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

private lemma span_range_sRoot_eq_top :
    span k (range (hA.toRealisation (hA.isUnit_map k).invertible).sRoot) = ⊤ := by
  suffices (hA.toRealisation (hA.isUnit_map k).invertible).sRoot = Pi.basisFun k n by simp [this]
  ext; simp [toRealisation]

/-- Given a field `k` of chacteristic zero and Cartan matrix `A`, this is a reduced
crystrallographic root system over `k`. It carries a natural base with Cartan matrix `A`. -/
def toRootPairing := (hA.toRealisation (hA.isUnit_map k).invertible).toRootPairing

instance : (hA.toRootPairing k).IsReduced :=
  inferInstanceAs (hA.toRealisation (hA.isUnit_map k).invertible).toRootPairing.IsReduced

instance : (hA.toRootPairing k).IsCrystallographic :=
  inferInstanceAs (hA.toRealisation (hA.isUnit_map k).invertible).toRootPairing.IsCrystallographic

instance : (hA.toRootPairing k).IsRootSystem :=
  CartanMatrix.Realisation.isRootSystem_toRootPairing _ (hA.span_range_sRoot_eq_top k)
    (hA.transpose.span_range_sRoot_eq_top k)

lemma isIrreducible_toRootPairing [Nonempty n] (hA' : A.IsIndecomposable) :
    (hA.toRootPairing k).IsIrreducible :=
  CartanMatrix.Realisation.isIrreducible_toRootPairing _ (hA.span_range_sRoot_eq_top k)
    (hA.transpose.span_range_sRoot_eq_top k) hA'

end Matrix.IsFiniteCartan
