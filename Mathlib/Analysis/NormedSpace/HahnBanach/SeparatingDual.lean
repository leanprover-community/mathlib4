/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Central.Defs
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Spaces with separating dual

We introduce a typeclass `SeparatingDual R V`, registering that the points of the topological
module `V` over `R` can be separated by continuous linear forms.

This property is satisfied for normed spaces over `ℝ` or `ℂ` (by the analytic Hahn-Banach theorem)
and for locally convex topological spaces over `ℝ` (by the geometric Hahn-Banach theorem).

We show in `SeparatingDual.exists_ne_zero` that given any non-zero vector in an `R`-module `V`
satisfying `SeparatingDual R V`, there exists a continuous linear functional whose value on `v` is
non-zero.

As a consequence of the existence of `SeparatingDual.exists_ne_zero`, a generalization of
Hahn-Banach beyond the normed setting, we show that if `V` and `W` are nontrivial topological vector
spaces over a topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`,
there are nontrivial continuous `R`-linear operators between `V` and `W`. This is recorded in the
instance `SeparatingDual.instNontrivialContinuousLinearMapIdOfContinuousSMul`.

Under the assumption `SeparatingDual R V`, we show in
`SeparatingDual.exists_continuousLinearEquiv_apply_eq` that the group of continuous linear
equivalences acts transitively on the set of nonzero vectors.
-/
/-- When `E` is a topological module over a topological ring `R`, the class `SeparatingDual R E`
registers that continuous linear forms on `E` separate points of `E`. -/
@[mk_iff separatingDual_def]
class SeparatingDual (R V : Type*) [Ring R] [AddCommGroup V] [TopologicalSpace V]
    [TopologicalSpace R] [Module R V] : Prop where
  /-- Any nonzero vector can be mapped by a continuous linear map to a nonzero scalar. -/
  exists_ne_zero' : ∀ (x : V), x ≠ 0 → ∃ f : StrongDual R V, f x ≠ 0

instance {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T1Space E] : SeparatingDual ℝ E :=
  ⟨fun x hx ↦ by
    rcases geometric_hahn_banach_point_point hx.symm with ⟨f, hf⟩
    simp only [map_zero] at hf
    exact ⟨f, hf.ne'⟩⟩

instance {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx ↦ by
    rcases exists_dual_vector 𝕜 x hx with ⟨f, -, hf⟩
    refine ⟨f, ?_⟩
    simpa [hf] using hx⟩

namespace SeparatingDual

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [TopologicalSpace R] [Module R V] [SeparatingDual R V]

lemma exists_ne_zero {x : V} (hx : x ≠ 0) :
    ∃ f : StrongDual R V, f x ≠ 0 :=
  exists_ne_zero' x hx

theorem exists_separating_of_ne {x y : V} (h : x ≠ y) :
    ∃ f : StrongDual R V, f x ≠ f y := by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩

protected theorem t1Space [T1Space R] : T1Space V := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩

protected theorem t2Space [T2Space R] : T2Space V := by
  apply (t2Space_iff _).2 (fun {x} {y} hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf

end Ring

section Field

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [IsTopologicalRing R] [Module R V]

-- TODO (@alreadydone): this could generalize to CommRing R if we were to add a section
theorem _root_.separatingDual_iff_injective : SeparatingDual R V ↔
    Function.Injective (ContinuousLinearMap.coeLM (R := R) R (M := V) (N₃ := R)).flip := by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm ∀ v, ?_
  rw [not_imp_comm, LinearMap.ext_iff]
  push_neg; rfl

variable [SeparatingDual R V]

open Function

/-- Given a finite-dimensional subspace `W` of a space `V` with separating dual, any
  linear functional on `W` extends to a continuous linear functional on `V`.
  This is stated more generally for an injective linear map from `W` to `V`. -/
theorem dualMap_surjective_iff {W} [AddCommGroup W] [Module R W] [FiniteDimensional R W]
    {f : W →ₗ[R] V} : Surjective (f.dualMap ∘ ContinuousLinearMap.toLinearMap) ↔ Injective f := by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

variable (V) in
open ContinuousLinearMap in
/- As a consequence of the existence of non-zero linear maps, itself a consequence of Hahn-Banach
in the normed setting, we show that if `V` and `W` are nontrivial topological vector spaces over a
topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`, there are
nontrivial continuous `R`-linear operators between `V` and `W`. -/
instance (W) [AddCommGroup W] [TopologicalSpace W] [Module R W] [Nontrivial W]
   [ContinuousSMul R W] [Nontrivial V] : Nontrivial (V →L[R] W) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨ψ, hψ⟩ := exists_ne_zero (R := R) hv
  exact ⟨ψ.smulRight w, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

lemma exists_eq_one {x : V} (hx : x ≠ 0) :
    ∃ f : StrongDual R V, f x = 1 := by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

theorem exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ f : StrongDual R V, f x = 1 ∧ f y ≠ 0 := by
  obtain ⟨u, ux⟩ : ∃ u : StrongDual R V, u x = 1 := exists_eq_one hx
  rcases ne_or_eq (u y) 0 with uy|uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : ∃ v : StrongDual R V, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx|vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel₀ vx, show (v x)⁻¹ * v y ≠ 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

variable [IsTopologicalAddGroup V]

/-- The center of continuous linear maps on a topological vector space
with separating dual is trivial, in other words, it is a central algebra. -/
instance _root_.Algebra.IsCentral.continuousLinearMap [ContinuousSMul R V] :
    Algebra.IsCentral R (V →L[R] V) where
  out T hT := by
    have h' (f : StrongDual R V) (y v : V) : f (T v) • y = f v • T y := by
      simpa using congr($(Subalgebra.mem_center_iff.mp hT <| f.smulRight y) v)
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨f, hf⟩ := exists_eq_one (R := R) hx
    exact ⟨f (T x), ContinuousLinearMap.ext fun _ => by simp [h', hf]⟩

/-- In a topological vector space with separating dual, the group of continuous linear equivalences
acts transitively on the set of nonzero vectors: given two nonzero vectors `x` and `y`, there
exists `A : V ≃L[R] V` mapping `x` to `y`. -/
theorem exists_continuousLinearEquiv_apply_eq [ContinuousSMul R V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : V ≃L[R] V, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : ∃ G : StrongDual R V, G x = 1 ∧ G y ≠ 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z ↦ z + G z • (y - x)
    invFun := fun z ↦ z + ((G y) ⁻¹ * G z) • (x - y)
    map_add' := fun a b ↦ by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z ↦ by
      simp only [RingHom.id_apply, smul_eq_mul,
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
        map_add, map_smulₛₗ _, map_sub, Gx, mul_sub, mul_one, add_sub_cancel]
      rw [mul_comm (G z), ← mul_assoc, inv_mul_cancel₀ Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z ↦ by
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [map_add, map_smulₛₗ _, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y), ← mul_assoc, mul_inv_cancel₀ Gy]
      simp only [smul_sub, one_mul, add_sub_cancel]
      abel
    continuous_toFun := continuous_id.add (G.continuous.smul continuous_const)
    continuous_invFun :=
      continuous_id.add ((continuous_const.mul G.continuous).smul continuous_const) }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

open Filter
open scoped Topology

section
variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SeparatingDual 𝕜 E] [Nontrivial E]

/-- If a space of linear maps from `E` to `F` is complete, and `E` is nontrivial, then `F` is
complete. -/
lemma completeSpace_of_completeSpace_continuousLinearMap [CompleteSpace (E →L[𝕜] F)] :
    CompleteSpace F := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  obtain ⟨v, hv⟩ : ∃ (v : E), v ≠ 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ : ∃ φ : StrongDual 𝕜 E, φ v = 1 := exists_eq_one hv
  let g : ℕ → (E →L[𝕜] F) := fun n ↦ ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
  have : CauchySeq g := (ContinuousLinearMap.smulRightL 𝕜 E F φ).lipschitz.cauchySeq_comp hf
  obtain ⟨a, ha⟩ : ∃ a, Tendsto g atTop (𝓝 a) := cauchy_iff_exists_le_nhds.mp this
  refine ⟨a v, ?_⟩
  have : Tendsto (fun n ↦ g n v) atTop (𝓝 (a v)) := by
    have : Continuous (fun (i : E →L[𝕜] F) ↦ i v) := by fun_prop
    exact (this.tendsto _).comp ha
  simpa [g, ContinuousLinearMap.smulRightL, hφ]

lemma completeSpace_continuousLinearMap_iff :
    CompleteSpace (E →L[𝕜] F) ↔ CompleteSpace F :=
  ⟨fun _h ↦ completeSpace_of_completeSpace_continuousLinearMap 𝕜 E F, fun _h ↦ inferInstance⟩

open ContinuousMultilinearMap

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)]
  [∀ i, NormedSpace 𝕜 (M i)] [∀ i, SeparatingDual 𝕜 (M i)]

/-- If a space of multilinear maps from `Π i, E i` to `F` is complete, and each `E i` has a nonzero
element, then `F` is complete. -/
lemma completeSpace_of_completeSpace_continuousMultilinearMap
    [CompleteSpace (ContinuousMultilinearMap 𝕜 M F)]
    {m : ∀ i, M i} (hm : ∀ i, m i ≠ 0) : CompleteSpace F := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have : ∀ i, ∃ φ : StrongDual 𝕜 (M i), φ (m i) = 1 := fun i ↦ exists_eq_one (hm i)
  choose φ hφ using this
  cases nonempty_fintype ι
  let g : ℕ → (ContinuousMultilinearMap 𝕜 M F) := fun n ↦
    compContinuousLinearMapL φ
    (ContinuousMultilinearMap.smulRightL 𝕜 _ F ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝕜)) (f n))
  have : CauchySeq g := by
    refine (ContinuousLinearMap.lipschitz _).cauchySeq_comp ?_
    exact (ContinuousLinearMap.lipschitz _).cauchySeq_comp hf
  obtain ⟨a, ha⟩ : ∃ a, Tendsto g atTop (𝓝 a) := cauchy_iff_exists_le_nhds.mp this
  refine ⟨a m, ?_⟩
  have : Tendsto (fun n ↦ g n m) atTop (𝓝 (a m)) := ((continuous_eval_const _).tendsto _).comp ha
  simpa [g, hφ]

lemma completeSpace_continuousMultilinearMap_iff {m : ∀ i, M i} (hm : ∀ i, m i ≠ 0) :
    CompleteSpace (ContinuousMultilinearMap 𝕜 M F) ↔ CompleteSpace F :=
  ⟨fun _h ↦ completeSpace_of_completeSpace_continuousMultilinearMap 𝕜 F hm, fun _h ↦ inferInstance⟩

end

end Field

end SeparatingDual
