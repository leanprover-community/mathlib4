/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

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

public section
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
  ⟨fun x hx ↦
    let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
    let : Module ℝ E := .restrictScalars ℝ 𝕜 E
    have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
    have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
    RCLike.geometric_hahn_banach_point_point hx |>.imp fun f hf hf' ↦ by simp [hf'] at hf⟩

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

theorem eq_zero_of_forall_dual_eq_zero {x : V} (h : ∀ f : StrongDual R V, f x = 0) : x = 0 := by
  by_contra hx
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact hf (h f)

theorem eq_zero_iff_forall_dual_eq_zero (x : V) : x = 0 ↔ ∀ g : StrongDual R V, g x = 0 :=
  ⟨by simp +contextual, fun h => eq_zero_of_forall_dual_eq_zero (R := R) h⟩

/-- See also `geometric_hahn_banach_point_point`. -/
theorem eq_iff_forall_dual_eq {x y : V} : x = y ↔ ∀ g : StrongDual R V, g x = g y := by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero (R := R) (x - y)]
  simp [sub_eq_zero]

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
  push Not; rfl

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
  rcases ne_or_eq (u y) 0 with uy | uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : ∃ v : StrongDual R V, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx | vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel₀ vx, show (v x)⁻¹ * v y ≠ 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

variable [IsTopologicalAddGroup V] [ContinuousSMul R V]

section algebra
variable {S : Type*} [CommSemiring S] [Module S V] [SMulCommClass R S V] [Algebra S R]
  [IsScalarTower S R V] [ContinuousConstSMul S V]

/-- The center of continuous linear maps on a topological vector space
with separating dual is trivial, in other words, it is a central algebra. -/
instance _root_.Algebra.IsCentral.instContinuousLinearMap [Algebra.IsCentral S R] :
    Algebra.IsCentral S (V →L[R] V) where
  out f hf := by
    suffices ∃ α ∈ Subalgebra.center S R, f = α • .id R V from
      have ⟨_, ⟨y, _⟩, _⟩ := Algebra.IsCentral.center_eq_bot S R ▸ this
      ⟨y, by aesop⟩
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨g, hg⟩ := exists_eq_one (R := R) hx
    have (y : V) := by simpa [hg] using congr($(Subalgebra.mem_center_iff.mp hf (g.smulRight y)) x)
    exact ⟨g (f x), by simp [this, ContinuousLinearMap.ext_iff]⟩

open ContinuousLinearMap ContinuousLinearEquiv in
theorem _root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff
    {R V W : Type*} [NormedField R] [AddCommGroup V] [AddCommGroup W] [TopologicalSpace R]
    [TopologicalSpace V] [TopologicalSpace W] [IsTopologicalRing R] [Module R V] [Module R W]
    [SeparatingDual R V] [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]
    [ContinuousSMul R V] [ContinuousSMul R W] (f g : V ≃L[R] W) :
    f.conjContinuousAlgEquiv = g.conjContinuousAlgEquiv ↔ ∃ α : Rˣ, f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← ContinuousLinearMap.comp_assoc,
    eq_comp_toContinuousLinearMap_symm, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ f.toContinuousLinearMap, comp_coe, ← mul_def,
    ← Subalgebra.mem_center_iff (R := R), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one, ContinuousLinearEquiv.ext_iff]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : R), by ext; simp [h]⟩⟩
  if hy : y = 0 then exact ⟨1, funext fun x ↦ by simp [by simpa [hy] using congr($h x).symm]⟩
  else exact ⟨.mk0 y hy, funext fun x ↦ by simp [by simpa [eq_symm_apply] using congr($h x)]⟩

end algebra

/-- In a topological vector space with separating dual, the group of continuous linear equivalences
acts transitively on the set of nonzero vectors: given two nonzero vectors `x` and `y`, there
exists `A : V ≃L[R] V` mapping `x` to `y`. -/
theorem exists_continuousLinearEquiv_apply_eq
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : V ≃L[R] V, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : ∃ G : StrongDual R V, G x = 1 ∧ G y ≠ 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z ↦ z + G z • (y - x)
    invFun := fun z ↦ z + ((G y)⁻¹ * G z) • (x - y)
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
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

end Field

end SeparatingDual
