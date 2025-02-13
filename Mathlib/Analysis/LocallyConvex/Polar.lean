/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle Kytölä
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.Topology.Algebra.Module.WeakBilin

/-!
# Polar set

In this file we define the polar set. There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, where `𝕜` is a normed commutative ring and
`E` and `F` are modules over `𝕜`.

## Main definitions

* `LinearMap.polar`: The polar of a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.

## Main statements

* `LinearMap.polar_eq_iInter`: The polar as an intersection.
* `LinearMap.subset_bipolar`: The polar is a subset of the bipolar.
* `LinearMap.polar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

variable {𝕜 E F : Type*}

open Topology

namespace LinearMap

section NormedRing

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The (absolute) polar of `s : Set E` is given by the set of all `y : F` such that `‖B x y‖ ≤ 1`
for all `x ∈ s`. -/
def polar (s : Set E) : Set F :=
  { y : F | ∀ x ∈ s, ‖B x y‖ ≤ 1 }

theorem polar_mem_iff (s : Set E) (y : F) : y ∈ B.polar s ↔ ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  Iff.rfl

theorem polar_mem (s : Set E) (y : F) (hy : y ∈ B.polar s) : ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  hy

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : F) ∈ B.polar s := fun _ _ => by
  simp only [map_zero, norm_zero, zero_le_one]

theorem polar_nonempty (s : Set E) : Set.Nonempty (B.polar s) := by
  use 0
  exact zero_mem_polar B s

theorem polar_eq_iInter {s : Set E} : B.polar s = ⋂ x ∈ s, { y : F | ‖B x y‖ ≤ 1 } := by
  ext
  simp only [polar_mem_iff, Set.mem_iInter, Set.mem_setOf_eq]

/-- The map `B.polar : Set E → Set F` forms an order-reversing Galois connection with
`B.flip.polar : Set F → Set E`. We use `OrderDual.toDual` and `OrderDual.ofDual` to express
that `polar` is order-reversing. -/
theorem polar_gc :
    GaloisConnection (OrderDual.toDual ∘ B.polar) (B.flip.polar ∘ OrderDual.ofDual) := fun _ _ =>
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hx⟩

@[simp]
theorem polar_iUnion {ι} {s : ι → Set E} : B.polar (⋃ i, s i) = ⋂ i, B.polar (s i) :=
  B.polar_gc.l_iSup

@[simp]
theorem polar_union {s t : Set E} : B.polar (s ∪ t) = B.polar s ∩ B.polar t :=
  B.polar_gc.l_sup

theorem polar_antitone : Antitone (B.polar : Set E → Set F) :=
  B.polar_gc.monotone_l

@[simp]
theorem polar_empty : B.polar ∅ = Set.univ :=
  B.polar_gc.l_bot

@[simp]
theorem polar_singleton {a : E} : B.polar {a} = { y | ‖B a y‖ ≤ 1 } := le_antisymm
  (fun _ hy => hy _ rfl)
  (fun y hy => (polar_mem_iff _ _ _).mp (fun _ hb => by rw [Set.mem_singleton_iff.mp hb]; exact hy))

theorem mem_polar_singleton {x : E} (y : F) : y ∈ B.polar {x} ↔ ‖B x y‖ ≤ 1 := by
  simp only [polar_singleton, Set.mem_setOf_eq]

theorem polar_zero : B.polar ({0} : Set E) = Set.univ := by
  simp only [polar_singleton, map_zero, zero_apply, norm_zero, zero_le_one, Set.setOf_true]

theorem subset_bipolar (s : Set E) : s ⊆ B.flip.polar (B.polar s) := fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]
theorem tripolar_eq_polar (s : Set E) : B.polar (B.flip.polar (B.polar s)) = B.polar s :=
  (B.polar_antitone (B.subset_bipolar s)).antisymm (subset_bipolar B.flip (B.polar s))

/-- The polar set is closed in the weak topology induced by `B.flip`. -/
theorem polar_weak_closed (s : Set E) : IsClosed[WeakBilin.instTopologicalSpace B.flip]
    (B.polar s) := by
  rw [polar_eq_iInter]
  refine isClosed_iInter fun x => isClosed_iInter fun _ => ?_
  exact isClosed_le (WeakBilin.eval_continuous B.flip x).norm continuous_const

theorem sInter_polar_finite_subset_eq_polar (s : Set E) :
    ⋂₀ (B.polar '' { F | F.Finite ∧ F ⊆ s }) = B.polar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha ↦ ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

theorem iInter_polar_singleton_eq_polar (s : Set E) :
    ⋂ i ∈ s, (B.polar { i }) = B.polar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha ↦ ?_, fun hx a ha => (mem_polar_singleton B x).mpr (hx a ha)⟩
  simpa [mem_polar_singleton] using hx _ ha

end NormedRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

theorem polar_univ (h : SeparatingRight B) : B.polar Set.univ = {(0 : F)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_polar], fun y hy => h _ fun x => ?_⟩
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc
    ‖B x y‖ = ‖c‖ * ‖B (c⁻¹ • x) y‖ := by
      rw [B.map_smul, LinearMap.smul_apply, Algebra.id.smul_eq_mul, norm_mul, norm_inv,
        mul_inv_cancel_left₀ hc.ne']
    _ ≤ ε * 1 := by gcongr; exact hy _ trivial
    _ = ε := mul_one _

theorem polar_subMulAction {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    B.polar m = { y | ∀ x ∈ m, B x y = 0 } := by
  ext y
  constructor
  · intro hy x hx
    obtain ⟨r, hr⟩ := NormedField.exists_lt_norm 𝕜 ‖B x y‖⁻¹
    contrapose! hr
    rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hr)]
    simpa using hy _ (SMulMemClass.smul_mem r hx)
  · intro h x hx
    simp [h x hx]

/-- The polar of a set closed under scalar multiplication as a submodule -/
def polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : Submodule 𝕜 F :=
  .copy (⨅ x ∈ m, LinearMap.ker (B x)) (B.polar m) <| by ext; simp [polar_subMulAction]

end NontriviallyNormedField

end LinearMap
