/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle Kytölä
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

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
* `LinearMap.polar_isClosed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

@[expose] public section

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

theorem polar_eq_biInter_preimage (s : Set E) :
    B.polar s = ⋂ x ∈ s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1) := by aesop

-- TODO: this theorem is abusing defeq between F and WeakBilin B.flip
theorem polar_isClosed (s : Set E) : IsClosed (X := WeakBilin B.flip) (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ ↦ Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)

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

theorem sInter_polar_finite_subset_eq_polar (s : Set E) :
    ⋂₀ (B.polar '' { F | F.Finite ∧ F ⊆ s }) = B.polar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha ↦ ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

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
      rw [B.map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul, norm_inv,
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

namespace StrongDual

section

variable (R M : Type*) [SeminormedCommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

theorem dualPairing_separatingLeft : (topDualPairing R M).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

end

section

/-- Given a subset `s` in a monoid `M` (over a commutative ring `R`), the polar `polar R s` is the
subset of `StrongDual R M` consisting of those functionals which evaluate to something of norm at
most one at all points `z ∈ s`. -/
def polar (R : Type*) [NormedCommRing R] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module R M] : Set M → Set (StrongDual R M) :=
  (topDualPairing R M).flip.polar

/-- Given a subset `s` in a monoid `M` (over a field `𝕜`) closed under scalar multiplication,
the polar `polarSubmodule 𝕜 s` is the submodule of `StrongDual 𝕜 M` consisting of those functionals
which evaluate to zero at all points `z ∈ s`. -/
def polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module 𝕜 M] {S : Type*} [SetLike S M] [SMulMemClass S 𝕜 M] (m : S) :
    Submodule 𝕜 (StrongDual 𝕜 M) := (topDualPairing 𝕜 M).flip.polarSubmodule m

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]

lemma polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) :
    (polarSubmodule 𝕜 m : Set (StrongDual 𝕜 E)) = polar 𝕜 m := rfl

theorem mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl

lemma polarSubmodule_eq_setOf {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    polarSubmodule 𝕜 m = { y : StrongDual 𝕜 E | ∀ x ∈ m, y x = 0 } :=
  (topDualPairing 𝕜 E).flip.polar_subMulAction _

lemma mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
    (y : StrongDual 𝕜 E) : y ∈ polarSubmodule 𝕜 m ↔ ∀ x ∈ m, y x = 0 :=
  propext_iff.mp congr($(polarSubmodule_eq_setOf 𝕜 m) y)

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : StrongDual 𝕜 E) ∈ polar 𝕜 s :=
  LinearMap.zero_mem_polar _ s

theorem polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s) :=
  LinearMap.polar_nonempty _ _

open Set

@[simp]
theorem polar_empty : polar 𝕜 (∅ : Set E) = Set.univ :=
  LinearMap.polar_empty _

@[simp]
theorem polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ ≤ 1 } := by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, topDualPairing_apply]

theorem mem_polar_singleton {a : E} (y : StrongDual 𝕜 E) : y ∈ polar 𝕜 {a} ↔ ‖y a‖ ≤ 1 := by
  simp only [polar_singleton, mem_setOf_eq]

theorem polar_zero : polar 𝕜 ({0} : Set E) = Set.univ :=
  LinearMap.polar_zero _

end

section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

open Set

@[simp]
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)} :=
  (topDualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

end

end StrongDual
