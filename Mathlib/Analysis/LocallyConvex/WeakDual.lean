/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.locally_convex.weak_dual
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.LocallyConvex.WithSeminorms

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicit give a neighborhood basis in terms of the family of seminorms `λ x, ‖B x y‖`
for `y : F`.

## Main definitions

* `linear_map.to_seminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `λ x, ‖f x‖`.
* `linear_map.to_seminorm_family`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
`F → seminorm 𝕜 E`.

## Main statements

* `linear_map.has_basis_weak_bilin`: the seminorm balls of `B.to_seminorm_family` form a
neighborhood basis of `0` in the weak topology.
* `linear_map.to_seminorm_family.with_seminorms`: the topology of a weak space is induced by the
family of seminorm `B.to_seminorm_family`.
* `weak_bilin.locally_convex_space`: a spaced endowed with a weak topology is locally convex.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

weak dual, seminorm
-/


variable {𝕜 E F ι : Type _}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` by
`λ x, ‖f x‖` -/
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f
#align linear_map.to_seminorm LinearMap.toSeminorm

theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl
#align linear_map.coe_to_seminorm LinearMap.coe_toSeminorm

@[simp]
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl
#align linear_map.to_seminorm_apply LinearMap.toSeminorm_apply

theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, to_seminorm_apply]
#align linear_map.to_seminorm_ball_zero LinearMap.toSeminorm_ball_zero

theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm :=
  by
  ext
  simp only [Seminorm.comp_apply, to_seminorm_apply, coe_comp]
#align linear_map.to_seminorm_comp LinearMap.toSeminorm_comp

/-- Construct a family of seminorms from a bilinear form. -/
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm
#align linear_map.to_seminorm_family LinearMap.toSeminormFamily

@[simp]
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl
#align linear_map.to_seminorm_family_apply LinearMap.toSeminormFamily_apply

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

variable [Nonempty ι]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basis_sets id :=
  by
  let p := B.to_seminorm_family
  rw [nhds_induced, nhds_pi]
  simp only [map_zero, LinearMap.zero_apply]
  have h := @Metric.nhds_basis_ball 𝕜 _ 0
  have h' := Filter.hasBasis_pi fun i : F => h
  have h'' := Filter.HasBasis.comap (fun x y => B x y) h'
  refine' h''.to_has_basis _ _
  · rintro (U : Set F × (F → ℝ)) hU
    cases' hU with hU₁ hU₂
    simp only [id.def]
    let U' := hU₁.to_finset
    by_cases hU₃ : U.fst.nonempty
    · have hU₃' : U'.nonempty := hU₁.to_finset_nonempty.mpr hU₃
      refine'
        ⟨(U'.sup p).ball 0 <| U'.inf' hU₃' U.snd,
          p.basis_sets_mem _ <|
            (Finset.lt_inf'_iff _).2 fun y hy => hU₂ y <| hU₁.mem_to_finset.mp hy,
          fun x hx y hy => _⟩
      simp only [Set.mem_preimage, Set.mem_pi, mem_ball_zero_iff]
      rw [Seminorm.mem_ball_zero] at hx
      rw [← LinearMap.toSeminormFamily_apply]
      have hyU' : y ∈ U' := (Set.Finite.mem_toFinset hU₁).mpr hy
      have hp : p y ≤ U'.sup p := Finset.le_sup hyU'
      refine' lt_of_le_of_lt (hp x) (lt_of_lt_of_le hx _)
      exact Finset.inf'_le _ hyU'
    rw [set.not_nonempty_iff_eq_empty.mp hU₃]
    simp only [Set.empty_pi, Set.preimage_univ, Set.subset_univ, and_true_iff]
    exact Exists.intro ((p 0).ball 0 1) (p.basis_sets_singleton_mem 0 one_pos)
  rintro U (hU : U ∈ p.basis_sets)
  rw [SeminormFamily.basisSets_iff] at hU
  rcases hU with ⟨s, r, hr, hU⟩
  rw [hU]
  refine' ⟨(s, fun _ => r), ⟨by simp only [s.finite_to_set], fun y hy => hr⟩, fun x hx => _⟩
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, mem_ball_zero_iff] at hx
  simp only [id.def, Seminorm.mem_ball, sub_zero]
  refine' Seminorm.finset_sup_apply_lt hr fun y hy => _
  rw [LinearMap.toSeminormFamily_apply]
  exact hx y hy
#align linear_map.has_basis_weak_bilin LinearMap.hasBasis_weakBilin

theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  SeminormFamily.withSeminorms_of_hasBasis _ B.hasBasis_weakBilin
#align linear_map.weak_bilin_with_seminorms LinearMap.weakBilin_withSeminorms

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

variable [Nonempty ι] [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

instance {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} : LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex

