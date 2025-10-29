/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The rank of a linear map

## Main Definition
-  `LinearMap.rank`: The rank of a linear map.
-/


noncomputable section

universe u v v' v''

variable {K : Type u} {V V₁ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

open Cardinal Basis Submodule Function Set

namespace LinearMap

section Ring

variable [Ring K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V'] [Module K V']

/-- `rank f` is the rank of a `LinearMap` `f`, defined as the dimension of `f.range`. -/
abbrev rank (f : V →ₗ[K] V') : Cardinal :=
  Module.rank K (LinearMap.range f)

theorem rank_le_range (f : V →ₗ[K] V') : rank f ≤ Module.rank K V' :=
  Submodule.rank_le _

theorem rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V :=
  rank_range_le _

@[simp]
theorem rank_zero [Nontrivial K] : rank (0 : V →ₗ[K] V') = 0 := by
  rw [rank, LinearMap.range_zero, rank_bot]

variable [AddCommGroup V''] [Module K V'']

theorem rank_comp_le_left (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f := by
  refine Submodule.rank_mono ?_
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

theorem lift_rank_comp_le_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) ≤ Cardinal.lift.{v''} (rank g) := by
  rw [rank, rank, LinearMap.range_comp]; exact lift_rank_map_le _ _

/-- The rank of the composition of two maps is less than the minimum of their ranks. -/
theorem lift_rank_comp_le (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) ≤
      min (Cardinal.lift.{v'} (rank f)) (Cardinal.lift.{v''} (rank g)) :=
  le_min (Cardinal.lift_le.mpr <| rank_comp_le_left _ _) (lift_rank_comp_le_right _ _)

variable [AddCommGroup V'₁] [Module K V'₁]

theorem rank_comp_le_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) : rank (f.comp g) ≤ rank g := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le_right g f

/-- The rank of the composition of two maps is less than the minimum of their ranks.

See `lift_rank_comp_le` for the universe-polymorphic version. -/
theorem rank_comp_le (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) :
    rank (f.comp g) ≤ min (rank f) (rank g) := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le g f

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V'] [Module K V']

theorem rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
  calc
    rank (f + g) ≤ Module.rank K (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') := by
      refine Submodule.rank_mono ?_
      exact LinearMap.range_le_iff_comap.2 <| eq_top_iff'.2 fun x =>
        show f x + g x ∈ (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    _ ≤ rank f + rank g := Submodule.rank_add_le_rank_add_rank _ _

theorem rank_finset_sum_le {η} (s : Finset η) (f : η → V →ₗ[K] V') :
    rank (∑ d ∈ s, f d) ≤ ∑ d ∈ s, rank (f d) :=
  @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a ≤ b) f (fun d => rank (f d)) s
    (le_of_eq rank_zero) fun _ _ _ h => le_trans (rank_add_le _ _) (by gcongr)

theorem le_rank_iff_exists_linearIndependent {c : Cardinal} {f : V →ₗ[K] V'} :
    c ≤ rank f ↔ ∃ s : Set V,
    Cardinal.lift.{v'} #s = Cardinal.lift.{v} c ∧ LinearIndepOn K f s := by
  rcases f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict with ⟨g, hg⟩
  have fg : LeftInverse f.rangeRestrict g := LinearMap.congr_fun hg
  refine ⟨fun h => ?_, ?_⟩
  · rcases _root_.le_rank_iff_exists_linearIndependent.1 h with ⟨s, rfl, si⟩
    refine ⟨g '' s, Cardinal.mk_image_eq_lift _ _ fg.injective, ?_⟩
    replace fg : ∀ x, f (g x) = x := by
      intro x
      convert congr_arg Subtype.val (fg x)
    replace si : LinearIndepOn K (fun x => f (g x)) s := by
      simpa only [fg] using si.map' _ (ker_subtype _)
    exact si.image_of_comp
  · rintro ⟨s, hsc, si⟩
    have : LinearIndepOn K f.rangeRestrict s :=
      LinearIndependent.of_comp (LinearMap.range f).subtype (by convert si)
    convert this.id_image.cardinal_le_rank
    rw [← Cardinal.lift_inj, ← hsc, Cardinal.mk_image_eq_of_injOn_lift]
    exact injOn_iff_injective.2 this.injective

theorem le_rank_iff_exists_linearIndependent_finset {n : ℕ} {f : V →ₗ[K] V'} :
    ↑n ≤ rank f ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s : Set V) => f x := by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff,
    Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

end DivisionRing

end LinearMap
