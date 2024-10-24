/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.CompletelyRegular
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Fintype.Order

/-!
# Uniform spaces are completely regular

This module proves that uniform spaces are equivalent to completely regular spaces,
which are spaces in which each closed set `K ⊆ X` and point `x ∈ Kᶜ`
admits a continuous function `f` from `X` to the unit interval,
such that `f x = 0` and `∀ y ∈ K, f y = 1`.

To obtain this result, we first show that for any point of open set `x ∈ s`,
there exists a family `D` of pseudometrics and an `ε > 0`,
such that `⋂ m ∈ D, @Metric.ball _ m x ε ⊆ s`.

One can then use this to define a continuous function `f` satisfying the requirements of a
completely regular space.

## Main statements

* `UniformSpace.UniformSpaceOf`, the uniform space associated with a set `s ∈ 𝓤 X`,
  whose uniformity is coarser than `𝓤 X` and that is countably generated.
* `UniformSpace.PseudoMetricSpaceOf`, the pseudometric space associated with its corresponding
  `UniformSpaceOf` space.
* `UniformSpace.exists_pseudoMetricSpace_family_of_isOpen`: for every point `x ∈ s` with `s` open,
  there exists a finite family of pseudometric spaces coarser than `X` and an `ε > 0`, such that
  the intersection of those families is a subset of `s`.
* `UniformSpace.completelyRegularSpace`: a uniform space is a completely regular space.

## TODO

Provide a way to construct a uniformity from the definition of a completely regular spaces,
fully deprecating `CompletelyRegularSpace`.

## References

* N. Bourbaki, General Topology, Chapter 9
* Stephen Willard, General Topology

-/

variable {X : Type*} [unf : UniformSpace X]
open Topology Uniformity

namespace UniformSpace

section PseudoMetrics

variable {s : Set (X × X)}

/--
A series of symmetric sets in `X × X`, with `UniformityBasisOf _ n ⊆ s` for some `s ∈ 𝓤 X`,
and `(UniformityBasisOf _ (n + 1)) ^ 2 ⊆ UniformityBasisOf _ n`.

When used to generate a filter, this series yields a uniformity (`UniformSpace.UniformSpaceOf`)
that is coarser than the ambient `𝓤 X`.
-/
noncomputable def UniformityBasisOf (s_in_unf : s ∈ 𝓤 X) :
    ℕ → { s : Set (X × X) // s ∈ 𝓤 X }
  | 0 => ⟨symmetrizeRel s, symmetrize_mem_uniformity s_in_unf⟩
  | Nat.succ n =>
    let ⟨_, t_in_uni⟩ := UniformSpace.UniformityBasisOf s_in_unf n
    ⟨(comp_symm_mem_uniformity_sets t_in_uni).choose,
      (comp_symm_mem_uniformity_sets t_in_uni).choose_spec.1⟩

theorem uniformityBasisOf_symmetric (s_in_unf : s ∈ 𝓤 X) (n : ℕ) :
    SymmetricRel (UniformityBasisOf s_in_unf n).val := by
  cases n with
  | zero => exact symmetric_symmetrizeRel s
  | succ n =>
    exact (comp_symm_mem_uniformity_sets <| (UniformityBasisOf s_in_unf n).prop).choose_spec.2.1

theorem uniformityBasisOf_comp_subset (s_in_unf : s ∈ 𝓤 X) (n : ℕ) :
    compRel
      (UniformityBasisOf s_in_unf <| n + 1).val
      (UniformityBasisOf s_in_unf <| n + 1).val ⊆ UniformityBasisOf s_in_unf n := by
  rw [← Nat.succ_eq_add_one]
  exact (comp_symm_mem_uniformity_sets <| (UniformityBasisOf s_in_unf n).prop).choose_spec.2.2

theorem uniformity_le_uniformSpaceOf (s_in_unf : s ∈ 𝓤 X) :
    𝓤 X ≤ Filter.generate { (UniformSpace.UniformityBasisOf s_in_unf n).val | n : ℕ } := by
  rw [Filter.le_generate_iff]
  intro r
  simp only [Set.mem_setOf_eq, Filter.mem_sets, forall_exists_index]
  intro n r_eq
  exact r_eq ▸ (UniformityBasisOf s_in_unf n).prop

/--
The uniform space associated with a set `s ∈ 𝓤 X`:

* It is finitely generated (`UniformSpace.uniformSpaceOf_finitelyGenerated`).
* It is coarser than `𝓤 X` (`UniformSpace.uniformity_le_uniformSpaceOf`).
* The infimum of all the `UniformSpaceOf` is equal to the ambient uniform space
  (`UniformSpace.uniformity_eq_iInf_uniformSpaceOf`).
-/
def UniformSpaceOf (s_in_unf : s ∈ 𝓤 X) : UniformSpace X :=
  let uniformity := Filter.generate { (UniformSpace.UniformityBasisOf s_in_unf n).val | n : ℕ }
  UniformSpace.ofCore {
    uniformity := uniformity
    refl := by
      intro r r_in_unf
      rw [Filter.mem_principal, idRel_subset]
      exact fun x => refl_mem_uniformity <| uniformity_le_uniformSpaceOf s_in_unf r_in_unf
    symm := by
      rw [Filter.Tendsto, Filter.le_generate_iff]
      intro r ⟨n, r_eq⟩
      rw [← r_eq, Filter.mem_sets, Filter.mem_map, UniformSpace.uniformityBasisOf_symmetric]
      apply Filter.mem_generate_of_mem
      use n
    comp := by
      rw [Filter.le_generate_iff]
      intro r ⟨n, r_eq⟩
      rw [← r_eq]
      apply Filter.mem_of_superset _ <| UniformSpace.uniformityBasisOf_comp_subset s_in_unf n
      apply (Filter.mem_lift'_sets <| Monotone.compRel monotone_id monotone_id).mpr
      exact ⟨_, Filter.mem_generate_of_mem ⟨n + 1, rfl⟩, subset_refl _⟩
  }

theorem self_mem_uniformSpaceOf (s_in_unf : s ∈ 𝓤 X) :
    s ∈ (UniformSpaceOf s_in_unf).uniformity :=
  Filter.mem_of_superset (Filter.mem_generate_of_mem (Exists.intro 0 rfl))
    <| (symmetrizeRel_subset_self _)

/--
The ambient uniformity is equal to the infimum of all `UniformSpaceOf` for `s ∈ 𝓤 X`.
-/
theorem uniformity_eq_iInf_uniformSpaceOf :
    𝓤 X = ⨅ s, ⨅ (h : s ∈ 𝓤 X), 𝓤[UniformSpaceOf h] :=
  _root_.le_antisymm
    (by
      simp_rw [le_iInf_iff]
      exact fun _ mem_unf => uniformity_le_uniformSpaceOf mem_unf)
    (fun (r : Set (X × X)) (r_in_unf : r ∈ 𝓤 X) =>
      Filter.mem_iInf_of_mem r
        <| Filter.mem_iInf_of_mem r_in_unf
        <| self_mem_uniformSpaceOf r_in_unf)

/--
The uniformity associated with `s ∈ 𝓤 X` is countably generated, so a pseudometric space
can be constructed for it.

Note that the uniformity associated with `s ∈ 𝓤 X` is in general
not equal to the ambient uniformity, see `UniformSpace.UniformSpaceOf` for more details.
-/
noncomputable def PseudoMetricSpaceOf (s_in_unf : s ∈ 𝓤 X) : PseudoMetricSpace X :=
  @UniformSpace.pseudoMetricSpace X (UniformSpaceOf s_in_unf)
    ⟨⟨_, Set.countable_range fun n => (UniformityBasisOf s_in_unf n).val, rfl⟩⟩

/--
If a set `t` is open within the topology generated by `UniformSpaceOf s_in_unf`,
then one can find some `ε > 0` for all of its points
-/
theorem isOpen_uniformSpaceOf_iff (s_in_unf : s ∈ 𝓤 X) {t : Set X} :
    IsOpen[(UniformSpaceOf s_in_unf).toTopologicalSpace] t ↔
      ∀ x ∈ t, ∃ ε, 0 < ε ∧ @Metric.ball X (PseudoMetricSpaceOf s_in_unf) x ε ⊆ t :=
  @Metric.isOpen_iff X (PseudoMetricSpaceOf s_in_unf) _

/--
If `x ∈ s` for some open `s`, then there exists a family of pseudometric spaces `D`
and an `ε > 0`, such that:
* `∀ m ∈ D`, the topology associated with `D` is coarser than the ambient topology on `X`.
* The intersection of the balls $$B_d(x, ε)$$ for all `d ∈ D` is a subset of `s`.
-/
theorem exists_pseudoMetricSpace_family_of_isOpen {s : Set X} (s_open : IsOpen s)
    {x : X} (x_in_s : x ∈ s) : ∃ D : Set (PseudoMetricSpace X), D.Finite ∧
      (∀ m ∈ D, unf.toTopologicalSpace ≤ m.toUniformSpace.toTopologicalSpace) ∧
      ∃ (ε : ℝ), 0 < ε ∧ ⋂ m ∈ D, @Metric.ball X m x ε ⊆ s := by
  rw [isOpen_iff_ball_subset] at s_open
  let ⟨V, V_in_unf, ball_subset⟩ := s_open x x_in_s
  rw [uniformity_eq_iInf_uniformSpaceOf] at V_in_unf

  -- We firts obtain a family `t` of sets `r ∈ 𝓤 X`,
  -- as well as a map `f` such that `∀ r ∈ t, f r ∈ 𝓤[UniformSpaceOf r]`.
  rw [← iInf_subtype (f := fun pair : { t : Set (X × X) // t ∈ 𝓤 X } =>
    @uniformity X <| UniformSpaceOf pair.prop), Filter.mem_iInf] at V_in_unf
  have ⟨t, t_finite, f, f_mem_unf, V_eq⟩ := V_in_unf
  rw [Set.Finite] at t_finite
  rw [V_eq] at ball_subset
  clear V_in_unf s_open V_eq V

  by_cases t_nonempty : Nonempty t; swap
  {
    -- If `t` is empty, then `s = Set.univ`, we don't need to provide any pseudometric space.
    rw [not_nonempty_iff] at t_nonempty
    simp only [ball, Set.iInter_of_empty, Set.preimage_univ, Set.univ_subset_iff] at ball_subset
    rw [ball_subset]
    use ∅
    simp only [Set.finite_empty, gt_iff_lt, Set.mem_empty_iff_false, Set.iInter_of_empty,
      Set.iInter_univ, Set.subset_univ, and_true, true_and]
    refine ⟨fun _ ff => ff.elim, ?eps⟩
    use 1
    exact zero_lt_one
  }

  -- We then construct a version of `interior ∘ f`, where each set `f ⟨i, i_in_unf⟩` is mapped to
  -- `interior[UniformSpaceOf i_in_unf] (f i)`.
  let f' : t → Set (X × X) := fun v =>
    let inst : TopologicalSpace X := (UniformSpaceOf v.val.prop).toTopologicalSpace
    @interior (X × X) (@instTopologicalSpaceProd _ _ inst inst) (f v)

  have x_in_ball_iInter : x ∈ ball x (⋂ i : t, f' i) := by
    apply UniformSpace.mem_ball_self
    rw [Filter.iInter_mem]
    intro i
    apply uniformity_le_uniformSpaceOf i.val.prop
    let _inst := UniformSpaceOf i.val.prop
    exact interior_mem_uniformity (f_mem_unf i)

  have ball_isOpen : ∀ i : t, IsOpen[(UniformSpaceOf i.val.prop).toTopologicalSpace]
      (ball x (f' i)) := fun i =>
    let _inst := UniformSpaceOf i.val.prop
    isOpen_ball _ isOpen_interior

  -- Each `ball x (f' i)` is open in `UniformSpaceOf i_in_unf` and contains `x`,
  -- so we can use the pseudometric associated with `i` to get a set of `ε`,
  -- such that the metric ball associated with each `i` is a subset of the uniform ball
  -- associated with `i`.
  simp_rw [UniformSpace.isOpen_uniformSpaceOf_iff] at ball_isOpen
  replace ball_isOpen := fun i => ball_isOpen i x
    <| ball_mono (Set.iInter_subset _ i) x x_in_ball_iInter
  choose ε ε_pos ball_subset' using ball_isOpen

  -- We finally just need to show that the family of pseudometric space associated
  -- with elements of `t` and `iInf ε` satisfy our requirements.
  let D := (fun v => PseudoMetricSpaceOf v.prop) '' t
  refine ⟨D, Set.Finite.image _ t_finite, ?topology_le, ⟨iInf ε, ?pos, ?subset⟩⟩
  case pos =>
    rw [← sInf_range, Set.Finite.lt_cInf_iff (Set.finite_range ε) (Set.range_nonempty ε)]
    exact fun _ ⟨x, eq⟩ => eq ▸ ε_pos x
  case topology_le =>
    intro _ ⟨x, _, eq⟩
    rw [← eq]
    apply toTopologicalSpace_mono <| uniformity_le_uniformSpaceOf x.prop
  case subset =>
    show ⋂ m ∈ D, @Metric.ball _ m x (iInf ε) ⊆ s
    calc
      _ = ⋂ (i : t), @Metric.ball X (PseudoMetricSpaceOf i.val.prop) x (iInf ε) := by
        simp_rw [Set.biInter_image, Set.iInter_subtype]
      _ ⊆ ⋂ (i : t), @Metric.ball _ (PseudoMetricSpaceOf i.val.prop) x (ε i) := by
        apply Set.iInter_mono
        intro i
        let _inst := PseudoMetricSpaceOf i.val.prop
        apply Metric.ball_subset
        rw [dist_self, sub_nonneg]
        exact ciInf_le (Finite.bddBelow_range _) _
      _ ⊆ ⋂ (i : t), ball x (f' i) := Set.iInter_mono ball_subset'
      _ ⊆ ⋂ (i : t), ball x (f i) := by
        refine Set.iInter_mono fun i => ball_mono ?subset x
        let _inst := (UniformSpaceOf i.val.prop).toTopologicalSpace
        exact interior_subset
      _ = ball x (⋂ (i : t), f i) := ball_iInter.symm
      _ ⊆ s := ball_subset

end PseudoMetrics

instance completelyRegularSpace : CompletelyRegularSpace X := by
  rw [completelyRegularSpace_iff]
  intro x K hK hx
  have hK' := hK.isOpen_compl
  rw [← Set.mem_compl_iff] at hx
  have ⟨t, t_finite, coarser, ε, ε_pos, subset⟩ :=
    UniformSpace.exists_pseudoMetricSpace_family_of_isOpen hK' hx
  let ⟨finset, eq⟩ := t_finite.exists_finset_coe

  by_cases finset_ne : finset.Nonempty; swap
  {
    -- If `t` is empty, then `K = X`, so a constant function suffices.
    rw [Finset.not_nonempty_iff_eq_empty] at finset_ne
    rw [finset_ne, Finset.coe_empty] at eq
    simp only [← eq, Set.mem_empty_iff_false, Set.iInter_of_empty, Set.iInter_univ,
      Set.univ_subset_iff, Set.compl_univ_iff] at subset
    rw [subset]
    exact ⟨fun _ => 0, continuous_const, rfl, Set.eqOn_empty _ _⟩
  }

  -- f is a continuous function that maps `x` to `0` and points inside of `K` to values `≥ ε`
  let f := fun y : X => finset.sup' finset_ne fun m => m.dist x y
  have f_cont : Continuous f := by
    apply Continuous.finset_sup'_apply finset_ne
    intro m mem
    apply Continuous.dist <| @continuous_const _ _ _ m.toUniformSpace.toTopologicalSpace _

    show Continuous[unf.toTopologicalSpace, m.toUniformSpace.toTopologicalSpace] id
    rw [continuous_id_iff_le]
    simp only [← eq, Finset.mem_coe] at coarser
    exact coarser m mem

  have f_ge : ∀ y ∈ K, ε ≤ f y := by
    intro y yK
    simp_rw [Set.subset_compl_comm, Set.compl_iInter] at subset
    apply subset at yK
    simp_rw [Set.mem_iUnion, Set.mem_compl_iff, ← eq, Finset.mem_coe, Metric.mem_ball] at yK
    let ⟨m, m_in_t, y_notin_ball⟩ := yK
    rw [← swap_dist] at y_notin_ball
    exact (Finset.le_sup'_iff _).mpr ⟨m, m_in_t, by simpa using y_notin_ball⟩

  have f_pos : ∀ y, 0 ≤ f y := fun y =>
    let ⟨m, m_in_finset⟩ := finset_ne
    (Finset.le_sup'_iff _).mpr ⟨m, m_in_finset, dist_nonneg⟩

  -- We obtain our target function by clamping `f` to `ε` and dividing it by `ε`.
  refine ⟨fun y : X => ⟨(f y ⊓ ε) / ε, unitInterval.div_mem
      (le_inf_iff.mpr ⟨f_pos y, ε_pos.le⟩)
      ε_pos.le
      inf_le_right⟩,
    Continuous.subtype_mk (Continuous.div_const (Continuous.inf f_cont continuous_const) _) _,
    ?eq_zero,
    ?eqOn_one⟩

  case eq_zero =>
    rw [Subtype.mk.injEq]
    simp only [dist_self, Finset.sup'_const, Set.Icc.coe_zero, div_eq_zero_iff, inf_eq_left]
    left
    exact ε_pos.le
  case eqOn_one =>
    intro y yK
    rw [Subtype.mk.injEq, Pi.one_apply, Set.Icc.coe_one, div_eq_one_iff_eq ε_pos.ne']
    exact inf_eq_right.mpr (f_ge y yK)
