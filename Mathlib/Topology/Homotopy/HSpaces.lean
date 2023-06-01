/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Junyan Xu

! This file was ported from Lean 3 source module topology.homotopy.H_spaces
! leanprover-community/mathlib commit 729d23f9e1640e1687141be89b106d3c8f9d10c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.CompactOpen
import Mathbin.Topology.Homotopy.Path

/-!
# H-spaces

This file defines H-spaces mainly following the approach proposed by Serre in his paper
*Homologie singulière des espaces fibrés*. The idea beaneath `H-spaces` is that they are topological
spaces with a binary operation `⋀ : X → X → X` that is a homotopic-theoretic weakening of an
operation what would make `X` into a topological monoid. In particular, there exists a "neutral
element" `e : X` such that `λ x, e ⋀ x` and `λ x, x ⋀ e` are homotopic to the identity on `X`, see
[the Wikipedia page of H-spaces](https://en.wikipedia.org/wiki/H-space).

Some notable properties of `H-spaces` are
* Their fundamental group is always abelian (by the same argument for topological groups);
* Their cohomology ring comes equipped with a structure of a Hopf-algebra;
* The loop space based at every `x : X` carries a structure of an `H-spaces`.

## Main Results

* Every topological group `G` is an `H-space` using its operation `* : G → G → G` (this is already
true if `G` has an instance of a `mul_one_class` and `continuous_mul`);
* Given two `H-spaces` `X` and `Y`, their product is again an `H`-space. We show in an example that
starting with two topological groups `G, G'`, the `H`-space structure on `G × G'` is definitionally
equal to the product of `H-space` structures on `G` and `G'`.
* The loop space based at every `x : X` carries a structure of an `H-spaces`.

## To Do
* Prove that for every `normed_add_torsor Z` and every `z : Z`, the operation
`λ x y, midpoint x y` defines a `H-space` structure with `z` as a "neutral element".
* Prove that `S^0`, `S^1`, `S^3` and `S^7` are the unique spheres that are `H-spaces`, where the
first three inherit the structure because they are topological groups (they are Lie groups,
actually), isomorphic to the invertible elements in `ℤ`, in `ℂ` and in the quaternion; and the
fourth from the fact that `S^7` coincides with the octonions of norm 1 (it is not a group, in
particular, only has an instance of `mul_one_class`).

## References

* [J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*,
  Ann. of Math (2) 1951, 54, 425–505][serre1951]
-/


universe u v

noncomputable section

open scoped unitInterval

open Path ContinuousMap Set.Icc TopologicalSpace

/-- A topological space `X` is an H-space if it behaves like a (potentially non-associative)
topological group, but where the axioms for a group only hold up to homotopy.
-/
class HSpace (X : Type u) [TopologicalSpace X] where
  hmul : C(X × X, X)
  e : X
  hmul_e_e : Hmul (e, e) = e
  eHmul :
    (Hmul.comp <| (const X e).prod_mk <| ContinuousMap.id X).HomotopyRel (ContinuousMap.id X) {e}
  hmulE :
    (Hmul.comp <| (ContinuousMap.id X).prod_mk <| const X e).HomotopyRel (ContinuousMap.id X) {e}
#align H_space HSpace

-- mathport name: H_space.Hmul
-- We use the notation `⋀`, typeset as \And, to denote the binary operation `Hmul` on a H-space
scoped[HSpaces] notation x "⋀" y => HSpace.hmul (x, y)

instance HSpace.prod (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] [HSpace X]
    [HSpace Y] : HSpace (X × Y)
    where
  hmul := ⟨fun p => (p.1.1⋀p.2.1, p.1.2⋀p.2.2), by continuity⟩
  e := (HSpace.e, HSpace.e)
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk, Prod.mk.inj_iff]
    exact ⟨HSpace.hmul_e_e, HSpace.hmul_e_e⟩
  eHmul :=
    by
    let G : I × X × Y → X × Y := fun p => (HSpace.eHmul (p.1, p.2.1), HSpace.eHmul (p.1, p.2.2))
    have hG : Continuous G :=
      (Continuous.comp HSpace.eHmul.1.1.2
            (continuous_fst.prod_mk (continuous_fst.comp continuous_snd))).prod_mk
        (Continuous.comp HSpace.eHmul.1.1.2
          (continuous_fst.prod_mk (continuous_snd.comp continuous_snd)))
    use ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exacts[prod.mk.inj_iff.mpr ⟨HSpace.eHmul.1.2 x, HSpace.eHmul.1.2 y⟩]
    · rintro ⟨x, y⟩
      exact prod.mk.inj_iff.mpr ⟨HSpace.eHmul.1.3 x, HSpace.eHmul.1.3 y⟩
    · rintro t ⟨x, y⟩ h
      replace h := prod.mk.inj_iff.mp (set.mem_singleton_iff.mp h)
      exact
        ⟨prod.mk.inj_iff.mpr
            ⟨homotopy_rel.eq_fst HSpace.eHmul t (set.mem_singleton_iff.mpr h.1),
              homotopy_rel.eq_fst HSpace.eHmul t (set.mem_singleton_iff.mpr h.2)⟩,
          prod.mk.inj_iff.mpr ⟨(HSpace.eHmul.2 t x h.1).2, (HSpace.eHmul.2 t y h.2).2⟩⟩
  hmulE :=
    by
    let G : I × X × Y → X × Y := fun p => (HSpace.hmulE (p.1, p.2.1), HSpace.hmulE (p.1, p.2.2))
    have hG : Continuous G :=
      (Continuous.comp HSpace.hmulE.1.1.2
            (continuous_fst.prod_mk (continuous_fst.comp continuous_snd))).prod_mk
        (Continuous.comp HSpace.hmulE.1.1.2
          (continuous_fst.prod_mk (continuous_snd.comp continuous_snd)))
    use ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exacts[prod.mk.inj_iff.mpr ⟨HSpace.hmulE.1.2 x, HSpace.hmulE.1.2 y⟩]
    · rintro ⟨x, y⟩
      exact prod.mk.inj_iff.mpr ⟨HSpace.hmulE.1.3 x, HSpace.hmulE.1.3 y⟩
    · rintro t ⟨x, y⟩ h
      replace h := prod.mk.inj_iff.mp (set.mem_singleton_iff.mp h)
      exact
        ⟨prod.mk.inj_iff.mpr
            ⟨homotopy_rel.eq_fst HSpace.hmulE t (set.mem_singleton_iff.mpr h.1),
              homotopy_rel.eq_fst HSpace.hmulE t (set.mem_singleton_iff.mpr h.2)⟩,
          prod.mk.inj_iff.mpr ⟨(HSpace.hmulE.2 t x h.1).2, (HSpace.hmulE.2 t y h.2).2⟩⟩
#align H_space.prod HSpace.prod

namespace TopologicalGroup

/-- The definition `to_H_space` is not an instance because its `@additive` version would
lead to a diamond since a topological field would inherit two `H_space` structures, one from the
`mul_one_class` and one from the `add_zero_class`. In the case of a group, we make
`topological_group.H_space` an instance."-/
@[to_additive
      "The definition `to_H_space` is not an instance because it comes together with a\nmultiplicative version which would lead to a diamond since a topological field would inherit two\n`H_space` structures, one from the `mul_one_class` and one from the `add_zero_class`. In the case\nof an additive group, we make `topological_group.H_space` an instance."]
def toHSpace (M : Type u) [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] : HSpace M
    where
  hmul := ⟨Function.uncurry Mul.mul, continuous_mul⟩
  e := 1
  hmul_e_e := one_mul 1
  eHmul := (HomotopyRel.refl _ _).cast rfl (by ext1; apply one_mul)
  hmulE := (HomotopyRel.refl _ _).cast rfl (by ext1; apply mul_one)
#align topological_group.to_H_space TopologicalGroup.toHSpace
#align topological_add_group.to_H_space TopologicalAddGroup.to_H_space

@[to_additive]
instance (priority := 600) hSpace (G : Type u) [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    HSpace G :=
  toHSpace G
#align topological_group.H_space TopologicalGroup.hSpace
#align topological_add_group.H_space TopologicalAddGroup.H_space

theorem one_eq_hSpace_e {G : Type u} [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    (1 : G) = HSpace.e :=
  rfl
#align topological_group.one_eq_H_space_e TopologicalGroup.one_eq_hSpace_e

/- In the following example we see that the `H-space` structure on the product of two topological
groups is definitionally equally to the product `H-space`-structure of the two groups.-/
example {G G' : Type u} [TopologicalSpace G] [Group G] [TopologicalGroup G] [TopologicalSpace G']
    [Group G'] [TopologicalGroup G'] : toHSpace (G × G') = HSpace.prod G G' :=
  rfl

end TopologicalGroup

namespace unitInterval

/-- `Q_right` is analogous to the function `Q` defined on p. 475 of [serre1951] that helps proving
continuity of `delay_refl_right`.-/
def qRight (p : I × I) : I :=
  Set.projIcc 0 1 zero_le_one (2 * p.1 / (1 + p.2))
#align unit_interval.Q_right unitInterval.qRight

theorem continuous_qRight : Continuous qRight :=
  continuous_projIcc.comp <|
    Continuous.div (by continuity) (by continuity) fun x => (add_pos zero_lt_one).ne'
#align unit_interval.continuous_Q_right unitInterval.continuous_qRight

theorem qRight_zero_left (θ : I) : qRight (0, θ) = 0 :=
  Set.projIcc_of_le_left _ <| by simp only [coe_zero, MulZeroClass.mul_zero, zero_div]
#align unit_interval.Q_right_zero_left unitInterval.qRight_zero_left

theorem qRight_one_left (θ : I) : qRight (1, θ) = 1 :=
  Set.projIcc_of_right_le _ <|
    (le_div_iff <| add_pos zero_lt_one).2 <| by dsimp only; rw [coe_one, one_mul, mul_one];
      apply add_le_add_left (le_one _)
#align unit_interval.Q_right_one_left unitInterval.qRight_one_left

theorem qRight_zero_right (t : I) : (qRight (t, 0) : ℝ) = if (t : ℝ) ≤ 1 / 2 then 2 * t else 1 :=
  by
  simp only [Q_right, coe_zero, add_zero, div_one]
  split_ifs
  · rw [Set.projIcc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _)]; exacts[rfl, ⟨t.2.1, h⟩]
  · rw [(Set.projIcc_eq_right _).2]; · rfl; · linarith; · exact zero_lt_one
#align unit_interval.Q_right_zero_right unitInterval.qRight_zero_right

theorem qRight_one_right (t : I) : qRight (t, 1) = t :=
  Eq.trans (by rw [Q_right]; congr ; apply mul_div_cancel_left; exact two_ne_zero) <|
    Set.projIcc_val zero_le_one _
#align unit_interval.Q_right_one_right unitInterval.qRight_one_right

end unitInterval

namespace Path

open unitInterval

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- This is the function analogous to the one on p. 475 of [serre1951], defining a homotopy from
the product path `γ ∧ e` to `γ`.-/
def delayReflRight (θ : I) (γ : Path x y) : Path x y
    where
  toFun t := γ (qRight (t, θ))
  continuous_toFun := γ.Continuous.comp (continuous_qRight.comp <| Continuous.Prod.mk_left θ)
  source' := by dsimp only; rw [Q_right_zero_left, γ.source]
  target' := by dsimp only; rw [Q_right_one_left, γ.target]
#align path.delay_refl_right Path.delayReflRight

theorem continuous_delayReflRight : Continuous fun p : I × Path x y => delayReflRight p.1 p.2 :=
  continuous_uncurry_iff.mp <|
    (continuous_snd.comp continuous_fst).path_eval <|
      continuous_qRight.comp <| continuous_snd.prod_mk <| continuous_fst.comp continuous_fst
#align path.continuous_delay_refl_right Path.continuous_delayReflRight

theorem delayReflRight_zero (γ : Path x y) : delayReflRight 0 γ = γ.trans (Path.refl y) :=
  by
  ext t
  simp only [delay_refl_right, trans_apply, refl_extend, Path.coe_mk_mk, Function.comp_apply,
    refl_apply]
  split_ifs; swap; conv_rhs => rw [← γ.target]
  all_goals apply congr_arg γ; ext1; rw [Q_right_zero_right]
  exacts[if_neg h, if_pos h]
#align path.delay_refl_right_zero Path.delayReflRight_zero

theorem delayReflRight_one (γ : Path x y) : delayReflRight 1 γ = γ := by ext t;
  exact congr_arg γ (Q_right_one_right t)
#align path.delay_refl_right_one Path.delayReflRight_one

/-- This is the function on p. 475 of [serre1951], defining a homotopy from a path `γ` to the
product path `e ∧ γ`.-/
def delayReflLeft (θ : I) (γ : Path x y) : Path x y :=
  (delayReflRight θ γ.symm).symm
#align path.delay_refl_left Path.delayReflLeft

theorem continuous_delayReflLeft : Continuous fun p : I × Path x y => delayReflLeft p.1 p.2 :=
  Path.continuous_symm.comp <|
    continuous_delayReflRight.comp <|
      continuous_fst.prod_mk <| Path.continuous_symm.comp continuous_snd
#align path.continuous_delay_refl_left Path.continuous_delayReflLeft

theorem delayReflLeft_zero (γ : Path x y) : delayReflLeft 0 γ = (Path.refl x).trans γ := by
  simp only [delay_refl_left, delay_refl_right_zero, trans_symm, refl_symm, Path.symm_symm]
#align path.delay_refl_left_zero Path.delayReflLeft_zero

theorem delayReflLeft_one (γ : Path x y) : delayReflLeft 1 γ = γ := by
  simp only [delay_refl_left, delay_refl_right_one, Path.symm_symm]
#align path.delay_refl_left_one Path.delayReflLeft_one

/-- The loop space at x carries a structure of a `H-space`. Note that the field `e_Hmul`
(resp. `Hmul_e`) neither implies nor is implied by `path.homotopy.refl_trans`
(resp. `path.homotopy.trans_refl`).
-/
instance (x : X) : HSpace (Path x x)
    where
  hmul := ⟨fun ρ => ρ.1.trans ρ.2, continuous_trans⟩
  e := refl x
  hmul_e_e := refl_trans_refl
  eHmul :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x => delayReflLeft p.1 p.2, continuous_delayReflLeft⟩,
          delayReflLeft_zero, delayReflLeft_one⟩
      prop' := by rintro t _ (rfl : _ = _); exact ⟨refl_trans_refl.symm, rfl⟩ }
  hmulE :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x => delayReflRight p.1 p.2, continuous_delayReflRight⟩,
          delayReflRight_zero, delayReflRight_one⟩
      prop' := by rintro t _ (rfl : _ = _); exact ⟨refl_trans_refl.symm, rfl⟩ }

end Path

