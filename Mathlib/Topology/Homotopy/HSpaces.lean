/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Junyan Xu
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Path

/-!
# H-spaces

This file defines H-spaces mainly following the approach proposed by Serre in his paper
*Homologie singulière des espaces fibrés*. The idea beneath `H-spaces` is that they are topological
spaces with a binary operation `⋀ : X → X → X` that is a homotopic-theoretic weakening of an
operation what would make `X` into a topological monoid.
In particular, there exists a "neutral element" `e : X` such that `fun x ↦e ⋀ x` and
`fun x ↦ x ⋀ e` are homotopic to the identity on `X`, see
[the Wikipedia page of H-spaces](https://en.wikipedia.org/wiki/H-space).

Some notable properties of `H-spaces` are
* Their fundamental group is always abelian (by the same argument for topological groups);
* Their cohomology ring comes equipped with a structure of a Hopf-algebra;
* The loop space based at every `x : X` carries a structure of an `H-spaces`.

## Main Results

* Every topological group `G` is an `H-space` using its operation `* : G → G → G` (this is already
  true if `G` has an instance of a `MulOneClass` and `ContinuousMul`);
* Given two `H-spaces` `X` and `Y`, their product is again an `H`-space. We show in an example that
  starting with two topological groups `G, G'`, the `H`-space structure on `G × G'` is
  definitionally equal to the product of `H-space` structures on `G` and `G'`.
* The loop space based at every `x : X` carries a structure of an `H-spaces`.

## To Do
* Prove that for every `NormedAddTorsor Z` and every `z : Z`, the operation
`fun x y ↦ midpoint x y` defines an `H-space` structure with `z` as a "neutral element".
* Prove that `S^0`, `S^1`, `S^3` and `S^7` are the unique spheres that are `H-spaces`, where the
  first three inherit the structure because they are topological groups (they are Lie groups,
  actually), isomorphic to the invertible elements in `ℤ`, in `ℂ` and in the quaternion; and the
  fourth from the fact that `S^7` coincides with the octonions of norm 1 (it is not a group, in
  particular, only has an instance of `MulOneClass`).

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
  hmul_e_e : hmul (e, e) = e
  eHmul :
    (hmul.comp <| (const X e).prodMk <| ContinuousMap.id X).HomotopyRel (ContinuousMap.id X) {e}
  hmulE :
    (hmul.comp <| (ContinuousMap.id X).prodMk <| const X e).HomotopyRel (ContinuousMap.id X) {e}

/-- The binary operation `hmul` on an `H`-space -/
scoped[HSpaces] notation x "⋀" y => HSpace.hmul (x, y)

open HSpaces

instance HSpace.prod (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] [HSpace X]
    [HSpace Y] : HSpace (X × Y) where
  hmul := ⟨fun p => (p.1.1 ⋀ p.2.1, p.1.2 ⋀ p.2.2), by fun_prop⟩
  e := (HSpace.e, HSpace.e)
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk, Prod.mk_inj]
    exact ⟨HSpace.hmul_e_e, HSpace.hmul_e_e⟩
  eHmul := by
    let G : I × X × Y → X × Y := fun p => (HSpace.eHmul (p.1, p.2.1), HSpace.eHmul (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.2 x) (HSpace.eHmul.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.3 x) (HSpace.eHmul.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.eHmul.2 t x h.1) (HSpace.eHmul.2 t y h.2)
  hmulE := by
    let G : I × X × Y → X × Y := fun p => (HSpace.hmulE (p.1, p.2.1), HSpace.hmulE (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.2 x) (HSpace.hmulE.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.3 x) (HSpace.hmulE.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.hmulE.2 t x h.1) (HSpace.hmulE.2 t y h.2)


namespace IsTopologicalGroup

/-- The definition `toHSpace` is not an instance because its additive version would
lead to a diamond since a topological field would inherit two `HSpace` structures, one from the
`MulOneClass` and one from the `AddZeroClass`. In the case of a group, we make
`IsTopologicalGroup.hSpace` an instance." -/
@[to_additive
      "The definition `toHSpace` is not an instance because it comes together with a
      multiplicative version which would lead to a diamond since a topological field would inherit
      two `HSpace` structures, one from the `MulOneClass` and one from the `AddZeroClass`.
      In the case of an additive group, we make `IsTopologicalAddGroup.hSpace` an instance."]
def toHSpace (M : Type u) [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] : HSpace M where
  hmul := ⟨Function.uncurry Mul.mul, continuous_mul⟩
  e := 1
  hmul_e_e := one_mul 1
  eHmul := (HomotopyRel.refl _ _).cast rfl (by ext1; apply one_mul)
  hmulE := (HomotopyRel.refl _ _).cast rfl (by ext1; apply mul_one)

@[to_additive]
instance (priority := 600) hSpace (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : HSpace G :=
  toHSpace G

theorem one_eq_hSpace_e {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    (1 : G) = HSpace.e :=
  rfl

/- In the following example we see that the H-space structure on the product of two topological
groups is definitionally equally to the product H-space-structure of the two groups. -/
example {G G' : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace G']
    [Group G'] [IsTopologicalGroup G'] : IsTopologicalGroup.hSpace (G × G') = HSpace.prod G G' := by
  simp only [HSpace.prod]
  rfl


end IsTopologicalGroup

namespace unitInterval

/-- `qRight` is analogous to the function `Q` defined on p. 475 of [serre1951] that helps proving
continuity of `delayReflRight`. -/
def qRight (p : I × I) : I :=
  Set.projIcc 0 1 zero_le_one (2 * p.1 / (1 + p.2))

@[fun_prop]
theorem continuous_qRight : Continuous qRight :=
  continuous_projIcc.comp <|
    Continuous.div (by fun_prop) (by fun_prop) fun _ ↦ (add_pos zero_lt_one).ne'

theorem qRight_zero_left (θ : I) : qRight (0, θ) = 0 :=
  Set.projIcc_of_le_left _ <| by simp only [coe_zero, mul_zero, zero_div, le_refl]

theorem qRight_one_left (θ : I) : qRight (1, θ) = 1 :=
  Set.projIcc_of_right_le _ <|
    (le_div_iff₀ <| add_pos zero_lt_one).2 <| by
      dsimp only
      rw [coe_one, one_mul, mul_one, add_comm, ← one_add_one_eq_two]
      simp only [add_le_add_iff_right]
      exact le_one _

theorem qRight_zero_right (t : I) :
    (qRight (t, 0) : ℝ) = if (t : ℝ) ≤ 1 / 2 then (2 : ℝ) * t else 1 := by
  simp only [qRight, coe_zero, add_zero, div_one]
  split_ifs
  · rw [Set.projIcc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _)]
    refine ⟨t.2.1, ?_⟩
    tauto
  · rw [(Set.projIcc_eq_right _).2]
    · linarith
    · exact zero_lt_one

theorem qRight_one_right (t : I) : qRight (t, 1) = t :=
  Eq.trans (by rw [qRight]; norm_num) <| Set.projIcc_val zero_le_one _

end unitInterval

namespace Path

open unitInterval

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- This is the function analogous to the one on p. 475 of [serre1951], defining a homotopy from
the product path `γ ∧ e` to `γ`. -/
def delayReflRight (θ : I) (γ : Path x y) : Path x y where
  toFun t := γ (qRight (t, θ))
  continuous_toFun := by fun_prop
  source' := by
    rw [qRight_zero_left, γ.source]
  target' := by
    rw [qRight_one_left, γ.target]

theorem continuous_delayReflRight : Continuous fun p : I × Path x y => delayReflRight p.1 p.2 :=
  continuous_uncurry_iff.mp <|
    (continuous_snd.comp continuous_fst).eval <|
      continuous_qRight.comp <| continuous_snd.prodMk <| continuous_fst.comp continuous_fst

theorem delayReflRight_zero (γ : Path x y) : delayReflRight 0 γ = γ.trans (Path.refl y) := by
  ext t
  simp only [delayReflRight, trans_apply, refl_extend, Path.coe_mk_mk, Function.comp_apply,
    refl_apply]
  split_ifs with h; swap
  on_goal 1 => conv_rhs => rw [← γ.target]
  all_goals apply congr_arg γ; ext1; rw [qRight_zero_right]
  exacts [if_neg h, if_pos h]

theorem delayReflRight_one (γ : Path x y) : delayReflRight 1 γ = γ := by
  ext t
  exact congr_arg γ (qRight_one_right t)

/-- This is the function on p. 475 of [serre1951], defining a homotopy from a path `γ` to the
product path `e ∧ γ`. -/
def delayReflLeft (θ : I) (γ : Path x y) : Path x y :=
  (delayReflRight θ γ.symm).symm

theorem continuous_delayReflLeft : Continuous fun p : I × Path x y => delayReflLeft p.1 p.2 :=
  Path.continuous_symm.comp <|
    continuous_delayReflRight.comp <|
      continuous_fst.prodMk <| Path.continuous_symm.comp continuous_snd

theorem delayReflLeft_zero (γ : Path x y) : delayReflLeft 0 γ = (Path.refl x).trans γ := by
  simp only [delayReflLeft, delayReflRight_zero, trans_symm, refl_symm, Path.symm_symm]

theorem delayReflLeft_one (γ : Path x y) : delayReflLeft 1 γ = γ := by
  simp only [delayReflLeft, delayReflRight_one, Path.symm_symm]

/-- The loop space at x carries a structure of an H-space. Note that the field `eHmul`
(resp. `hmulE`) neither implies nor is implied by `Path.Homotopy.reflTrans`
(resp. `Path.Homotopy.transRefl`).
-/
instance (x : X) : HSpace (Path x x) where
  hmul := ⟨fun ρ => ρ.1.trans ρ.2, continuous_trans⟩
  e := refl x
  hmul_e_e := refl_trans_refl
  eHmul :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x ↦ delayReflLeft p.1 p.2, continuous_delayReflLeft⟩,
          delayReflLeft_zero, delayReflLeft_one⟩
      prop' := by rintro t _ rfl; exact refl_trans_refl.symm }
  hmulE :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x ↦ delayReflRight p.1 p.2, continuous_delayReflRight⟩,
          delayReflRight_zero, delayReflRight_one⟩
      prop' := by rintro t _ rfl; exact refl_trans_refl.symm }

end Path
