/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam

! This file was ported from Lean 3 source module algebraic_topology.fundamental_groupoid.basic
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Groupoid
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.Homotopy.Path

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

/-- Auxilliary function for `refl_trans_symm` -/
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)
#align path.homotopy.refl_trans_symm_aux Path.Homotopy.reflTransSymmAux

@[continuity]
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux :=
  by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _
  · continuity
  · continuity
  · continuity
  · continuity
  intro x hx
  norm_num [hx, mul_assoc]
#align path.homotopy.continuous_refl_trans_symm_aux Path.Homotopy.continuous_reflTransSymmAux

theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I :=
  by
  dsimp only [refl_trans_symm_aux]
  split_ifs
  · constructor
    · apply mul_nonneg
      · apply mul_nonneg
        · unit_interval
        · norm_num
      · unit_interval
    · rw [mul_assoc]
      apply mul_le_one
      · unit_interval
      · apply mul_nonneg
        · norm_num
        · unit_interval
      · linarith
  · constructor
    · apply mul_nonneg
      · unit_interval
      linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
    · apply mul_le_one
      · unit_interval
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
#align path.homotopy.refl_trans_symm_aux_mem_I Path.Homotopy.reflTransSymmAux_mem_I

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm)
    where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by continuity
  map_zero_left' := by norm_num [refl_trans_symm_aux]
  map_one_left' x :=
    by
    dsimp only [refl_trans_symm_aux, Path.coe_toContinuousMap, Path.trans]
    change _ = ite _ _ _
    split_ifs
    · rw [Path.extend, Set.IccExtend_of_mem]
      · norm_num
      · rw [unitInterval.mul_pos_mem_iff zero_lt_two]
        exact ⟨unitInterval.nonneg x, h⟩
    · rw [Path.symm, Path.extend, Set.IccExtend_of_mem]
      · congr 1
        ext
        norm_num [sub_sub_eq_add_sub]
      · rw [unitInterval.two_mul_sub_one_mem_iff]
        exact ⟨(not_le.1 h).le, unitInterval.le_one x⟩
  prop' t x hx := by
    cases hx
    · rw [hx]
      simp [refl_trans_symm_aux]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      norm_num [refl_trans_symm_aux]
#align path.homotopy.refl_trans_symm Path.Homotopy.reflTransSymm

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ Path.symm_symm
#align path.homotopy.refl_symm_trans Path.Homotopy.reflSymmTrans

end

section TransRefl

/-- Auxilliary function for `trans_refl_reparam` -/
def transReflReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2 * t else 1
#align path.homotopy.trans_refl_reparam_aux Path.Homotopy.transReflReparamAux

@[continuity]
theorem continuous_transReflReparamAux : Continuous transReflReparamAux :=
  by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _ <;>
    [continuity, continuity, continuity, continuity, skip]
  intro x hx
  norm_num [hx]
#align path.homotopy.continuous_trans_refl_reparam_aux Path.Homotopy.continuous_transReflReparamAux

theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t ∈ I :=
  by
  unfold trans_refl_reparam_aux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
#align path.homotopy.trans_refl_reparam_aux_mem_I Path.Homotopy.transReflReparamAux_mem_I

theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by norm_num [trans_refl_reparam_aux]
#align path.homotopy.trans_refl_reparam_aux_zero Path.Homotopy.transReflReparamAux_zero

theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by norm_num [trans_refl_reparam_aux]
#align path.homotopy.trans_refl_reparam_aux_one Path.Homotopy.transReflReparamAux_one

theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) :=
  by
  ext
  unfold trans_refl_reparam_aux
  simp only [Path.trans_apply, not_le, coe_to_fun, Function.comp_apply]
  split_ifs
  · rfl
  · simp
#align path.homotopy.trans_refl_reparam Path.Homotopy.trans_refl_reparam

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (path.refl x₁)` to `p`.
-/
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by continuity) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm
#align path.homotopy.trans_refl Path.Homotopy.transRefl

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `(path.refl x₀).trans p` to `p`.
-/
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)
#align path.homotopy.refl_trans Path.Homotopy.reflTrans

end TransRefl

section Assoc

/-- Auxilliary function for `trans_assoc_reparam`. -/
def transAssocReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2 * t else if (t : ℝ) ≤ 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)
#align path.homotopy.trans_assoc_reparam_aux Path.Homotopy.transAssocReparamAux

@[continuity]
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux := by
  refine'
        continuous_if_le _ _ (Continuous.continuousOn _)
          (continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _)
              _).ContinuousOn
          _ <;>
      [continuity, continuity, continuity, continuity, continuity, continuity, continuity, skip,
      skip] <;>
    · intro x hx
      norm_num [hx]
#align path.homotopy.continuous_trans_assoc_reparam_aux Path.Homotopy.continuous_transAssocReparamAux

theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t ∈ I :=
  by
  unfold trans_assoc_reparam_aux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
#align path.homotopy.trans_assoc_reparam_aux_mem_I Path.Homotopy.transAssocReparamAux_mem_I

theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [trans_assoc_reparam_aux]
#align path.homotopy.trans_assoc_reparam_aux_zero Path.Homotopy.transAssocReparamAux_zero

theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [trans_assoc_reparam_aux]
#align path.homotopy.trans_assoc_reparam_aux_one Path.Homotopy.transAssocReparamAux_one

theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) :=
  by
  ext
  simp only [trans_assoc_reparam_aux, Path.trans_apply, mul_inv_cancel_left₀, not_le,
    Function.comp_apply, Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, mul_ite, Subtype.coe_mk,
    Path.coe_reparam]
  -- TODO: why does split_ifs not reduce the ifs??????
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · simp [h₂, h₃, -one_div]
  · exfalso
    linarith
  · exfalso
    linarith
  · have h : ¬(x : ℝ) + 1 / 4 ≤ 1 / 2 := by linarith
    have h' : 2 * ((x : ℝ) + 1 / 4) - 1 ≤ 1 / 2 := by linarith
    have h'' : 2 * (2 * (x : ℝ)) - 1 = 2 * (2 * (↑x + 1 / 4) - 1) := by linarith
    simp only [h₄, h₁, h, h', h'', dif_neg (show ¬False from id), dif_pos True.intro, if_false,
      if_true]
  · exfalso
    linarith
  · have h : ¬(1 / 2 : ℝ) * (x + 1) ≤ 1 / 2 := by linarith
    have h' : ¬2 * ((1 / 2 : ℝ) * (x + 1)) - 1 ≤ 1 / 2 := by linarith
    simp only [h₁, h₅, h, h', if_false, dif_neg (show ¬False from id)]
    congr
    ring
#align path.homotopy.trans_assoc_reparam Path.Homotopy.trans_assoc_reparam

/-- For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`.
-/
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm
#align path.homotopy.trans_assoc Path.Homotopy.transAssoc

end Assoc

end Homotopy

end Path

/--
The fundamental groupoid of a space `X` is defined to be a type synonym for `X`, and we subsequently
put a `category_theory.groupoid` structure on it.
-/
def FundamentalGroupoid (X : Type u) :=
  X
#align fundamental_groupoid FundamentalGroupoid

namespace FundamentalGroupoid

instance {X : Type u} [h : Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  h

attribute [local reducible] FundamentalGroupoid

attribute [local instance] Path.Homotopic.setoid

instance : CategoryTheory.Groupoid (FundamentalGroupoid X)
    where
  Hom x y := Path.Homotopic.Quotient x y
  id x := ⟦Path.refl x⟧
  comp x y z := Path.Homotopic.Quotient.comp
  id_comp' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Path.refl x).trans a⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.reflTrans a⟩
  comp_id' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Path.refl y)⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.transRefl a⟩
  assoc' w x y z f g h :=
    Quotient.induction_on₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound ⟨Path.Homotopy.transAssoc p q r⟩
  inv x y p :=
    Quotient.lift (fun l : Path x y => ⟦l.symm⟧)
      (by
        rintro a b ⟨h⟩
        rw [Quotient.eq']
        exact ⟨h.symm₂⟩)
      p
  inv_comp' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.symm.trans a⟧ = ⟦Path.refl y⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflSymmTrans a).symm⟩
  comp_inv' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans a.symm⟧ = ⟦Path.refl x⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflTransSymm a).symm⟩

theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.comp q :=
  rfl
#align fundamental_groupoid.comp_eq FundamentalGroupoid.comp_eq

theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x⟧ :=
  rfl
#align fundamental_groupoid.id_eq_path_refl FundamentalGroupoid.id_eq_path_refl

/-- The functor sending a topological space `X` to its fundamental groupoid.
-/
def fundamentalGroupoidFunctor : TopCat ⥤ CategoryTheory.Grpd
    where
  obj X := { α := FundamentalGroupoid X }
  map X Y f :=
    { obj := f
      map := fun x y p => p.mapFn f
      map_id' := fun X => rfl
      map_comp' := fun x y z p q =>
        Quotient.induction_on₂ p q fun a b => by
          simp [comp_eq, ← Path.Homotopic.map_lift, ← Path.Homotopic.comp_lift] }
  map_id' := by
    intro X
    change _ = (⟨_, _, _, _⟩ : FundamentalGroupoid X ⥤ FundamentalGroupoid X)
    congr
    ext (x y p)
    refine' Quotient.inductionOn p fun q => _
    rw [← Path.Homotopic.map_lift]
    conv_rhs => rw [← q.map_id]
    rfl
  map_comp' := by
    intro X Y Z f g
    congr
    ext (x y p)
    refine' Quotient.inductionOn p fun q => _
    simp only [Quotient.map_mk, Path.map_map, Quotient.eq']
    rfl
#align fundamental_groupoid.fundamental_groupoid_functor FundamentalGroupoid.fundamentalGroupoidFunctor

-- mathport name: fundamental_groupoid_functor
scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

-- mathport name: fundamental_groupoid_functor.obj
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj

-- mathport name: fundamental_groupoid_functor.map
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map

theorem map_eq {X Y : TopCat} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ f).map p = p.mapFn f :=
  rfl
#align fundamental_groupoid.map_eq FundamentalGroupoid.map_eq

/-- Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space. -/
@[reducible]
def toTop {X : TopCat} (x : πₓ X) : X :=
  x
#align fundamental_groupoid.to_top FundamentalGroupoid.toTop

/-- Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space -/
@[reducible]
def fromTop {X : TopCat} (x : X) : πₓ X :=
  x
#align fundamental_groupoid.from_top FundamentalGroupoid.fromTop

/-- Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `path.homotopic.quotient`). -/
@[reducible]
def toPath {X : TopCat} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) : Path.Homotopic.Quotient x₀ x₁ :=
  p
#align fundamental_groupoid.to_path FundamentalGroupoid.toPath

/-- Help the typechecker by convering a path in a topological space to an arrow in the
fundamental groupoid of that space. -/
@[reducible]
def fromPath {X : TopCat} {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) : x₀ ⟶ x₁ :=
  p
#align fundamental_groupoid.from_path FundamentalGroupoid.fromPath

end FundamentalGroupoid

