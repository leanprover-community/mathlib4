/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Covering

#align_import topology.algebra.continuous_monoid_hom from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Pontryagin dual

This file defines the Pontryagin dual of a topological group. The Pontryagin dual of a topological
group `A` is the topological group of continuous homomorphisms `A →* circle` with the compact-open
topology. For example, `ℤ` and `circle` are Pontryagin duals of each other. This is an example of
Pontryagin duality, which states that a locally compact abelian topological group is canonically
isomorphic to its double dual.

## Main definitions

* `PontryaginDual A`: The group of continuous homomorphisms `A →* circle`.
-/

section ForMathlib

lemma coveringmap : IsLocalHomeomorph expMapCircle := by
  have fund : ∀ x : circle, Complex.arg x = Real.pi ↔ x = expMapCircle Real.pi := by
    rintro ⟨x, hx⟩
    rw [mem_circle_iff_normSq, Complex.normSq_apply] at hx
    rw [Complex.arg_eq_pi_iff, Subtype.ext_iff, expMapCircle_apply, Complex.exp_pi_mul_I,
        Complex.ext_iff, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, neg_zero]
    rw [and_congr_left_iff]
    simp only
    intro hx'
    rw [hx', mul_zero, add_zero, ← sq, sq_eq_one_iff] at hx
    rcases hx with hx | hx <;> rw [hx] <;> norm_num
  let e1 : PartialHomeomorph ℝ circle :=
  { toFun := expMapCircle
    invFun := Complex.arg ∘ Subtype.val
    source := Set.Ioo (-Real.pi) Real.pi
    target := {expMapCircle Real.pi}ᶜ
    map_source' := by
      intro x hx hx'
      rw [Set.mem_singleton_iff] at hx'
      replace hx' := congrArg (Complex.arg ∘ Subtype.val) hx'
      simp only [Function.comp_apply] at hx'
      rw [arg_expMapCircle hx.1 hx.2.le] at hx'
      rw [arg_expMapCircle (neg_lt_self Real.pi_pos) le_rfl] at hx'
      rw [hx'] at hx
      exact lt_irrefl Real.pi hx.2
    map_target' := by
      intro x hx
      have key := Complex.arg_mem_Ioc x
      exact ⟨key.1, lt_of_le_of_ne key.2 (hx ∘ (fund x).mp)⟩
    left_inv' := fun x hx ↦ arg_expMapCircle hx.1 hx.2.le
    right_inv' := fun x _ ↦ expMapCircle_arg x
    open_source := isOpen_Ioo
    open_target := isOpen_compl_singleton
    continuousOn_toFun := Continuous.continuousOn $ by continuity
    continuousOn_invFun := by
      refine' (ContinuousAt.continuousOn fun _ ↦ Complex.continuousAt_arg).comp
        (Continuous.continuousOn $ by continuity) _
      simp only
      intro x hx
      contrapose! hx
      rw [Set.not_mem_compl_iff, Set.mem_singleton_iff, ← fund, Complex.arg_eq_pi_iff]
      rw [Complex.slitPlane, Set.mem_setOf_eq, not_or, not_lt, not_ne_iff] at hx
      refine' ⟨lt_of_le_of_ne hx.1 _, hx.2⟩
      intro hx'
      have hx'' := x.2
      rw [mem_circle_iff_normSq, Complex.normSq_apply, hx', hx.2, mul_zero, add_zero] at hx''
      exact zero_ne_one hx'' }
  intro t
  let e2 : PartialHomeomorph ℝ ℝ :=
  { toFun := fun s ↦ s - t
    invFun := fun s ↦ s + t
    source := Set.Ioo (t - Real.pi) (t + Real.pi)
    target := Set.Ioo (-Real.pi) Real.pi
    map_source' := by
      intro x hx
      rw [Set.mem_Ioo, sub_lt_iff_lt_add'] at hx ⊢
      rwa [neg_lt_sub_iff_lt_add]
    map_target' := by
      intro x hx
      rw [Set.mem_Ioo] at hx ⊢
      rwa [← neg_add_eq_sub, add_lt_add_iff_right, add_comm, add_lt_add_iff_right]
    left_inv' := fun x _ ↦ sub_add_cancel x t
    right_inv' := fun x _ ↦ add_sub_cancel x t
    open_source := isOpen_Ioo
    open_target := isOpen_Ioo
    continuousOn_toFun := Continuous.continuousOn $ by continuity
    continuousOn_invFun := Continuous.continuousOn $ by continuity }
  let e3 : PartialHomeomorph circle circle :=
  { toFun := fun s ↦ s * expMapCircle t
    invFun := fun s ↦ s / expMapCircle t
    source := {expMapCircle Real.pi}ᶜ
    target := {expMapCircle (Real.pi + t)}ᶜ
    map_source' := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      rwa [← eq_div_iff_mul_eq', ← expMapCircle_sub, add_sub_cancel]
    map_target' := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      rwa [div_eq_iff_eq_mul, ← expMapCircle_add]
    left_inv' := fun x _ ↦ mul_div_cancel'' x (expMapCircle t)
    right_inv' := fun x _ ↦ div_mul_cancel' x (expMapCircle t)
    open_source := isOpen_compl_singleton
    open_target := isOpen_compl_singleton
    continuousOn_toFun := Continuous.continuousOn $ by continuity
    continuousOn_invFun := Continuous.continuousOn $ by continuity }
  let e4 : PartialHomeomorph ℝ circle := e2.trans' (e1.trans' e3 rfl) rfl
  refine' ⟨e4, ⟨sub_lt_self t Real.pi_pos, lt_add_of_pos_right t Real.pi_pos⟩, _⟩
  ext x
  simp only [e4, e1, e3, e2]
  simp only [expMapCircle_apply, expMapCircle_add, PartialHomeomorph.trans'_apply,
    PartialHomeomorph.mk_coe, expMapCircle_sub, div_mul_cancel']

instance {X : Type*} [TopologicalSpace X] [Group X] [TopologicalGroup X] [LocallyCompactSpace X] :
    LocallyCompactSpace (ContinuousMonoidHom X circle) := by
  let Vn : ℕ → Set circle :=
    fun n ↦ expMapCircle '' { x | |x| < Real.pi / 2 ^ (n + 1)}
  have hVn : ∀ n x, x ∈ Vn n ↔ 2 ^ (n + 1) * |Complex.arg x| < Real.pi := by
    intro n x
    rw [← lt_div_iff' (pow_pos two_pos (n + 1))]
    refine' ⟨_, fun hx ↦ ⟨Complex.arg x, hx, expMapCircle_arg x⟩⟩
    rintro ⟨t, ht : |t| < _, rfl⟩
    have ht' : |t| < Real.pi :=
      ht.trans (div_lt_self Real.pi_pos (one_lt_pow one_lt_two (Nat.succ_ne_zero _)))
    rw [abs_lt] at ht'
    rwa [arg_expMapCircle ht'.1 ht'.2.le]
  have key0 : Filter.HasBasis (nhds 1) (fun _ ↦ True) Vn := by
    rw [← expMapCircle_zero, ← coveringmap.map_nhds_eq 0]
    refine' Filter.HasBasis.map expMapCircle _
    have key := nhds_basis_zero_abs_sub_lt ℝ
    refine' key.to_hasBasis (fun x hx ↦ _) fun k _ ↦ ⟨Real.pi / 2 ^ (k + 1), by positivity, le_rfl⟩
    refine' ⟨Nat.ceil (Real.pi / x), trivial, fun t ht ↦ _⟩
    rw [Set.mem_setOf_eq] at ht ⊢
    refine' lt_of_lt_of_le ht _
    rw [div_le_iff' (pow_pos two_pos _), ← div_le_iff hx]
    refine' (Nat.le_ceil (Real.pi / x)).trans _
    exact_mod_cast (Nat.le_succ _).trans (Nat.lt_two_pow _).le
  refine' mythm' Vn _ key0
  intro n x h1 h2
  have hx : x.1 ≠ 0 := ne_zero_of_mem_circle x
  rw [hVn] at h1 h2 ⊢
  rwa [Submonoid.coe_mul, Complex.arg_mul hx hx, ← two_mul, abs_mul, abs_two, ← mul_assoc,
    ← pow_succ'] at h2
  clear h2
  rw [← abs_two, pow_succ', mul_assoc, ← abs_mul, abs_two] at h1
  rw [← two_mul]
  apply Set.Ioo_subset_Ioc_self
  rw [Set.mem_Ioo, ← abs_lt]
  refine' lt_of_le_of_lt _ h1
  exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow_of_one_le one_le_two n)

end ForMathlib

open Pointwise Function

variable (A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle
#align pontryagin_dual PontryaginDual

-- Porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A circle))

-- Porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A circle))

-- Porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A circle))

variable {A B C D E}

namespace PontryaginDual

open ContinuousMonoidHom

instance : FunLike (PontryaginDual A) A circle :=
  ContinuousMonoidHom.funLike

noncomputable instance : ContinuousMonoidHomClass (PontryaginDual A) A circle :=
  ContinuousMonoidHom.ContinuousMonoidHomClass

/-- `PontryaginDual` is a contravariant functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft circle
#align pontryagin_dual.map PontryaginDual.map

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl
#align pontryagin_dual.map_apply PontryaginDual.map_apply

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)
#align pontryagin_dual.map_one PontryaginDual.map_one

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl
#align pontryagin_dual.map_comp PontryaginDual.map_comp

@[simp]
nonrec theorem map_mul (f g : ContinuousMonoidHom A E) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)
#align pontryagin_dual.map_mul PontryaginDual.map_mul

variable (A B C D E)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
noncomputable def mapHom [LocallyCompactSpace E] :
    ContinuousMonoidHom (ContinuousMonoidHom A E)
      (ContinuousMonoidHom (PontryaginDual E) (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp
#align pontryagin_dual.map_hom PontryaginDual.mapHom

end PontryaginDual
