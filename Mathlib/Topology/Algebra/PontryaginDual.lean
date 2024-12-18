/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Pontryagin dual

This file defines the Pontryagin dual of a topological group. The Pontryagin dual of a topological
group `A` is the topological group of continuous homomorphisms `A →* Circle` with the compact-open
topology. For example, `ℤ` and `Circle` are Pontryagin duals of each other. This is an example of
Pontryagin duality, which states that a locally compact abelian topological group is canonically
isomorphic to its double dual.

## Main definitions

* `PontryaginDual A`: The group of continuous homomorphisms `A →* Circle`.
-/

open Pointwise Function

variable (A B C G H : Type*) [Monoid A] [Monoid B] [Monoid C] [CommGroup G] [Group H]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalGroup G] [TopologicalGroup H]

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → Circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A Circle

-- Porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A Circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A Circle))

-- Porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A Circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A Circle))

-- Porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A Circle))

instance [LocallyCompactSpace H] : LocallyCompactSpace (PontryaginDual H) := by
  let Vn : ℕ → Set Circle :=
    fun n ↦ Circle.exp '' { x | |x| < Real.pi / 2 ^ (n + 1)}
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < Real.pi / 2 ^ (n + 1) := by
    refine fun n x ↦ ⟨?_, fun hx ↦ ⟨Complex.arg x, hx, Circle.exp_arg x⟩⟩
    rintro ⟨t, ht : |t| < _, rfl⟩
    have ht' := ht.trans_le (div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two))
    rwa [Circle.arg_exp (neg_lt_of_abs_lt ht') (lt_of_abs_lt ht').le]
  refine ContinuousMonoidHom.locallyCompactSpace_of_hasBasis Vn ?_ ?_
  · intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    exact h1.trans_le
      (div_le_div_of_nonneg_left Real.pi_nonneg two_pos (le_self_pow₀ one_le_two n.succ_ne_zero))
  · rw [← Circle.exp_zero, ← isLocalHomeomorph_circleExp.map_nhds_eq 0]
    refine ((nhds_basis_zero_abs_sub_lt ℝ).to_hasBasis
        (fun x hx ↦ ⟨Nat.ceil (Real.pi / x), trivial, fun t ht ↦ ?_⟩)
          fun k _ ↦ ⟨Real.pi / 2 ^ (k + 1), by positivity, le_rfl⟩).map Circle.exp
    rw [Set.mem_setOf_eq] at ht ⊢
    refine lt_of_lt_of_le ht ?_
    rw [div_le_iff₀' (pow_pos two_pos _), ← div_le_iff₀ hx]
    refine (Nat.le_ceil (Real.pi / x)).trans ?_
    exact_mod_cast (Nat.le_succ _).trans Nat.lt_two_pow_self.le

variable {A B C G}

namespace PontryaginDual

open ContinuousMonoidHom

instance : FunLike (PontryaginDual A) A Circle :=
  ContinuousMonoidHom.instFunLike

noncomputable instance instContinuousMapClass : ContinuousMapClass (PontryaginDual A) A Circle :=
  ContinuousMonoidHom.instContinuousMapClass

noncomputable instance instMonoidHomClass : MonoidHomClass (PontryaginDual A) A Circle :=
  ContinuousMonoidHom.instMonoidHomClass

/-- `PontryaginDual` is a contravariant functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft Circle

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl

@[simp]
nonrec theorem map_mul (f g : ContinuousMonoidHom A G) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)

variable (A B C G)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
noncomputable def mapHom [LocallyCompactSpace G] :
    ContinuousMonoidHom (ContinuousMonoidHom A G)
      (ContinuousMonoidHom (PontryaginDual G) (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

end PontryaginDual
