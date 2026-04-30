/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.CompactOpen

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

@[expose] public section

open scoped Pointwise

variable (A B C G H : Type*) [Monoid A] [Monoid B] [Monoid C] [CommGroup G] [Group H]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

noncomputable section

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → Circle`. -/
def PontryaginDual :=
  A →ₜ* Circle
deriving TopologicalSpace

instance [LocallyCompactSpace H] : LocallyCompactSpace (PontryaginDual H) := by
  let Vn : ℕ → Set Circle := fun n ↦ Circle.centeredArc (Real.pi / 2 ^ (n + 1))
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < Real.pi / 2 ^ (n + 1) :=
    fun n x ↦ Circle.mem_centeredArc (z := x)
      (div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two))
  refine ContinuousMonoidHom.locallyCompactSpace_of_hasBasis Vn ?_ ?_
  · intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  · rw [← Circle.exp_zero, ← isLocalHomeomorph_circleExp.map_nhds_eq 0]
    refine ((nhds_basis_zero_abs_lt ℝ).to_hasBasis
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
open Real

#adaptation_note /-- nightly-2026-03-31
Without this `set_option` we get a PANIC!
-/
set_option backward.inferInstanceAs.wrap.data false in
instance : CommGroup (PontryaginDual A) := inferInstanceAs (CommGroup (A →ₜ* Circle))

deriving instance
  T2Space, IsTopologicalGroup,
  Inhabited, FunLike, ContinuousMapClass, MonoidHomClass,
  [DiscreteTopology A] → CompactSpace _
for PontryaginDual A

/-- A discrete monoid has compact Pontryagin dual. -/
add_decl_doc instLocallyCompactSpacePontryaginDual

/-- A compact monoid has discrete Pontryagin dual. -/
instance [CompactSpace A] : DiscreteTopology (PontryaginDual A) := by
  let V : Set (PontryaginDual A) := {ψ | Set.MapsTo ψ Set.univ (Circle.centeredArc (π / 2))}
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact isOpen_induced (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ
      (Circle.isOpen_centeredArc (π / 2)))
  have hVeq : V = ({1} : Set (PontryaginDual A)) := by
    ext ψ
    refine ⟨fun hψ ↦ ?_, fun hψ ↦ ?_⟩
    · rw [Set.mem_singleton_iff]
      apply ContinuousMonoidHom.ext
      intro a
      refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n hn ↦ ?_
      simpa [map_pow] using hψ (Set.mem_univ (a ^ n))
    · rw [Set.mem_singleton_iff] at hψ
      subst ψ
      intro _ _
      change (1 : Circle) ∈ Circle.centeredArc (π / 2)
      rw [Circle.mem_centeredArc (by linarith [pi_pos])]
      simp [pi_pos]
  exact discreteTopology_of_isOpen_singleton_one (by simpa [hVeq] using hVopen)

instance [DiscreteTopology A] [CompactSpace A] : Finite (PontryaginDual A) :=
  finite_of_compact_of_discrete

noncomputable instance [DiscreteTopology A] [CompactSpace A] : Fintype (PontryaginDual A) :=
  .ofFinite _

/-- `PontryaginDual` is a contravariant functor. -/
def map (f : A →ₜ* B) :
    (PontryaginDual B) →ₜ* (PontryaginDual A) :=
  f.compLeft Circle

@[simp]
theorem map_apply (f : A →ₜ* B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl

@[simp]
theorem map_one : map (1 : A →ₜ* B) = 1 :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)

@[simp]
theorem map_comp (g : B →ₜ* C) (f : A →ₜ* B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl

@[simp]
nonrec theorem map_mul (f g : A →ₜ* G) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)

variable (A B C G)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
def mapHom [LocallyCompactSpace G] :
    (A →ₜ* G) →ₜ* ((PontryaginDual G) →ₜ* (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

end PontryaginDual
