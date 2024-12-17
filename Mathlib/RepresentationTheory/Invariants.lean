/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of
`MonoidAlgebra k G`. The action of this special element gives a projection onto the
subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

suppress_compilation

open MonoidAlgebra

open Representation

namespace GroupAlgebra

variable (k G : Type*) [CommSemiring k] [Group G]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The average of all elements of the group `G`, considered as an element of `MonoidAlgebra k G`.
-/
noncomputable def average : MonoidAlgebra k G :=
  ⅟ (Fintype.card G : k) • ∑ g : G, of k G g

/-- `average k G` is invariant under left multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_left (g : G) : ↑(Finsupp.single g 1) * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    Finset.sum_congr, MonoidAlgebra.single_mul_single]
  set f : G → MonoidAlgebra k G := fun x => Finsupp.single x 1
  show ⅟ (Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟ (Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

/-- `average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_right (g : G) : average k G * ↑(Finsupp.single g 1) = average k G := by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    Finset.sum_congr, MonoidAlgebra.single_mul_single]
  set f : G → MonoidAlgebra k G := fun x => Finsupp.single x 1
  show ⅟ (Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟ (Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

end GroupAlgebra

namespace Representation

section Invariants

open GroupAlgebra

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/-- The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
def invariants : Submodule k V where
  carrier := setOf fun v => ∀ g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, LinearMap.map_smulₛₗ, RingHom.id_apply]

@[simp]
theorem mem_invariants (v : V) : v ∈ invariants ρ ↔ ∀ g : G, ρ g v = v := by rfl

theorem invariants_eq_inter : (invariants ρ).carrier = ⋂ g : G, Function.fixedPoints (ρ g) := by
  ext; simp [Function.IsFixedPt]

theorem invariants_eq_top [ρ.IsTrivial] :
    invariants ρ = ⊤ :=
eq_top_iff.2 (fun x _ g => ρ.apply_eq_self g x)

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
noncomputable def averageMap : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `averageMap` sends elements of `V` to the subspace of invariants.
-/
theorem averageMap_invariant (v : V) : averageMap ρ v ∈ invariants ρ := fun g => by
  rw [averageMap, ← asAlgebraHom_single_one, ← LinearMap.mul_apply, ← map_mul (asAlgebraHom ρ),
    mul_average_left]

/-- The `averageMap` acts as the identity on the subspace of invariants.
-/
theorem averageMap_id (v : V) (hv : v ∈ invariants ρ) : averageMap ρ v = v := by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]

theorem isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap :=
  ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

end Invariants

namespace linHom

universe u

open CategoryTheory Action

section Rep

variable {k : Type u} [CommRing k] {G : Grp.{u}}

theorem mem_invariants_iff_comm {X Y : Rep k G} (f : X.V →ₗ[k] Y.V) (g : G) :
    (linHom X.ρ Y.ρ) g f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f := by
  dsimp
  rw [← LinearMap.comp_assoc, ← ModuleCat.hom_ofHom (Y.ρ g), ← ModuleCat.hom_ofHom f,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_ofHom (X.ρ g⁻¹), ← ModuleCat.hom_comp,
      Rep.ofHom_ρ, ← ρAut_apply_inv X g, Rep.ofHom_ρ, ← ρAut_apply_hom Y g, ← ModuleCat.hom_ext_iff,
      Iso.inv_comp_eq, ρAut_apply_hom, ← ModuleCat.hom_ofHom (X.ρ g),
      ← ModuleCat.hom_comp, ← ModuleCat.hom_ext_iff]
  exact comm

/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
@[simps]
def invariantsEquivRepHom (X Y : Rep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  toFun f := ⟨ModuleCat.ofHom f.val, fun g =>
    ModuleCat.hom_ext ((mem_invariants_iff_comm _ g).1 (f.property g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.hom.hom, fun g =>
    (mem_invariants_iff_comm _ g).2 (ModuleCat.hom_ext_iff.mp (f.comm g))⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

end Rep

section FDRep

variable {k : Type u} [Field k] {G : Grp.{u}}

/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
def invariantsEquivFDRepHom (X Y : FDRep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y := by
  rw [← FDRep.forget₂_ρ, ← FDRep.forget₂_ρ]
  -- Porting note: The original version used `linHom.invariantsEquivRepHom _ _ ≪≫ₗ`
  exact linHom.invariantsEquivRepHom
    ((forget₂ (FDRep k G) (Rep k G)).obj X) ((forget₂ (FDRep k G) (Rep k G)).obj Y) ≪≫ₗ
    FDRep.forget₂HomLinearEquiv X Y

end FDRep

end linHom

end Representation
