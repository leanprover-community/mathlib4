/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module representation_theory.maschke
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.Algebra.CharP.Invertible
import Mathbin.LinearAlgebra.Basis

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `invertible (fintype.card G : k)`.

We do the core computation in greater generality.
For any `[comm_ring k]` in which  `[invertible (fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes
* These results assume `invertible (fintype.card G : k)` which is equivalent to the more
familiar `¬(ring_char k ∣ fintype.card G)`. It is possible to convert between them using
`invertible_of_ring_char_not_dvd` and `not_ring_char_dvd_of_invertible`.


## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/


universe u

noncomputable section

open Module

open MonoidAlgebra

open BigOperators

section

-- At first we work with any `[comm_ring k]`, and add the assumption that
-- `[invertible (fintype.card G : k)]` when it is required.
variable {k : Type u} [CommRing k] {G : Type u} [Group G]

variable {V : Type u} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]

variable [IsScalarTower k (MonoidAlgebra k G) V]

variable {W : Type u} [AddCommGroup W] [Module k W] [Module (MonoidAlgebra k G) W]

variable [IsScalarTower k (MonoidAlgebra k G) W]

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/


namespace LinearMap

variable (π : W →ₗ[k] V)

include π

/-- We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) : W →ₗ[k] V :=
  ((GroupSmul.linearMap k V g⁻¹).comp π).comp (GroupSmul.linearMap k W g)
#align linear_map.conjugate LinearMap.conjugate

variable (i : V →ₗ[MonoidAlgebra k G] W) (h : ∀ v : V, π (i v) = v)

section

include h

theorem conjugate_i (g : G) (v : V) : (conjugate π g) (i v) = v :=
  by
  dsimp [conjugate]
  simp only [← i.map_smul, h, ← mul_smul, single_mul_single, mul_one, mul_left_inv]
  change (1 : MonoidAlgebra k G) • v = v
  simp
#align linear_map.conjugate_i LinearMap.conjugate_i

end

variable (G) [Fintype G]

/-- The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sumOfConjugates : W →ₗ[k] V :=
  ∑ g : G, π.conjugate g
#align linear_map.sum_of_conjugates LinearMap.sumOfConjugates

/-- In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sumOfConjugatesEquivariant : W →ₗ[MonoidAlgebra k G] V :=
  MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v =>
    by
    simp only [sum_of_conjugates,
      LinearMap.sum_apply,-- We have a `module (monoid_algebra k G)` instance but are working with `finsupp`s,
        -- so help the elaborator unfold everything correctly.
        @Finset.smul_sum
        (MonoidAlgebra k G)]
    dsimp [conjugate]
    conv_lhs =>
      rw [← Finset.univ_map_embedding (mulRightEmbedding g⁻¹)]
      simp only [mulRightEmbedding]
    simp only [← mul_smul, single_mul_single, mul_inv_rev, mul_one, Function.Embedding.coeFn_mk,
      Finset.sum_map, inv_inv, inv_mul_cancel_right]
#align linear_map.sum_of_conjugates_equivariant LinearMap.sumOfConjugatesEquivariant

section

variable [inv : Invertible (Fintype.card G : k)]

include inv

/-- We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariantProjection : W →ₗ[MonoidAlgebra k G] V :=
  ⅟ (Fintype.card G : k) • π.sumOfConjugatesEquivariant G
#align linear_map.equivariant_projection LinearMap.equivariantProjection

include h

theorem equivariantProjection_condition (v : V) : (π.equivariantProjection G) (i v) = v :=
  by
  rw [equivariant_projection, smul_apply, sum_of_conjugates_equivariant,
    equivariant_of_linear_of_comm_apply, sum_of_conjugates]
  rw [LinearMap.sum_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_smul_cast k, ← mul_smul,
    Invertible.invOf_mul_self, one_smul]
#align linear_map.equivariant_projection_condition LinearMap.equivariantProjection_condition

end

end LinearMap

end

namespace CharZero

variable {k : Type u} [Field k] {G : Type u} [Fintype G] [Group G] [CharZero k]

instance : Invertible (Fintype.card G : k) :=
  invertibleOfRingCharNotDvd (by simp [Fintype.card_eq_zero_iff])

end CharZero

namespace MonoidAlgebra

-- Now we work over a `[field k]`.
variable {k : Type u} [Field k] {G : Type u} [Fintype G] [Invertible (Fintype.card G : k)]

variable [Group G]

variable {V : Type u} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]

variable [IsScalarTower k (MonoidAlgebra k G) V]

variable {W : Type u} [AddCommGroup W] [Module k W] [Module (MonoidAlgebra k G) W]

variable [IsScalarTower k (MonoidAlgebra k G) W]

theorem exists_left_inverse_of_injective (f : V →ₗ[MonoidAlgebra k G] W) (hf : f.ker = ⊥) :
    ∃ g : W →ₗ[MonoidAlgebra k G] V, g.comp f = LinearMap.id :=
  by
  obtain ⟨φ, hφ⟩ :=
    (f.restrict_scalars k).exists_leftInverse_of_injective
      (by simp only [hf, Submodule.restrictScalars_bot, LinearMap.ker_restrictScalars])
  refine' ⟨φ.equivariant_projection G, _⟩
  apply LinearMap.ext
  intro v
  simp only [LinearMap.id_coe, id.def, LinearMap.comp_apply]
  apply LinearMap.equivariantProjection_condition
  intro v
  have := congr_arg LinearMap.toFun hφ
  exact congr_fun this v
#align monoid_algebra.exists_left_inverse_of_injective MonoidAlgebra.exists_left_inverse_of_injective

namespace Submodule

theorem exists_isCompl (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  let ⟨f, hf⟩ := MonoidAlgebra.exists_left_inverse_of_injective p.Subtype p.ker_subtype
  ⟨f.ker, LinearMap.isCompl_of_proj <| LinearMap.ext_iff.1 hf⟩
#align monoid_algebra.submodule.exists_is_compl MonoidAlgebra.Submodule.exists_isCompl

/-- This also implies an instance `is_semisimple_module (monoid_algebra k G) V`. -/
instance complementedLattice : ComplementedLattice (Submodule (MonoidAlgebra k G) V) :=
  ⟨exists_isCompl⟩
#align monoid_algebra.submodule.complemented_lattice MonoidAlgebra.Submodule.complementedLattice

end Submodule

end MonoidAlgebra

