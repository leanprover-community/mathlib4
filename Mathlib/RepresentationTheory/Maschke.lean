/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.Basis.VectorSpace

#align_import representation_theory.maschke from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `Invertible (Fintype.card G : k)`.

We do the core computation in greater generality.
For any `[CommRing k]` in which `[Invertible (Fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes
* These results assume `Invertible (Fintype.card G : k)` which is equivalent to the more
familiar `¬(ringChar k ∣ Fintype.card G)`. It is possible to convert between them using
`invertibleOfRingCharNotDvd` and `not_ringChar_dvd_of_invertible`.


## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/


universe u v w

noncomputable section

open Module MonoidAlgebra BigOperators

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/

namespace LinearMap


-- At first we work with any `[CommRing k]`, and add the assumption that
-- `[Invertible (Fintype.card G : k)]` when it is required.
variable {k : Type u} [CommRing k] {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
variable [IsScalarTower k (MonoidAlgebra k G) V]
variable {W : Type w} [AddCommGroup W] [Module k W] [Module (MonoidAlgebra k G) W]
variable [IsScalarTower k (MonoidAlgebra k G) W]

variable (π : W →ₗ[k] V)

/-- We define the conjugate of `π` by `g`, as a `k`-linear map. -/
def conjugate (g : G) : W →ₗ[k] V :=
  .comp (.comp (GroupSmul.linearMap k V g⁻¹) π) (GroupSmul.linearMap k W g)
#align linear_map.conjugate LinearMap.conjugate

theorem conjugate_apply (g : G) (v : W) :
    π.conjugate g v = MonoidAlgebra.single g⁻¹ (1 : k) • π (MonoidAlgebra.single g (1 : k) • v) :=
  rfl

variable (i : V →ₗ[MonoidAlgebra k G] W) (h : ∀ v : V, (π : W → V) (i v) = v)

section

theorem conjugate_i (g : G) (v : V) : (conjugate π g : W → V) (i v) = v := by
  rw [conjugate_apply, ← i.map_smul, h, ← mul_smul, single_mul_single, mul_one, mul_left_inv,
    ← one_def, one_smul]
#align linear_map.conjugate_i LinearMap.conjugate_i

end

variable (G) [Fintype G]

/-- The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sumOfConjugates : W →ₗ[k] V :=
  ∑ g : G, π.conjugate g
#align linear_map.sum_of_conjugates LinearMap.sumOfConjugates

lemma sumOfConjugates_apply (v : W) : π.sumOfConjugates G v = ∑ g : G, π.conjugate g v :=
  LinearMap.sum_apply _ _ _

/-- In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sumOfConjugatesEquivariant : W →ₗ[MonoidAlgebra k G] V :=
  MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v => by
    simp only [sumOfConjugates_apply, Finset.smul_sum, conjugate_apply]
    -- ⊢ ∑ x : G, MonoidAlgebra.single x⁻¹ 1 • ↑π (MonoidAlgebra.single x 1 • MonoidA …
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ fun i ↦ ?_
    -- ⊢ MonoidAlgebra.single i⁻¹ 1 • ↑π (MonoidAlgebra.single i 1 • MonoidAlgebra.si …
    simp only [smul_smul, single_mul_single, mul_inv_rev, mul_inv_cancel_left, one_mul]
    -- 🎉 no goals
#align linear_map.sum_of_conjugates_equivariant LinearMap.sumOfConjugatesEquivariant

theorem sumOfConjugatesEquivariant_apply (v : W) :
    π.sumOfConjugatesEquivariant G v = ∑ g : G, π.conjugate g v :=
  π.sumOfConjugates_apply G v

section

variable [Invertible (Fintype.card G : k)]

/-- We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariantProjection : W →ₗ[MonoidAlgebra k G] V :=
  ⅟(Fintype.card G : k) • π.sumOfConjugatesEquivariant G
#align linear_map.equivariant_projection LinearMap.equivariantProjection

theorem equivariantProjection_apply (v : W) :
    π.equivariantProjection G v = ⅟(Fintype.card G : k) • ∑ g : G, π.conjugate g v := by
  simp only [equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply]
  -- 🎉 no goals

theorem equivariantProjection_condition (v : V) : (π.equivariantProjection G) (i v) = v := by
  rw [equivariantProjection_apply]
  -- ⊢ ⅟↑(Fintype.card G) • ∑ g : G, ↑(conjugate π g) (↑i v) = v
  simp only [conjugate_i π i h]
  -- ⊢ ⅟↑(Fintype.card G) • ∑ x : G, v = v
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_smul_cast k, smul_smul,
    Invertible.invOf_mul_self, one_smul]
#align linear_map.equivariant_projection_condition LinearMap.equivariantProjection_condition

end

end LinearMap

end

namespace MonoidAlgebra

-- Now we work over a `[Field k]`.
variable {k : Type u} [Field k] {G : Type u} [Fintype G] [Invertible (Fintype.card G : k)]
variable [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
variable [IsScalarTower k (MonoidAlgebra k G) V]
variable {W : Type u} [AddCommGroup W] [Module k W] [Module (MonoidAlgebra k G) W]
variable [IsScalarTower k (MonoidAlgebra k G) W]

theorem exists_leftInverse_of_injective (f : V →ₗ[MonoidAlgebra k G] W)
    (hf : LinearMap.ker f = ⊥) :
    ∃ g : W →ₗ[MonoidAlgebra k G] V, g.comp f = LinearMap.id := by
  obtain ⟨φ, hφ⟩ := (f.restrictScalars k).exists_leftInverse_of_injective <| by
    simp only [hf, Submodule.restrictScalars_bot, LinearMap.ker_restrictScalars]
  refine ⟨φ.equivariantProjection G, FunLike.ext _ _ ?_⟩
  -- ⊢ ∀ (x : V), ↑(LinearMap.comp (LinearMap.equivariantProjection G φ) f) x = ↑Li …
  exact φ.equivariantProjection_condition G _ <| FunLike.congr_fun hφ
  -- 🎉 no goals
#align monoid_algebra.exists_left_inverse_of_injective MonoidAlgebra.exists_leftInverse_of_injective

namespace Submodule

theorem exists_isCompl (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q := by
  have : IsScalarTower k (MonoidAlgebra k G) p := p.isScalarTower'
  -- ⊢ ∃ q, IsCompl p q
  rcases MonoidAlgebra.exists_leftInverse_of_injective p.subtype p.ker_subtype with ⟨f, hf⟩
  -- ⊢ ∃ q, IsCompl p q
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj ?_⟩
  -- ⊢ ∀ (x : { x // x ∈ p }), ↑f ↑x = x
  exact FunLike.congr_fun hf
  -- 🎉 no goals
#align monoid_algebra.submodule.exists_is_compl MonoidAlgebra.Submodule.exists_isCompl

/-- This also implies an instance `IsSemisimpleModule (MonoidAlgebra k G) V`. -/
instance complementedLattice : ComplementedLattice (Submodule (MonoidAlgebra k G) V) :=
  ⟨exists_isCompl⟩
#align monoid_algebra.submodule.complemented_lattice MonoidAlgebra.Submodule.complementedLattice

end Submodule

end MonoidAlgebra
