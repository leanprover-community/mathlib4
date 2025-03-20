/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `Fintype.card G` invertible in `k`.

We do the core computation in greater generality.
For any commutative ring `k` in which `Fintype.card G` is invertible,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes

* These results assume `IsUnit (Fintype.card G : k)` which is equivalent to the more
  familiar `¬(ringChar k ∣ Fintype.card G)`.

## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/


universe u v w

noncomputable section

open Module MonoidAlgebra

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
-- `IsUnit (Fintype.card G : k)` when it is required.
variable {k : Type u} [CommRing k] {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
variable [IsScalarTower k (MonoidAlgebra k G) V]
variable {W : Type w} [AddCommGroup W] [Module k W] [Module (MonoidAlgebra k G) W]
variable [IsScalarTower k (MonoidAlgebra k G) W]
variable (π : W →ₗ[k] V)

/-- We define the conjugate of `π` by `g`, as a `k`-linear map. -/
def conjugate (g : G) : W →ₗ[k] V :=
  GroupSMul.linearMap k V g⁻¹ ∘ₗ π ∘ₗ GroupSMul.linearMap k W g

theorem conjugate_apply (g : G) (v : W) :
    π.conjugate g v = MonoidAlgebra.single g⁻¹ (1 : k) • π (MonoidAlgebra.single g (1 : k) • v) :=
  rfl

variable (i : V →ₗ[MonoidAlgebra k G] W)

section

theorem conjugate_i (h : ∀ v : V, π (i v) = v) (g : G) (v : V) :
    (conjugate π g : W → V) (i v) = v := by
  rw [conjugate_apply, ← i.map_smul, h, ← mul_smul, single_mul_single, mul_one, inv_mul_cancel,
    ← one_def, one_smul]

end

variable (G) [Fintype G]

/-- The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sumOfConjugates : W →ₗ[k] V :=
  ∑ g : G, π.conjugate g

lemma sumOfConjugates_apply (v : W) : π.sumOfConjugates G v = ∑ g : G, π.conjugate g v :=
  LinearMap.sum_apply _ _ _

/-- In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
def sumOfConjugatesEquivariant : W →ₗ[MonoidAlgebra k G] V :=
  MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v => by
    simp only [sumOfConjugates_apply, Finset.smul_sum, conjugate_apply]
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ fun i ↦ ?_
    simp only [smul_smul, single_mul_single, mul_inv_rev, mul_inv_cancel_left, one_mul]

theorem sumOfConjugatesEquivariant_apply (v : W) :
    π.sumOfConjugatesEquivariant G v = ∑ g : G, π.conjugate g v :=
  π.sumOfConjugates_apply G v

section

/-- We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariantProjection : W →ₗ[MonoidAlgebra k G] V :=
  Ring.inverse (Fintype.card G : k) • π.sumOfConjugatesEquivariant G

theorem equivariantProjection_apply (v : W) :
    π.equivariantProjection G v = Ring.inverse (Fintype.card G : k) • ∑ g : G, π.conjugate g v := by
  simp only [equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply]

theorem equivariantProjection_condition (hcard : IsUnit (Fintype.card G : k))
    (h : ∀ v : V, π (i v) = v) (v : V) : (π.equivariantProjection G) (i v) = v := by
  rw [equivariantProjection_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    Ring.inverse_mul_cancel _ hcard, one_smul]

end

end LinearMap

end

namespace MonoidAlgebra

-- Now we work over a `[Field k]`.
variable {k : Type u} [Field k] {G : Type u} [Fintype G] [NeZero (Fintype.card G : k)]
variable [Group G]
variable {V : Type u} [AddCommGroup V] [Module (MonoidAlgebra k G) V]
variable {W : Type u} [AddCommGroup W] [Module (MonoidAlgebra k G) W]

theorem exists_leftInverse_of_injective
    (f : V →ₗ[MonoidAlgebra k G] W) (hf : LinearMap.ker f = ⊥) :
    ∃ g : W →ₗ[MonoidAlgebra k G] V, g.comp f = LinearMap.id := by
  let A := MonoidAlgebra k G
  letI : Module k W := .compHom W (algebraMap k A)
  letI : Module k V := .compHom V (algebraMap k A)
  have := IsScalarTower.of_compHom k A W
  have := IsScalarTower.of_compHom k A V
  obtain ⟨φ, hφ⟩ := (f.restrictScalars k).exists_leftInverse_of_injective <| by
    simp only [hf, Submodule.restrictScalars_bot, LinearMap.ker_restrictScalars]
  refine ⟨φ.equivariantProjection G, DFunLike.ext _ _ ?_⟩
  exact φ.equivariantProjection_condition G _ (.mk0 _ <| NeZero.ne _) <| DFunLike.congr_fun hφ

namespace Submodule

theorem exists_isCompl (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q := by
  rcases MonoidAlgebra.exists_leftInverse_of_injective p.subtype p.ker_subtype with ⟨f, hf⟩
  exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj <| DFunLike.congr_fun hf⟩

/-- This also implies instances `IsSemisimpleModule (MonoidAlgebra k G) V` and
`IsSemisimpleRing (MonoidAlgebra k G)`. -/
instance complementedLattice : ComplementedLattice (Submodule (MonoidAlgebra k G) V) :=
  ⟨exists_isCompl⟩

instance [AddGroup G] : IsSemisimpleRing (AddMonoidAlgebra k G) :=
  haveI : NeZero (Fintype.card (Multiplicative G) : k) := by
    rwa [Fintype.card_congr Multiplicative.toAdd]
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := ℕ)).toRingEquiv.symm.isSemisimpleRing

end Submodule

end MonoidAlgebra
