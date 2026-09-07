/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The Tate-Shafarevich group of a continuous representation

This file defines a general notion of a Tate-Shafarevich group for a continuous representation `A`
over a field `K`, as the intersection of the kernels of the maps `Hⁿ(K, A) → Hⁿ(Kᵥ, Aᵥ)`.

Here `Kᵥ` is a `K`-algebra for each place `v` in an arbitrary indexing set `V`,
which induces maps between absolute Galois groups and hence maps between cohomology groups.

When `V` is the set of places of a global field `K`, `A` is the set of rational points of an abelian
variety over K, and `n = 1`, this recovers the classical definition of the Tate-Shafarevich group.
-/

@[expose] public section

universe u

variable {K V : Type u} [Field K] (f : V → Type u) [h : ∀ v : V, Field (f v)]
  [h' : ∀ v : V, Algebra K (f v)] [TopologicalSpace K] (A : TopRep K (Field.absoluteGaloisGroup K))
  (n : ℕ)

open CategoryTheory

namespace ContinuousCohomology

/-- The Tate-Shafarevich group of a continuous representation. -/
@[simps!]
noncomputable def tateSha : Submodule K (continuousCohomology n A) :=
  letI (v : V) : Algebra (AlgebraicClosure K) (AlgebraicClosure (f v)) := IsAlgClosed.lift.toAlgebra
  letI (v : V) : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (IsAlgClosed.lift.commutes k).symm
  iInf (fun v : V ↦ (ContinuousCohomology.map (X := A)
    (Field.absoluteGaloisGroup.mapOfAlgebra K (f v)) (𝟙 _) n).hom.ker)

lemma tateSha_eq_iInf :
    letI (v : V) : Algebra (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
      IsAlgClosed.lift.toAlgebra
    letI (v : V) : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
      IsScalarTower.of_algebraMap_eq (IsAlgClosed.lift.commutes · |>.symm)
    tateSha f A n = iInf (fun v : V ↦ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.mapOfAlgebra K (f v)) (𝟙 _) n).hom.ker) := rfl

lemma tateSha_eq_ker_pi :
    letI (v : V) : Algebra (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
      IsAlgClosed.lift.toAlgebra
    letI (v : V) : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
      IsScalarTower.of_algebraMap_eq (IsAlgClosed.lift.commutes · |>.symm)
    tateSha f A n = (LinearMap.pi fun v : V ↦ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.mapOfAlgebra K (f v)) (𝟙 _) n).hom.toLinearMap).ker := by
  rw [tateSha_eq_iInf, LinearMap.ker_pi]

@[simp]
lemma mem_tateSha (x : continuousCohomology n A) : x ∈ tateSha f A n ↔
    letI (v : V) : Algebra (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
      IsAlgClosed.lift.toAlgebra
    letI (v : V) : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure (f v)) :=
      IsScalarTower.of_algebraMap_eq (IsAlgClosed.lift.commutes · |>.symm)
    ∀ v : V, x ∈ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.mapOfAlgebra K (f v)) (𝟙 _) n).hom.ker := by
  simp [tateSha_eq_iInf]

end ContinuousCohomology
