/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Jujian Zhang
-/

import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!

# Main definitions and results

In a field extension `K/k`

* `finGaloisGroup L` : The (finite) Galois group `Gal(L/k)` associated to a
  `L : FiniteGaloisIntermediateField k K` `L`.

* `finGaloisGroupMap` : For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGaloisGroupFunctor` : Mapping `FiniteGaloisIntermediateField` ordered by inverse inclusion to
  its corresponding Galois Group as `FiniteGrp`.

-/

open CategoryTheory Opposite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Profinite

/-- The (finite) Galois group `Gal(L / k)` associated to a
`L : FiniteGaloisIntermediateField k K` `L`. -/
def FiniteGaloisIntermediateField.finGaloisGroup (L : FiniteGaloisIntermediateField k K) :
    FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of <| L ≃ₐ[k] L

/-- For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  the restriction homomorphism from `Gal(L₁/k)` to `Gal(L₂/k)` -/
noncomputable def finGaloisGroupMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) : L₁.unop.finGaloisGroup ⟶ L₂.unop.finGaloisGroup :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

namespace finGaloisGroupMap

@[simp]
lemma map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGaloisGroupMap (𝟙 L)) = 𝟙 L.unop.finGaloisGroup :=
  AlgEquiv.restrictNormalHom_id _ _

@[simp]
lemma map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    finGaloisGroupMap (f ≫ g) = finGaloisGroupMap f ≫ finGaloisGroupMap g := by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  letI : Algebra L₃ L₂ := RingHom.toAlgebra (Subsemiring.inclusion g.unop.le)
  letI : Algebra L₂ L₁ := RingHom.toAlgebra (Subsemiring.inclusion f.unop.le)
  letI : Algebra L₃ L₁ := RingHom.toAlgebra (Subsemiring.inclusion (g.unop.le.trans f.unop.le))
  haveI : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  apply IsScalarTower.AlgEquiv.restrictNormalHom_comp k L₃ L₂ L₁

end finGaloisGroupMap

variable (k K) in
/-- The functor from `FiniteGaloisIntermediateField` (ordered by reverse inclusion) to `FiniteGrp`,
mapping each intermediate field `K/L/k` to `Gal (L/k)`.-/
noncomputable def finGaloisGroupFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGaloisGroup
  map := finGaloisGroupMap
  map_id := finGaloisGroupMap.map_id
  map_comp := finGaloisGroupMap.map_comp

end Profinite
