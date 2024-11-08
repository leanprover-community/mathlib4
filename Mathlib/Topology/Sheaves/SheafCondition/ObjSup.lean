/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The objects at the union of two opens.

## Main results

* `TopCat.Sheaf.objSupIsoProdEqLocus`: `F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps
  `F(U) × F(V) ⟶ F(U ⊓ V)`
-/


noncomputable section

universe w v u

open TopologicalSpace Opposite CategoryTheory

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

namespace TopCat.Sheaf

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/-- `F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps `F(U) × F(V) ⟶ F(U ⊓ V)`. -/
def objSupIsoProdEqLocus {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) :
    F.1.obj (op <| U ⊔ V) ≅ CommRingCat.of <|
    -- Porting note: Lean 3 is able to figure out the ring homomorphism automatically
    RingHom.eqLocus
      (RingHom.comp (F.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
        (RingHom.fst (F.val.obj <| op U) (F.val.obj <| op V)))
      (RingHom.comp (F.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)
        (RingHom.snd (F.val.obj <| op U) (F.val.obj <| op V))) :=
  (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)

theorem objSupIsoProdEqLocus_hom_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.fst = F.1.map (homOfLE le_sup_left).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

theorem objSupIsoProdEqLocus_hom_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.snd = F.1.map (homOfLE le_sup_right).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

theorem objSupIsoProdEqLocus_inv_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_left).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.1 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

theorem objSupIsoProdEqLocus_inv_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_right).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.2 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

theorem objSupIsoProdEqLocus_inv_eq_iff {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
    {U V W UW VW : Opens X} (e : W ≤ U ⊔ V) (x) (y : F.1.obj (op W))
    (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W) :
    F.1.map (homOfLE e).op ((F.objSupIsoProdEqLocus U V).inv x) = y ↔
    F.1.map (homOfLE (h₁ ▸ inf_le_left : UW ≤ U)).op x.1.1 =
      F.1.map (homOfLE <| h₁ ▸ inf_le_right).op y ∧
    F.1.map (homOfLE (h₂ ▸ inf_le_left : VW ≤ V)).op x.1.2 =
      F.1.map (homOfLE <| h₂ ▸ inf_le_right).op y := by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    -- `simp` doesn't see through the type equality of objects in `CommRingCat`, so use `rw` #8386
    repeat rw [← comp_apply]
    simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq₂
      (homOfLE (inf_le_right : U ⊓ W ≤ W)) (homOfLE (inf_le_right : V ⊓ W ≤ W)) ?_ _ _ ?_ ?_
    · rw [← inf_sup_right]
      exact le_inf e le_rfl
    · rw [← e₁, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]
      -- `simp` doesn't see through the type equality of objects in `CommRingCat`, so use `rw` #8386
      repeat rw [← comp_apply]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp]
    · rw [← e₂, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
      -- `simp` doesn't see through the type equality of objects in `CommRingCat`, so use `rw` #8386
      repeat rw [← comp_apply]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp]

end TopCat.Sheaf
