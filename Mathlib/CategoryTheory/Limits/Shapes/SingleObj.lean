/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# (Co)limits of functors out of `SingleObj M`

We characterise (co)limits of shape `SingleObj M`. Currently only in the category of types.

## Main results

* `SingleObj.Types.limitEquivFixedPoints`: The limit of `J : SingleObj G ⥤ Type u` is the fixed
  points of `J.obj (SingleObj.star G)` under the induced action.

* `SingleObj.Types.colimitEquivQuotient`: The colimit of `J : SingleObj G ⥤ Type u` is the
  quotient of `J.obj (SingleObj.star G)` by the induced action.

-/

assert_not_exists MonoidWithZero

universe u v

namespace CategoryTheory

namespace Limits

namespace SingleObj

variable {M G : Type v} [Monoid M] [Group G]

/-- The induced `G`-action on the target of `J : SingleObj G ⥤ Type u`. -/
instance (J : SingleObj M ⥤ Type u) : MulAction M (J.obj (SingleObj.star M)) where
  smul g x := J.map g x
  one_smul x := by
    change J.map (𝟙 _) x = x
    simp only [FunctorToTypes.map_id_apply]
  mul_smul g h x := by
    change J.map (g * h) x = (J.map h ≫ J.map g) x
    rw [← SingleObj.comp_as_mul]
    · simp only [FunctorToTypes.map_comp_apply, types_comp_apply]
      rfl

section Limits

variable (J : SingleObj M ⥤ Type u)

/-- The equivalence between sections of `J : SingleObj M ⥤ Type u` and fixed points of the
induced action on `J.obj (SingleObj.star M)`. -/
@[simps]
def Types.sections.equivFixedPoints :
    J.sections ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) where
  toFun s := ⟨s.val _, s.property⟩
  invFun p := ⟨fun _ ↦ p.val, p.property⟩

/-- The limit of `J : SingleObj M ⥤ Type u` is equivalent to the fixed points of the
induced action on `J.obj (SingleObj.star M)`. -/
@[simps!]
noncomputable def Types.limitEquivFixedPoints :
    limit J ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) :=
  (Types.limitEquivSections J).trans (Types.sections.equivFixedPoints J)

end Limits

section Colimits

variable {G : Type v} [Group G] (J : SingleObj G ⥤ Type u)

/-- The relation used to construct colimits in types for `J : SingleObj G ⥤ Type u` is
equivalent to the `MulAction.orbitRel` equivalence relation on `J.obj (SingleObj.star G)`. -/
lemma colimitTypeRel_iff_orbitRel (x y : J.obj (SingleObj.star G)) :
    J.ColimitTypeRel ⟨SingleObj.star G, x⟩ ⟨SingleObj.star G, y⟩ ↔
      MulAction.orbitRel G (J.obj (SingleObj.star G)) x y := by
  have h (g : G) : y = g • x ↔ g • x = y := ⟨symm, symm⟩
  conv => rhs; rw [Setoid.comm']
  change (∃ g : G, y = g • x) ↔ (∃ g : G, g • x = y)
  grind

@[deprecated (since := "2025-06-22")] alias Types.Quot.Rel.iff_orbitRel :=
  colimitTypeRel_iff_orbitRel

/-- The explicit quotient construction of the colimit of `J : SingleObj G ⥤ Type u` is
equivalent to the quotient of `J.obj (SingleObj.star G)` by the induced action. -/
@[simps]
def colimitTypeRelEquivOrbitRelQuotient :
    J.ColimitType ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) where
  toFun := Quot.lift (fun p ↦ ⟦p.2⟧) <| fun a b h ↦ Quotient.sound <|
    (colimitTypeRel_iff_orbitRel J a.2 b.2).mp h
  invFun := Quot.lift (fun x ↦ Quot.mk _ ⟨SingleObj.star G, x⟩) <| fun a b h ↦
    Quot.sound <| (colimitTypeRel_iff_orbitRel J a b).mpr h
  left_inv := fun x ↦ Quot.inductionOn x (fun _ ↦ rfl)
  right_inv := fun x ↦ Quot.inductionOn x (fun _ ↦ rfl)

@[deprecated (since := "2025-06-22")] alias Types.Quot.equivOrbitRelQuotient :=
  colimitTypeRelEquivOrbitRelQuotient

/-- The colimit of `J : SingleObj G ⥤ Type u` is equivalent to the quotient of
`J.obj (SingleObj.star G)` by the induced action. -/
@[simps!]
noncomputable def Types.colimitEquivQuotient :
    colimit J ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) :=
  (Types.colimitEquivColimitType J).trans (colimitTypeRelEquivOrbitRelQuotient J)

end Colimits

end SingleObj

end Limits

end CategoryTheory
