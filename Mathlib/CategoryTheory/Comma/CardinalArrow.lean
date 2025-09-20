/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Cardinal of Arrow

We obtain various results about the cardinality of `Arrow C`. For example,
If `A` is a (small) category, `Arrow C` is finite iff `FinCategory C` holds.

-/

universe w w' v' u' v u

namespace CategoryTheory

lemma Arrow.finite_iff (C : Type u) [SmallCategory C] :
    Finite (Arrow C) ↔ Nonempty (FinCategory C) := by
  constructor
  · intro
    refine ⟨?_, fun a b ↦ ?_⟩
    · have := Finite.of_injective (fun (a : C) ↦ Arrow.mk (𝟙 a))
        (fun _ _  ↦ congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) ↦ Arrow.mk f)
        (fun f g h ↦ by
          change (Arrow.mk f).hom = (Arrow.mk g).hom
          congr)
      apply Fintype.ofFinite
  · rintro ⟨_⟩
    have := Fintype.ofEquiv  _ (Arrow.equivSigma C).symm
    infer_instance

instance Arrow.finite {C : Type u} [SmallCategory C] [FinCategory C] :
    Finite (Arrow C) := by
  rw [Arrow.finite_iff]
  exact ⟨inferInstance⟩

/-- The bijection `Arrow Cᵒᵖ ≃ Arrow C`. -/
def Arrow.opEquiv (C : Type u) [Category.{v} C] : Arrow Cᵒᵖ ≃ Arrow C where
  toFun f := Arrow.mk f.hom.unop
  invFun g := Arrow.mk g.hom.op

@[simp]
lemma hasCardinalLT_arrow_op_iff (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow Cᵒᵖ) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.opEquiv C) κ

@[simp]
lemma hasCardinalLT_arrow_discrete_iff {X : Type u} (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow (Discrete X)) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv (Arrow.discreteEquiv X) κ

lemma small_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
    Small.{w} C :=
  small_of_injective (f := fun X ↦ Arrow.mk (𝟙 X)) (fun _ _ h ↦ congr_arg Comma.left h)

lemma locallySmall_of_small_arrow (C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] :
    LocallySmall.{w} C where
  hom_small X Y :=
    small_of_injective (f := fun f ↦ Arrow.mk f) (fun f g h ↦ by
      change (Arrow.mk f).hom = (Arrow.mk g).hom
      congr)

/-- The bijection `Arrow.{w} (ShrinkHoms C) ≃ Arrow C`. -/
noncomputable def Arrow.shrinkHomsEquiv (C : Type u) [Category.{v} C] [LocallySmall.{w} C] :
    Arrow.{w} (ShrinkHoms C) ≃ Arrow C where
  toFun := (ShrinkHoms.equivalence C).inverse.mapArrow.obj
  invFun := (ShrinkHoms.equivalence C).functor.mapArrow.obj
  left_inv _ := by simp
  right_inv _ := by simp

/-- The bijection `Arrow (Shrink C) ≃ Arrow C`. -/
noncomputable def Arrow.shrinkEquiv (C : Type u) [Category.{v} C] [Small.{w} C] :
    Arrow (Shrink.{w} C) ≃ Arrow C where
  toFun := (Shrink.equivalence C).inverse.mapArrow.obj
  invFun := (Shrink.equivalence C).functor.mapArrow.obj
  left_inv _ := Arrow.ext (Equiv.apply_symm_apply _ _)
      ((Equiv.apply_symm_apply _ _)) (by simp; rfl)
  right_inv _ := Arrow.ext (by simp [Shrink.equivalence])
    (by simp [Shrink.equivalence]) (by simp [Shrink.equivalence])

@[simp]
lemma hasCardinalLT_arrow_shrinkHoms_iff (C : Type u) [Category.{v} C] [LocallySmall.{w'} C]
    (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow.{w'} (ShrinkHoms C)) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.shrinkHomsEquiv C) κ

@[simp]
lemma hasCardinalLT_arrow_shrink_iff (C : Type u) [Category.{v} C] [Small.{w'} C]
    (κ : Cardinal.{w}) :
    HasCardinalLT (Arrow (Shrink.{w'} C)) κ ↔ HasCardinalLT (Arrow C) κ :=
  hasCardinalLT_iff_of_equiv (Arrow.shrinkEquiv C) κ

lemma hasCardinalLT_of_hasCardinalLT_arrow
    {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardinalLT (Arrow C) κ) :
    HasCardinalLT C κ :=
  h.of_injective (fun X ↦ Arrow.mk (𝟙 X)) (fun _ _ h ↦ congr_arg Comma.left h)

instance {C : Type u} [Category.{v} C] [Small.{w} C] [LocallySmall.{w} C] :
    Small.{w} (Arrow C) := by
  let φ (f : Arrow C) : Σ (s t : C), s ⟶ t := ⟨_, _, f.hom⟩
  refine small_of_injective (f := φ) ?_
  rintro ⟨s, t, f⟩ ⟨s', t', f'⟩ h
  obtain rfl : s = s' := congr_arg Sigma.fst h
  simp only [Functor.id_obj, Sigma.mk.injEq, heq_eq_eq, true_and, φ] at h
  obtain rfl : t = t' := h.1
  obtain rfl : f = f' := by simpa using h
  rfl

instance {C : Type u} [Category.{v} C] [Small.{w} C] [LocallySmall.{w} C]
    {D : Type u'} [Category.{v'} D] [Small.{w} D] [LocallySmall.{w} D] :
    Small.{w} (C ⥤ D) := by
  refine small_of_injective (f := fun F (f : Arrow C) ↦ Arrow.mk (F.map f.hom))
    (fun F G h ↦ Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_))
  · exact congr_arg Comma.left (congr_fun h (Arrow.mk (𝟙 X)))
  · have : Arrow.mk (F.map f) = Arrow.mk (G.map f) := congr_fun h (Arrow.mk f)
    rw [Arrow.mk_eq_mk_iff] at this
    tauto

end CategoryTheory
