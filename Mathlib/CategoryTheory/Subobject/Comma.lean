/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

#align_import category_theory.subobject.comma from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Subobjects in the category of structured arrows

We compute the subobjects of an object `A` in the category `StructuredArrow S T` for `T : C ⥤ D`
and `S : D` as a subtype of the subobjects of `A.right`. We deduce that `StructuredArrow S T` is
well-powered if `C` is.

## Main declarations
* `StructuredArrow.subobjectEquiv `: the order-equivalence between `Subobject A` and a subtype of
  `Subobject A.right`.

## Implementation notes
Our computation requires that `C` has all limits and `T` preserves all limits. Furthermore, we
require that the morphisms of `C` and `D` are in the same universe. It is possible that both of
these requirements can be relaxed by refining the results about limits in comma categories.

We also provide the dual results. As usual, we use `Subobject (op A)` for the quotient objects of
`A`.

-/

noncomputable section

open CategoryTheory.Limits Opposite

universe v u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

/-- Every subobject of a structured arrow can be projected to a subobject of the underlying
    object. -/
def projectSubobject [HasLimits C] [PreservesLimits T] {A : StructuredArrow S T} :
    Subobject A → Subobject A.right := by
  refine' Subobject.lift (fun P f hf => Subobject.mk f.right) _
  -- ⊢ ∀ ⦃A_1 B : StructuredArrow S T⦄ (f : A_1 ⟶ A) (g : B ⟶ A) [inst : Mono f] [i …
  intro P Q f g hf hg i hi
  -- ⊢ (fun P f hf => Subobject.mk f.right) P f hf = (fun P f hf => Subobject.mk f. …
  refine' Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) _
  -- ⊢ ((proj S T).mapIso i).hom ≫ g.right = f.right
  exact congr_arg CommaMorphism.right hi
  -- 🎉 no goals
#align category_theory.structured_arrow.project_subobject CategoryTheory.StructuredArrow.projectSubobject

@[simp]
theorem projectSubobject_mk [HasLimits C] [PreservesLimits T] {A P : StructuredArrow S T}
    (f : P ⟶ A) [Mono f] : projectSubobject (Subobject.mk f) = Subobject.mk f.right :=
  rfl
#align category_theory.structured_arrow.project_subobject_mk CategoryTheory.StructuredArrow.projectSubobject_mk

theorem projectSubobject_factors [HasLimits C] [PreservesLimits T] {A : StructuredArrow S T} :
    ∀ P : Subobject A, ∃ q, q ≫ T.map (projectSubobject P).arrow = A.hom :=
  Subobject.ind _ fun P f hf =>
    ⟨P.hom ≫ T.map (Subobject.underlyingIso _).inv, by
      dsimp
      -- ⊢ (P.hom ≫ T.map (Subobject.underlyingIso f.right).inv) ≫ T.map (Subobject.arr …
      simp [← T.map_comp]⟩
      -- 🎉 no goals
#align category_theory.structured_arrow.project_subobject_factors CategoryTheory.StructuredArrow.projectSubobject_factors

/-- A subobject of the underlying object of a structured arrow can be lifted to a subobject of
    the structured arrow, provided that there is a morphism making the subobject into a structured
    arrow. -/
@[simp]
def liftSubobject {A : StructuredArrow S T} (P : Subobject A.right) {q}
    (hq : q ≫ T.map P.arrow = A.hom) : Subobject A :=
  Subobject.mk (homMk P.arrow hq : mk q ⟶ A)
#align category_theory.structured_arrow.lift_subobject CategoryTheory.StructuredArrow.liftSubobject

/-- Projecting and then lifting a subobject recovers the original subobject, because there is at
    most one morphism making the projected subobject into a structured arrow. -/
theorem lift_projectSubobject [HasLimits C] [PreservesLimits T] {A : StructuredArrow S T} :
    ∀ (P : Subobject A) {q} (hq : q ≫ T.map (projectSubobject P).arrow = A.hom),
      liftSubobject (projectSubobject P) hq = P :=
  Subobject.ind _
    (by
      intro P f hf q hq
      -- ⊢ liftSubobject (projectSubobject (Subobject.mk f)) hq = Subobject.mk f
      fapply Subobject.mk_eq_mk_of_comm
      -- ⊢ mk q ≅ P
      · fapply isoMk
        -- ⊢ (mk q).right ≅ P.right
        · exact Subobject.underlyingIso _
          -- 🎉 no goals
        · exact (cancel_mono (T.map f.right)).1 (by dsimp; simpa [← T.map_comp] using hq)
          -- 🎉 no goals
      · exact ext _ _ (by dsimp; simp))
        -- 🎉 no goals
#align category_theory.structured_arrow.lift_project_subobject CategoryTheory.StructuredArrow.lift_projectSubobject

/-- If `A : S → T.obj B` is a structured arrow for `S : D` and `T : C ⥤ D`, then we can explicitly
    describe the subobjects of `A` as the subobjects `P` of `B` in `C` for which `A.hom` factors
    through the image of `P` under `T`. -/
@[simps!]
def subobjectEquiv [HasLimits C] [PreservesLimits T] (A : StructuredArrow S T) :
    Subobject A ≃o { P : Subobject A.right // ∃ q, q ≫ T.map P.arrow = A.hom } where
  toFun P := ⟨projectSubobject P, projectSubobject_factors P⟩
  invFun P := liftSubobject P.val P.prop.choose_spec
  left_inv P := lift_projectSubobject _ _
  right_inv P := Subtype.ext (by simp only [liftSubobject, homMk_right, projectSubobject_mk,
      Subobject.mk_arrow, Subtype.coe_eta])
  map_rel_iff' := by
    apply Subobject.ind₂
    -- ⊢ ∀ ⦃A_1 B : StructuredArrow S T⦄ (f : A_1 ⟶ A) (g : B ⟶ A) [inst : Mono f] [i …
    intro P Q f g hf hg
    -- ⊢ ↑{ toFun := fun P => { val := projectSubobject P, property := (_ : ∃ q, q ≫  …
    refine' ⟨fun h => Subobject.mk_le_mk_of_comm _ _, fun h => _⟩
    · exact homMk (Subobject.ofMkLEMk _ _ h)
        ((cancel_mono (T.map g.right)).1 (by simp [← T.map_comp]))
    · aesop_cat
      -- 🎉 no goals
    · refine' Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).right _
      -- ⊢ (Subobject.ofMkLEMk f g h).right ≫ (MonoOver.arrow (MonoOver.mk' g)).right = …
      exact congr_arg CommaMorphism.right (Subobject.ofMkLEMk_comp h)
      -- 🎉 no goals
#align category_theory.structured_arrow.subobject_equiv CategoryTheory.StructuredArrow.subobjectEquiv

/-- If `C` is well-powered and complete and `T` preserves limits, then `StructuredArrow S T` is
    well-powered. -/
instance wellPowered_structuredArrow [WellPowered C] [HasLimits C] [PreservesLimits T] :
    WellPowered (StructuredArrow S T)
    where subobject_small X := small_map (subobjectEquiv X).toEquiv
#align category_theory.structured_arrow.well_powered_structured_arrow CategoryTheory.StructuredArrow.wellPowered_structuredArrow

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

/-- Every quotient of a costructured arrow can be projected to a quotient of the underlying
    object. -/
def projectQuotient [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T} :
    Subobject (op A) → Subobject (op A.left) := by
  refine' Subobject.lift (fun P f hf => Subobject.mk f.unop.left.op) _
  -- ⊢ ∀ ⦃A_1 B : (CostructuredArrow S T)ᵒᵖ⦄ (f : A_1 ⟶ op A) (g : B ⟶ op A) [inst  …
  intro P Q f g hf hg i hi
  -- ⊢ (fun P f hf => Subobject.mk f.unop.left.op) P f hf = (fun P f hf => Subobjec …
  refine' Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i.unop).op (Quiver.Hom.unop_inj _)
  -- ⊢ ((Iso.op ((proj S T).mapIso (Iso.unop i))).hom ≫ g.unop.left.op).unop = f.un …
  have := congr_arg Quiver.Hom.unop hi
  -- ⊢ ((Iso.op ((proj S T).mapIso (Iso.unop i))).hom ≫ g.unop.left.op).unop = f.un …
  simpa using congr_arg CommaMorphism.left this
  -- 🎉 no goals
#align category_theory.costructured_arrow.project_quotient CategoryTheory.CostructuredArrow.projectQuotient

@[simp]
theorem projectQuotient_mk [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f] :
    projectQuotient (Subobject.mk f) = Subobject.mk f.unop.left.op :=
  rfl
#align category_theory.costructured_arrow.project_quotient_mk CategoryTheory.CostructuredArrow.projectQuotient_mk

theorem projectQuotient_factors [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T} :
    ∀ P : Subobject (op A), ∃ q, S.map (projectQuotient P).arrow.unop ≫ q = A.hom :=
  Subobject.ind _ fun P f hf =>
    ⟨S.map (Subobject.underlyingIso _).unop.inv ≫ P.unop.hom, by
      dsimp
      -- ⊢ S.map (Subobject.arrow (Subobject.mk f.unop.left.op)).unop ≫ S.map (Subobjec …
      rw [← Category.assoc, ← S.map_comp, ← unop_comp]
      -- ⊢ S.map ((Subobject.underlyingIso f.unop.left.op).inv ≫ Subobject.arrow (Subob …
      simp⟩
      -- 🎉 no goals
#align category_theory.costructured_arrow.project_quotient_factors CategoryTheory.CostructuredArrow.projectQuotient_factors

/-- A quotient of the underlying object of a costructured arrow can be lifted to a quotient of
    the costructured arrow, provided that there is a morphism making the quotient into a
    costructured arrow. -/
@[simp]
def liftQuotient {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q}
    (hq : S.map P.arrow.unop ≫ q = A.hom) : Subobject (op A) :=
  Subobject.mk (homMk P.arrow.unop hq : A ⟶ mk q).op
#align category_theory.costructured_arrow.lift_quotient CategoryTheory.CostructuredArrow.liftQuotient

/-- Technical lemma for `lift_projectQuotient`. -/
@[simp]
theorem unop_left_comp_underlyingIso_hom_unop {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f.unop.left.op] :
    f.unop.left ≫ (Subobject.underlyingIso f.unop.left.op).hom.unop =
      (Subobject.mk f.unop.left.op).arrow.unop := by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op f.unop.left]
  rw [← unop_comp, Subobject.underlyingIso_hom_comp_eq_mk]
  -- 🎉 no goals
#align category_theory.costructured_arrow.unop_left_comp_underlying_iso_hom_unop CategoryTheory.CostructuredArrow.unop_left_comp_underlyingIso_hom_unop

/-- Projecting and then lifting a quotient recovers the original quotient, because there is at most
    one morphism making the projected quotient into a costructured arrow. -/
theorem lift_projectQuotient [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T} :
    ∀ (P : Subobject (op A)) {q} (hq : S.map (projectQuotient P).arrow.unop ≫ q = A.hom),
      liftQuotient (projectQuotient P) hq = P :=
  Subobject.ind _
    (by
      intro P f hf q hq
      -- ⊢ liftQuotient (projectQuotient (Subobject.mk f)) hq = Subobject.mk f
      fapply Subobject.mk_eq_mk_of_comm
      -- ⊢ op (mk q) ≅ P
      · refine' (Iso.op (isoMk _ _) : _ ≅ op (unop P))
        -- ⊢ P.unop.left ≅ (mk q).left
        · exact (Subobject.underlyingIso f.unop.left.op).unop
          -- 🎉 no goals
        · refine' (cancel_epi (S.map f.unop.left)).1 _
          -- ⊢ S.map f.unop.left ≫ S.map (Iso.unop (Subobject.underlyingIso f.unop.left.op) …
          simpa [← Category.assoc, ← S.map_comp] using hq
          -- 🎉 no goals
      · exact Quiver.Hom.unop_inj (by aesop_cat))
        -- 🎉 no goals
#align category_theory.costructured_arrow.lift_project_quotient CategoryTheory.CostructuredArrow.lift_projectQuotient

/-- Technical lemma for `quotientEquiv`. -/
theorem unop_left_comp_ofMkLEMk_unop {A : CostructuredArrow S T} {P Q : (CostructuredArrow S T)ᵒᵖ}
    {f : P ⟶ op A} {g : Q ⟶ op A} [Mono f.unop.left.op] [Mono g.unop.left.op]
    (h : Subobject.mk f.unop.left.op ≤ Subobject.mk g.unop.left.op) :
    g.unop.left ≫ (Subobject.ofMkLEMk f.unop.left.op g.unop.left.op h).unop = f.unop.left := by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op g.unop.left]
  rw [← unop_comp]
  -- ⊢ (Subobject.ofMkLEMk f.unop.left.op g.unop.left.op h ≫ g.unop.left.op).unop = …
  simp only [Subobject.ofMkLEMk_comp, Quiver.Hom.unop_op]
  -- 🎉 no goals
#align category_theory.costructured_arrow.unop_left_comp_of_mk_le_mk_unop CategoryTheory.CostructuredArrow.unop_left_comp_ofMkLEMk_unop

/-- If `A : S.obj B ⟶ T` is a costructured arrow for `S : C ⥤ D` and `T : D`, then we can
    explicitly describe the quotients of `A` as the quotients `P` of `B` in `C` for which `A.hom`
    factors through the image of `P` under `S`. -/
def quotientEquiv [HasColimits C] [PreservesColimits S] (A : CostructuredArrow S T) :
    Subobject (op A) ≃o { P : Subobject (op A.left) // ∃ q, S.map P.arrow.unop ≫ q = A.hom } where
  toFun P := ⟨projectQuotient P, projectQuotient_factors P⟩
  invFun P := liftQuotient P.val P.prop.choose_spec
  left_inv P := lift_projectQuotient _ _
  right_inv P := Subtype.ext (by simp only [liftQuotient, Quiver.Hom.unop_op, homMk_left,
      Quiver.Hom.op_unop, projectQuotient_mk, Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    -- ⊢ ∀ ⦃A_1 B : (CostructuredArrow S T)ᵒᵖ⦄ (f : A_1 ⟶ op A) (g : B ⟶ op A) [inst  …
    intro P Q f g hf hg
    -- ⊢ ↑{ toFun := fun P => { val := projectQuotient P, property := (_ : ∃ q, S.map …
    refine' ⟨fun h => Subobject.mk_le_mk_of_comm _ _, fun h => _⟩
    · refine' (homMk (Subobject.ofMkLEMk _ _ h).unop ((cancel_epi (S.map g.unop.left)).1 _)).op
      -- ⊢ S.map g.unop.left ≫ S.map (Subobject.ofMkLEMk (MonoOver.arrow (MonoOver.mk'  …
      dsimp
      -- ⊢ S.map g.unop.left ≫ S.map (Subobject.ofMkLEMk f.unop.left.op g.unop.left.op  …
      simp only [← S.map_comp_assoc, unop_left_comp_ofMkLEMk_unop, unop_op, CommaMorphism.w,
        Functor.const_obj_obj, right_eq_id, Functor.const_obj_map, Category.comp_id]
    · apply Quiver.Hom.unop_inj
      -- ⊢ ((homMk (Subobject.ofMkLEMk (MonoOver.arrow (MonoOver.mk' f)).unop.left.op ( …
      ext
      -- ⊢ ((homMk (Subobject.ofMkLEMk (MonoOver.arrow (MonoOver.mk' f)).unop.left.op ( …
      exact unop_left_comp_ofMkLEMk_unop _
      -- 🎉 no goals
    · refine' Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).unop.left.op _
      -- ⊢ (Subobject.ofMkLEMk f g h).unop.left.op ≫ (MonoOver.arrow (MonoOver.mk' g)). …
      refine' Quiver.Hom.unop_inj _
      -- ⊢ ((Subobject.ofMkLEMk f g h).unop.left.op ≫ (MonoOver.arrow (MonoOver.mk' g)) …
      have := congr_arg Quiver.Hom.unop (Subobject.ofMkLEMk_comp h)
      -- ⊢ ((Subobject.ofMkLEMk f g h).unop.left.op ≫ (MonoOver.arrow (MonoOver.mk' g)) …
      simpa only [unop_op, Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
        MonoOver.mk'_arrow, unop_comp, Quiver.Hom.unop_op, comp_left]
          using congr_arg CommaMorphism.left this
#align category_theory.costructured_arrow.quotient_equiv CategoryTheory.CostructuredArrow.quotientEquiv

/-- If `C` is well-copowered and cocomplete and `S` preserves colimits, then
    `CostructuredArrow S T` is well-copowered. -/
instance well_copowered_costructuredArrow [WellPowered Cᵒᵖ] [HasColimits C] [PreservesColimits S] :
    WellPowered (CostructuredArrow S T)ᵒᵖ
    where subobject_small X := small_map (quotientEquiv (unop X)).toEquiv
#align category_theory.costructured_arrow.well_copowered_costructured_arrow CategoryTheory.CostructuredArrow.well_copowered_costructuredArrow

end CostructuredArrow

end CategoryTheory
