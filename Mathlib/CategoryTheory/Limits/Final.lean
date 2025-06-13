/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Grothendieck

/-!
# Final and initial functors

A functor `F : C ⥤ D` is final if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

Dually, a functor `F : C ⥤ D` is initial if for every `d : D`,
the comma category of morphisms `F.obj c ⟶ d` is connected.

We show that right adjoints are examples of final functors, while
left adjoints are examples of initial functors.

For final functors, we prove that the following three statements are equivalent:
1. `F : C ⥤ D` is final.
2. Every functor `G : D ⥤ E` has a colimit if and only if `F ⋙ G` does,
   and these colimits are isomorphic via `colimit.pre G F`.
3. `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`.

Starting at 1. we show (in `coconesEquiv`) that
the categories of cocones over `G : D ⥤ E` and over `F ⋙ G` are equivalent.
(In fact, via an equivalence which does not change the cocone point.)
This readily implies 2., as `comp_hasColimit`, `hasColimit_of_comp`, and `colimitIso`.

From 2. we can specialize to `G = coyoneda.obj (op d)` to obtain 3., as `colimitCompCoyonedaIso`.

From 3., we prove 1. directly in `final_of_colimit_comp_coyoneda_iso_pUnit`.

Dually, we prove that if a functor `F : C ⥤ D` is initial, then any functor `G : D ⥤ E` has a
limit if and only if `F ⋙ G` does, and these limits are isomorphic via `limit.pre G F`.

In the end of the file, we characterize the finality of some important induced functors on the
(co)structured arrow category (`StructuredArrow.pre` and `CostructuredArrow.pre`) and on the
Grothendieck construction (`Grothendieck.pre` and `Grothendieck.map`).

## Naming
There is some discrepancy in the literature about naming; some say 'cofinal' instead of 'final'.
The explanation for this is that the 'co' prefix here is *not* the usual category-theoretic one
indicating duality, but rather indicating the sense of "along with".

## See also
In `CategoryTheory.Filtered.Final` we give additional equivalent conditions in the case that
`C` is filtered.

## Future work
Dualise condition 3 above and the implications 2 ⇒ 3 and 3 ⇒ 1 to initial functors.

## References
* https://stacks.math.columbia.edu/tag/09WN
* https://ncatlab.org/nlab/show/final+functor
* Borceux, Handbook of Categorical Algebra I, Section 2.11.
  (Note he reverses the roles of definition and main result relative to here!)
-/


noncomputable section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace Functor

open Opposite

open CategoryTheory.Limits

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/--
A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected. -/
@[stacks 04E6]
class Final (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (StructuredArrow d F)

attribute [instance] Final.out

/-- A functor `F : C ⥤ D` is initial if for every `d : D`, the comma category of morphisms
`F.obj c ⟶ d` is connected.
-/
class Initial (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (CostructuredArrow F d)

attribute [instance] Initial.out

instance final_op_of_initial (F : C ⥤ D) [Initial F] : Final F.op where
  out d := isConnected_of_equivalent (costructuredArrowOpEquivalence F (unop d))

instance initial_op_of_final (F : C ⥤ D) [Final F] : Initial F.op where
  out d := isConnected_of_equivalent (structuredArrowOpEquivalence F (unop d))

theorem final_of_initial_op (F : C ⥤ D) [Initial F.op] : Final F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (structuredArrowOpEquivalence F d).symm) }

theorem initial_of_final_op (F : C ⥤ D) [Final F.op] : Initial F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (costructuredArrowOpEquivalence F d).symm) }

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

/-- If a functor `R : D ⥤ C` is a right adjoint, it is final. -/
theorem final_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Final R :=
  { out := fun c =>
      let u : StructuredArrow c R := StructuredArrow.mk (adj.unit.app c)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inr ⟨StructuredArrow.homMk ((adj.homEquiv c f.right).symm f.hom) (by simp [u])⟩))
          (Relation.ReflTransGen.single
            (show Zag u g from
              Or.inl ⟨StructuredArrow.homMk ((adj.homEquiv c g.right).symm g.hom) (by simp [u])⟩)) }

/-- If a functor `L : C ⥤ D` is a left adjoint, it is initial. -/
theorem initial_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Initial L :=
  { out := fun d =>
      let u : CostructuredArrow L d := CostructuredArrow.mk (adj.counit.app d)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inl ⟨CostructuredArrow.homMk (adj.homEquiv f.left d f.hom) (by simp [u])⟩))
          (Relation.ReflTransGen.single
            (show Zag u g from
              Or.inr ⟨CostructuredArrow.homMk (adj.homEquiv g.left d g.hom) (by simp [u])⟩)) }

instance (priority := 100) final_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] : Final F :=
  final_of_adjunction (Adjunction.ofIsRightAdjoint F)

instance (priority := 100) initial_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] : Initial F :=
  initial_of_adjunction (Adjunction.ofIsLeftAdjoint F)

theorem final_of_natIso {F F' : C ⥤ D} [Final F] (i : F ≅ F') : Final F' where
  out _ := isConnected_of_equivalent (StructuredArrow.mapNatIso i)

theorem final_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Final F ↔ Final F' :=
  ⟨fun _ => final_of_natIso i, fun _ => final_of_natIso i.symm⟩

theorem initial_of_natIso {F F' : C ⥤ D} [Initial F] (i : F ≅ F') : Initial F' where
  out _ := isConnected_of_equivalent (CostructuredArrow.mapNatIso i)

theorem initial_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Initial F ↔ Initial F' :=
  ⟨fun _ => initial_of_natIso i, fun _ => initial_of_natIso i.symm⟩

namespace Final

variable (F : C ⥤ D) [Final F]

instance (d : D) : Nonempty (StructuredArrow d F) :=
  IsConnected.is_nonempty

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is final, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
def lift (d : D) : C :=
  (Classical.arbitrary (StructuredArrow d F)).right

/-- When `F : C ⥤ D` is final, we denote by `homToLift` an arbitrary choice of morphism
`d ⟶ F.obj (lift F d)`.
-/
def homToLift (d : D) : d ⟶ F.obj (lift F d) :=
  (Classical.arbitrary (StructuredArrow d F)).hom

/-- We provide an induction principle for reasoning about `lift` and `homToLift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `homToLift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : d ⟶ F.obj X₀` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : ∀ (X : C) (_ : d ⟶ F.obj X), Sort*)
    (h₁ :
      ∀ (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
        k₁ ≫ F.map f = k₂ → Z X₁ k₁ → Z X₂ k₂)
    (h₂ :
      ∀ (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
        k₁ ≫ F.map f = k₂ → Z X₂ k₂ → Z X₁ k₁)
    {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d) := by
  apply Nonempty.some
  apply
    @isPreconnected_induction _ _ _ (fun Y : StructuredArrow d F => Z Y.right Y.hom) _ _
      (StructuredArrow.mk k₀) z
  · intro j₁ j₂ f a
    fapply h₁ _ _ _ _ f.right _ a
    convert f.w.symm
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.right _ a
    convert f.w.symm
    simp

variable {F G}

/-- Given a cocone over `F ⋙ G`, we can construct a `Cocone G` with the same cocone point.
-/
@[simps]
def extendCocone : Cocone (F ⋙ G) ⥤ Cocone G where
  obj c :=
    { pt := c.pt
      ι :=
        { app := fun X => G.map (homToLift F X) ≫ c.ι.app (lift F X)
          naturality := fun X Y f => by
            dsimp; simp only [Category.comp_id]
            -- This would be true if we'd chosen `lift F X` to be `lift F Y`
            -- and `homToLift F X` to be `f ≫ homToLift F Y`.
            apply
              induction F fun Z k =>
                G.map f ≫ G.map (homToLift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, Category.assoc, ← Functor.comp_map, c.w, z]
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, Category.assoc, ← Functor.comp_map, c.w] at z
              rw [z]
            · rw [← Functor.map_comp_assoc] } }
  map f := { hom := f.hom }

/-- Alternative equational lemma for `(extendCocone c).ι.app` in case a lift of the object
is given explicitly. -/
lemma extendCocone_obj_ι_app' (c : Cocone (F ⋙ G)) {X : D} {Y : C} (f : X ⟶ F.obj Y) :
    (extendCocone.obj c).ι.app X = G.map f ≫ c.ι.app Y := by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    G.map g ≫ c.ι.app Z = G.map f ≫ c.ι.app Y
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, c.ι.naturality, h₂]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map, c.ι.naturality]

@[simp]
theorem colimit_cocone_comp_aux (s : Cocone (F ⋙ G)) (j : C) :
    G.map (homToLift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) = s.ι.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => G.map k ≫ s.ι.app X = (s.ι.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w]
    rw [← s.w f] at h
    simpa using h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w] at h
    rw [← s.w f]
    simpa using h
  · exact s.w (𝟙 _)

variable (F G)

/-- If `F` is final,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
def coconesEquiv : Cocone (F ⋙ G) ≌ Cocone G where
  functor := extendCocone
  inverse := Cocones.whiskering F
  unitIso := NatIso.ofComponents fun c => Cocones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cocones.ext (Iso.refl _)

variable {G}

/-- When `F : C ⥤ D` is final, and `t : Cocone G` for some `G : D ⥤ E`,
`t.whisker F` is a colimit cocone exactly when `t` is.
-/
def isColimitWhiskerEquiv (t : Cocone G) : IsColimit (t.whisker F) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G).symm

/-- When `F` is final, and `t : Cocone (F ⋙ G)`,
`extendCocone.obj t` is a colimit cocone exactly when `t` is.
-/
def isColimitExtendCoconeEquiv (t : Cocone (F ⋙ G)) :
    IsColimit (extendCocone.obj t) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G)

/-- Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
def colimitCoconeComp (t : ColimitCocone G) : ColimitCocone (F ⋙ G) where
  cocone := _
  isColimit := (isColimitWhiskerEquiv F _).symm t.isColimit

instance (priority := 100) comp_hasColimit [HasColimit G] : HasColimit (F ⋙ G) :=
  HasColimit.mk (colimitCoconeComp F (getColimitCocone G))

instance (priority := 100) comp_preservesColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesColimit G H] : PreservesColimit (F ⋙ G) H where
  preserves {c} hc := by
    refine ⟨isColimitExtendCoconeEquiv (G := G ⋙ H) F (H.mapCocone c) ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitExtendCoconeEquiv F c).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocones.ext (Iso.refl _) (by simp))

instance (priority := 100) comp_reflectsColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsColimit G H] : ReflectsColimit (F ⋙ G) H where
  reflects {c} hc := by
    refine ⟨isColimitExtendCoconeEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitExtendCoconeEquiv (G := G ⋙ H) F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocones.ext (Iso.refl _) (by simp))

instance (priority := 100) compCreatesColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesColimit G H] : CreatesColimit (F ⋙ G) H where
  lifts {c} hc := by
    refine ⟨(liftColimit ((isColimitExtendCoconeEquiv F (G := G ⋙ H) _).symm hc)).whisker F, ?_⟩
    let i := liftedColimitMapsToOriginal ((isColimitExtendCoconeEquiv F (G := G ⋙ H) _).symm hc)
    exact (Cocones.whiskering F).mapIso i ≪≫ ((coconesEquiv F (G ⋙ H)).unitIso.app _).symm

instance colimit_pre_isIso [HasColimit G] : IsIso (colimit.pre G F) := by
  rw [colimit.pre_eq (colimitCoconeComp F (getColimitCocone G)) (getColimitCocone G)]
  erw [IsColimit.desc_self]
  dsimp
  infer_instance

section

variable (G)

/-- When `F : C ⥤ D` is final, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`. -/
@[simps! -isSimp, stacks 04E7]
def colimitIso [HasColimit G] : colimit (F ⋙ G) ≅ colimit G :=
  asIso (colimit.pre G F)

@[reassoc (attr := simp)]
theorem ι_colimitIso_hom [HasColimit G] (X : C) :
    colimit.ι (F ⋙ G) X ≫ (colimitIso F G).hom = colimit.ι G (F.obj X) := by
  simp [colimitIso]

@[reassoc (attr := simp)]
theorem ι_colimitIso_inv [HasColimit G] (X : C) :
    colimit.ι G (F.obj X) ≫ (colimitIso F G).inv = colimit.ι (F ⋙ G) X := by
  simp [colimitIso]

/-- A pointfree version of `colimitIso`, stating that whiskering by `F` followed by taking the
colimit is isomorpic to taking the colimit on the codomain of `F`. -/
def colimIso [HasColimitsOfShape D E] [HasColimitsOfShape C E] :
    (whiskeringLeft _ _ _).obj F ⋙ colim ≅ colim (J := D) (C := E) :=
  NatIso.ofComponents (fun G => colimitIso F G) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, colim_obj, comp_map, whiskeringLeft_obj_map,
      colim_map, colimitIso_hom]
    ext
    simp only [comp_obj, ι_colimMap_assoc, whiskerLeft_app, colimit.ι_pre, colimit.ι_pre_assoc,
      ι_colimMap]

end

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
def colimitCoconeOfComp (t : ColimitCocone (F ⋙ G)) : ColimitCocone G where
  cocone := extendCocone.obj t.cocone
  isColimit := (isColimitExtendCoconeEquiv F _).symm t.isColimit

/-- When `F` is final, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasColimit`.)
-/
theorem hasColimit_of_comp [HasColimit (F ⋙ G)] : HasColimit G :=
  HasColimit.mk (colimitCoconeOfComp F (getColimitCocone (F ⋙ G)))

theorem preservesColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesColimit (F ⋙ G) H] : PreservesColimit G H where
  preserves {c} hc := by
    refine ⟨isColimitWhiskerEquiv F _ ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitWhiskerEquiv F _).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocones.ext (Iso.refl _) (by simp))

theorem reflectsColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsColimit (F ⋙ G) H] : ReflectsColimit G H where
  reflects {c} hc := by
    refine ⟨isColimitWhiskerEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitWhiskerEquiv F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocones.ext (Iso.refl _) (by simp))

/-- If `F` is final and `F ⋙ G` creates colimits of `H`, then so does `G`. -/
def createsColimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesColimit (F ⋙ G) H] : CreatesColimit G H where
  reflects := (reflectsColimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCocone (F := F)).obj (liftColimit ((isColimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedColimitMapsToOriginal (K := (F ⋙ G)) ((isColimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCocone (F := F)).mapIso i) ≪≫ ((coconesEquiv F (G ⋙ H)).counitIso.app _)
    exact Cocones.ext (Iso.refl _)

include F in
theorem hasColimitsOfShape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape D E where
  has_colimit := fun _ => hasColimit_of_comp F

include F in
theorem preservesColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [PreservesColimitsOfShape C H] : PreservesColimitsOfShape D H where
  preservesColimit := preservesColimit_of_comp F

include F in
theorem reflectsColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [ReflectsColimitsOfShape C H] : ReflectsColimitsOfShape D H where
  reflectsColimit := reflectsColimit_of_comp F

include F in
/-- If `H` creates colimits of shape `C` and `F : C ⥤ D` is final, then `H` creates colimits of
shape `D`. -/
def createsColimitsOfShapeOfFinal {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [CreatesColimitsOfShape C H] : CreatesColimitsOfShape D H where
  CreatesColimit := createsColimitOfComp F

end Final

end ArbitraryUniverse

section LocallySmall

variable {C : Type v} [Category.{v} C] {D : Type u₁} [Category.{v} D] (F : C ⥤ D)

namespace Final

theorem zigzag_of_eqvGen_quot_rel {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
    (t : Relation.EqvGen (Types.Quot.Rel.{v, v} (F ⋙ coyoneda.obj (op d))) f₁ f₂) :
    Zigzag (StructuredArrow.mk f₁.2) (StructuredArrow.mk f₂.2) := by
  induction t with
  | rel x y r =>
    obtain ⟨f, w⟩ := r
    fconstructor
    swap
    · fconstructor
    left; fconstructor
    exact StructuredArrow.homMk f
  | refl => fconstructor
  | symm x y _ ih =>
    apply zigzag_symmetric
    exact ih
  | trans x y z _ _ ih₁ ih₂ =>
    apply Relation.ReflTransGen.trans
    · exact ih₁
    · exact ih₂

end Final

/-- If `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit` for all `d : D`, then `F` is final.
-/
theorem final_of_colimit_comp_coyoneda_iso_pUnit
    (I : ∀ d, colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit) : Final F :=
  ⟨fun d => by
    have : Nonempty (StructuredArrow d F) := by
      have := (I d).inv PUnit.unit
      obtain ⟨j, y, rfl⟩ := Limits.Types.jointly_surjective'.{v, v} this
      exact ⟨StructuredArrow.mk y⟩
    apply zigzag_isConnected
    rintro ⟨⟨⟨⟩⟩, X₁, f₁⟩ ⟨⟨⟨⟩⟩, X₂, f₂⟩
    let y₁ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₁ f₁
    let y₂ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₂ f₂
    have e : y₁ = y₂ := by
      apply (I d).toEquiv.injective
      ext
    have t := Types.colimit_eq.{v, v} e
    clear e y₁ y₂
    exact Final.zigzag_of_eqvGen_quot_rel t⟩

/-- A variant of `final_of_colimit_comp_coyoneda_iso_pUnit` where we bind the various claims
    about `colimit (F ⋙ coyoneda.obj (Opposite.op d))` for each `d : D` into a single claim about
    the presheaf `colimit (F ⋙ yoneda)`. -/
theorem final_of_isTerminal_colimit_comp_yoneda
    (h : IsTerminal (colimit (F ⋙ yoneda))) : Final F := by
  refine final_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => ?_)
  refine Types.isTerminalEquivIsoPUnit _ ?_
  let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ h
  exact b.ofIso <| preservesColimitIso ((evaluation _ _).obj (Opposite.op d)) (F ⋙ yoneda)

/-- If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda.obj (op d))`
is an isomorphism (as it always is when `F` is final),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`
(simply because `colimit (coyoneda.obj (op d)) ≅ PUnit`).
-/
def Final.colimitCompCoyonedaIso (d : D) [IsIso (colimit.pre (coyoneda.obj (op d)) F)] :
    colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit :=
  asIso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ Coyoneda.colimitCoyonedaIso (op d)

end LocallySmall

section SmallCategory

variable {C : Type v} [Category.{v} C] {D : Type v} [Category.{v} D] (F : C ⥤ D)

theorem final_iff_isIso_colimit_pre : Final F ↔ ∀ G : D ⥤ Type v, IsIso (colimit.pre G F) :=
  ⟨fun _ => inferInstance,
   fun _ => final_of_colimit_comp_coyoneda_iso_pUnit _ fun _ => Final.colimitCompCoyonedaIso _ _⟩

end SmallCategory

namespace Initial

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) [Initial F]

instance (d : D) : Nonempty (CostructuredArrow F d) :=
  IsConnected.is_nonempty

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is initial, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `F.obj (lift F d) ⟶ d`.
-/
def lift (d : D) : C :=
  (Classical.arbitrary (CostructuredArrow F d)).left

/-- When `F : C ⥤ D` is initial, we denote by `homToLift` an arbitrary choice of morphism
`F.obj (lift F d) ⟶ d`.
-/
def homToLift (d : D) : F.obj (lift F d) ⟶ d :=
  (Classical.arbitrary (CostructuredArrow F d)).hom

/-- We provide an induction principle for reasoning about `lift` and `homToLift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `homToLift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : F.obj X₀ ⟶ d` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : ∀ (X : C) (_ : F.obj X ⟶ d), Sort*)
    (h₁ :
      ∀ (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
        F.map f ≫ k₂ = k₁ → Z X₁ k₁ → Z X₂ k₂)
    (h₂ :
      ∀ (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
        F.map f ≫ k₂ = k₁ → Z X₂ k₂ → Z X₁ k₁)
    {X₀ : C} {k₀ : F.obj X₀ ⟶ d} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d) := by
  apply Nonempty.some
  apply
    @isPreconnected_induction _ _ _ (fun Y : CostructuredArrow F d => Z Y.left Y.hom) _ _
      (CostructuredArrow.mk k₀) z
  · intro j₁ j₂ f a
    fapply h₁ _ _ _ _ f.left _ a
    convert f.w
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.left _ a
    convert f.w
    simp

variable {F G}

/-- Given a cone over `F ⋙ G`, we can construct a `Cone G` with the same cocone point.
-/
@[simps]
def extendCone : Cone (F ⋙ G) ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π :=
        { app := fun d => c.π.app (lift F d) ≫ G.map (homToLift F d)
          naturality := fun X Y f => by
            dsimp; simp only [Category.id_comp, Category.assoc]
            -- This would be true if we'd chosen `lift F Y` to be `lift F X`
            -- and `homToLift F Y` to be `homToLift F X ≫ f`.
            apply
              induction F fun Z k =>
                (c.π.app Z ≫ G.map k : c.pt ⟶ _) =
                  c.π.app (lift F X) ≫ G.map (homToLift F X) ≫ G.map f
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, ← Functor.comp_map, ← Category.assoc, ← Category.assoc,
                c.w] at z
              rw [z, Category.assoc]
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, ← Functor.comp_map, ← Category.assoc, ← Category.assoc,
                c.w, z, Category.assoc]
            · rw [← Functor.map_comp] } }
  map f := { hom := f.hom }

/-- Alternative equational lemma for `(extendCone c).π.app` in case a lift of the object
is given explicitly. -/
lemma extendCone_obj_π_app' (c : Cone (F ⋙ G)) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (extendCone.obj c).π.app Y = c.π.app X ≫ G.map f := by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    c.π.app Z ≫ G.map g = c.π.app X ≫ G.map f
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map, c.π.naturality]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, c.π.naturality, h₂]

@[simp]
theorem limit_cone_comp_aux (s : Cone (F ⋙ G)) (j : C) :
    s.π.app (lift F (F.obj j)) ≫ G.map (homToLift F (F.obj j)) = s.π.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => s.π.app X ≫ G.map k = (s.π.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f]
    rw [← w] at h
    simpa using h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f] at h
    rw [← w]
    simpa using h
  · exact s.w (𝟙 _)

variable (F G)

/-- If `F` is initial,
the category of cones on `F ⋙ G` is equivalent to the category of cones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
def conesEquiv : Cone (F ⋙ G) ≌ Cone G where
  functor := extendCone
  inverse := Cones.whiskering F
  unitIso := NatIso.ofComponents fun c => Cones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cones.ext (Iso.refl _)

variable {G}

/-- When `F : C ⥤ D` is initial, and `t : Cone G` for some `G : D ⥤ E`,
`t.whisker F` is a limit cone exactly when `t` is.
-/
def isLimitWhiskerEquiv (t : Cone G) : IsLimit (t.whisker F) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G).symm

/-- When `F` is initial, and `t : Cone (F ⋙ G)`,
`extendCone.obj t` is a limit cone exactly when `t` is.
-/
def isLimitExtendConeEquiv (t : Cone (F ⋙ G)) : IsLimit (extendCone.obj t) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G)

/-- Given a limit cone over `G : D ⥤ E` we can construct a limit cone over `F ⋙ G`. -/
@[simps]
def limitConeComp (t : LimitCone G) : LimitCone (F ⋙ G) where
  cone := _
  isLimit := (isLimitWhiskerEquiv F _).symm t.isLimit

instance (priority := 100) comp_hasLimit [HasLimit G] : HasLimit (F ⋙ G) :=
  HasLimit.mk (limitConeComp F (getLimitCone G))

instance (priority := 100) comp_preservesLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesLimit G H] : PreservesLimit (F ⋙ G) H where
  preserves {c} hc := by
    refine ⟨isLimitExtendConeEquiv (G := G ⋙ H) F (H.mapCone c) ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitExtendConeEquiv F c).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cones.ext (Iso.refl _) (by simp))

instance (priority := 100) comp_reflectsLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsLimit G H] : ReflectsLimit (F ⋙ G) H where
  reflects {c} hc := by
    refine ⟨isLimitExtendConeEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitExtendConeEquiv (G := G ⋙ H) F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cones.ext (Iso.refl _) (by simp))

instance (priority := 100) compCreatesLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesLimit G H] : CreatesLimit (F ⋙ G) H where
  lifts {c} hc := by
    refine ⟨(liftLimit ((isLimitExtendConeEquiv F (G := G ⋙ H) _).symm hc)).whisker F, ?_⟩
    let i := liftedLimitMapsToOriginal ((isLimitExtendConeEquiv F (G := G ⋙ H) _).symm hc)
    exact (Cones.whiskering F).mapIso i ≪≫ ((conesEquiv F (G ⋙ H)).unitIso.app _).symm

instance limit_pre_isIso [HasLimit G] : IsIso (limit.pre G F) := by
  rw [limit.pre_eq (limitConeComp F (getLimitCone G)) (getLimitCone G)]
  erw [IsLimit.lift_self]
  dsimp
  infer_instance

section

variable (G)

/-- When `F : C ⥤ D` is initial, and `G : D ⥤ E` has a limit, then `F ⋙ G` has a limit also and
`limit (F ⋙ G) ≅ limit G`. -/
@[simps! -isSimp, stacks 04E7]
def limitIso [HasLimit G] : limit (F ⋙ G) ≅ limit G :=
  (asIso (limit.pre G F)).symm

/-- A pointfree version of `limitIso`, stating that whiskering by `F` followed by taking the
limit is isomorpic to taking the limit on the codomain of `F`. -/
def limIso [HasLimitsOfShape D E] [HasLimitsOfShape C E] :
    (whiskeringLeft _ _ _).obj F ⋙ lim ≅ lim (J := D) (C := E) :=
  Iso.symm <| NatIso.ofComponents (fun G => (limitIso F G).symm) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, lim_obj, comp_map, whiskeringLeft_obj_map, lim_map,
      Iso.symm_hom, limitIso_inv]
    ext
    simp

end

/-- Given a limit cone over `F ⋙ G` we can construct a limit cone over `G`. -/
@[simps]
def limitConeOfComp (t : LimitCone (F ⋙ G)) : LimitCone G where
  cone := extendCone.obj t.cone
  isLimit := (isLimitExtendConeEquiv F _).symm t.isLimit

/-- When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasLimit`.)
-/
theorem hasLimit_of_comp [HasLimit (F ⋙ G)] : HasLimit G :=
  HasLimit.mk (limitConeOfComp F (getLimitCone (F ⋙ G)))

theorem preservesLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesLimit (F ⋙ G) H] : PreservesLimit G H where
  preserves {c} hc := by
    refine ⟨isLimitWhiskerEquiv F _ ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitWhiskerEquiv F _).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cones.ext (Iso.refl _) (by simp))

theorem reflectsLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsLimit (F ⋙ G) H] : ReflectsLimit G H where
  reflects {c} hc := by
    refine ⟨isLimitWhiskerEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitWhiskerEquiv F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cones.ext (Iso.refl _) (by simp))

/-- If `F` is initial and `F ⋙ G` creates limits of `H`, then so does `G`. -/
def createsLimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesLimit (F ⋙ G) H] : CreatesLimit G H where
  reflects := (reflectsLimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCone (F := F)).obj (liftLimit ((isLimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedLimitMapsToOriginal (K := (F ⋙ G)) ((isLimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCone (F := F)).mapIso i) ≪≫ ((conesEquiv F (G ⋙ H)).counitIso.app _)
    exact Cones.ext (Iso.refl _)

include F in
theorem hasLimitsOfShape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E where
  has_limit := fun _ => hasLimit_of_comp F

include F in
theorem preservesLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [PreservesLimitsOfShape C H] : PreservesLimitsOfShape D H where
  preservesLimit := preservesLimit_of_comp F

include F in
theorem reflectsLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [ReflectsLimitsOfShape C H] : ReflectsLimitsOfShape D H where
  reflectsLimit := reflectsLimit_of_comp F

include F in
/-- If `H` creates limits of shape `C` and `F : C ⥤ D` is initial, then `H` creates limits of shape
`D`. -/
def createsLimitsOfShapeOfInitial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [CreatesLimitsOfShape C H] : CreatesLimitsOfShape D H where
  CreatesLimit := createsLimitOfComp F

end Initial

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)

/-- The hypotheses also imply that `G` is final, see `final_of_comp_full_faithful'`. -/
theorem final_of_comp_full_faithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where
  out d := isConnected_of_equivalent (StructuredArrow.post d F G).asEquivalence.symm

/-- The hypotheses also imply that `G` is initial, see `initial_of_comp_full_faithful'`. -/
theorem initial_of_comp_full_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where
  out d := isConnected_of_equivalent (CostructuredArrow.post F G d).asEquivalence.symm

/-- See also the strictly more general `final_comp` below. -/
theorem final_comp_equivalence [Final F] [IsEquivalence G] : Final (F ⋙ G) :=
  let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Final ((F ⋙ G) ⋙ G.inv) := final_of_natIso i
  final_of_comp_full_faithful (F ⋙ G) G.inv

/-- See also the strictly more general `initial_comp` below. -/
theorem initial_comp_equivalence [Initial F] [IsEquivalence G] : Initial (F ⋙ G) :=
  let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Initial ((F ⋙ G) ⋙ G.inv) := initial_of_natIso i
  initial_of_comp_full_faithful (F ⋙ G) G.inv

/-- See also the strictly more general `final_comp` below. -/
theorem final_equivalence_comp [IsEquivalence F] [Final G] : Final (F ⋙ G) where
  out d := isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence.symm

/-- See also the strictly more general `initial_comp` below. -/
theorem initial_equivalence_comp [IsEquivalence F] [Initial G] : Initial (F ⋙ G) where
  out d := isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence.symm

/-- See also the strictly more general `final_of_final_comp` below. -/
theorem final_of_equivalence_comp [IsEquivalence F] [Final (F ⋙ G)] : Final G where
  out d := isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence

/-- See also the strictly more general `initial_of_initial_comp` below. -/
theorem initial_of_equivalence_comp [IsEquivalence F] [Initial (F ⋙ G)] : Initial G where
  out d := isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence

/-- See also the strictly more general `final_iff_comp_final_full_faithful` below. -/
theorem final_iff_comp_equivalence [IsEquivalence G] : Final F ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp_equivalence _ _, fun _ => final_of_comp_full_faithful _ G⟩

/-- See also the strictly more general `final_iff_final_comp` below. -/
theorem final_iff_equivalence_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_equivalence_comp _ _, fun _ => final_of_equivalence_comp F _⟩

/-- See also the strictly more general `initial_iff_comp_initial_full_faithful` below. -/
theorem initial_iff_comp_equivalence [IsEquivalence G] : Initial F ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp_equivalence _ _, fun _ => initial_of_comp_full_faithful _ G⟩

/-- See also the strictly more general `initial_iff_initial_comp` below. -/
theorem initial_iff_equivalence_comp [IsEquivalence F] : Initial G ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_equivalence_comp _ _, fun _ => initial_of_equivalence_comp F _⟩

instance final_comp [hF : Final F] [hG : Final G] : Final (F ⋙ G) := by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G ⋙ s₃.functor) :=
    isoWhiskerLeft (s₁.inverse ⋙ F) (isoWhiskerRight s₂.unitIso (G ⋙ s₃.functor))
  rw [final_iff_comp_equivalence (F ⋙ G) s₃.functor, final_iff_equivalence_comp s₁.inverse,
    final_natIso_iff i, final_iff_isIso_colimit_pre]
  rw [final_iff_comp_equivalence F s₂.functor, final_iff_equivalence_comp s₁.inverse,
    final_iff_isIso_colimit_pre] at hF
  rw [final_iff_comp_equivalence G s₃.functor, final_iff_equivalence_comp s₂.inverse,
    final_iff_isIso_colimit_pre] at hG
  intro H
  rw [← colimit.pre_pre]
  infer_instance

instance initial_comp [Initial F] [Initial G] : Initial (F ⋙ G) := by
  suffices Final (F ⋙ G).op from initial_of_final_op _
  exact final_comp F.op G.op

theorem final_of_final_comp [hF : Final F] [hFG : Final (F ⋙ G)] : Final G := by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let _i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G ⋙ s₃.functor) :=
    isoWhiskerLeft (s₁.inverse ⋙ F) (isoWhiskerRight s₂.unitIso (G ⋙ s₃.functor))
  rw [final_iff_comp_equivalence G s₃.functor, final_iff_equivalence_comp s₂.inverse,
    final_iff_isIso_colimit_pre]
  rw [final_iff_comp_equivalence F s₂.functor, final_iff_equivalence_comp s₁.inverse,
    final_iff_isIso_colimit_pre] at hF
  rw [final_iff_comp_equivalence (F ⋙ G) s₃.functor, final_iff_equivalence_comp s₁.inverse,
    final_natIso_iff _i, final_iff_isIso_colimit_pre] at hFG
  intro H
  replace hFG := hFG H
  rw [← colimit.pre_pre] at hFG
  exact IsIso.of_isIso_comp_left (colimit.pre _ (s₁.inverse ⋙ F ⋙ s₂.functor)) _

theorem initial_of_initial_comp [Initial F] [Initial (F ⋙ G)] : Initial G := by
  suffices Final G.op from initial_of_final_op _
  have : Final (F.op ⋙ G.op) := show Final (F ⋙ G).op from inferInstance
  exact final_of_final_comp F.op G.op

/-- The hypotheses also imply that `F` is final, see `final_of_comp_full_faithful`. -/
theorem final_of_comp_full_faithful' [Full G] [Faithful G] [Final (F ⋙ G)] : Final G :=
  have := final_of_comp_full_faithful F G
  final_of_final_comp F G

/-- The hypotheses also imply that `F` is initial, see `initial_of_comp_full_faithful`. -/
theorem initial_of_comp_full_faithful' [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial G :=
  have := initial_of_comp_full_faithful F G
  initial_of_initial_comp F G

theorem final_iff_comp_final_full_faithful [Final G] [Full G] [Faithful G] :
    Final F ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp _ _, fun _ => final_of_comp_full_faithful F G⟩

theorem initial_iff_comp_initial_full_faithful [Initial G] [Full G] [Faithful G] :
    Initial F ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp _ _, fun _ => initial_of_comp_full_faithful F G⟩

theorem final_iff_final_comp [Final F] : Final G ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp _ _, fun _ => final_of_final_comp F G⟩

theorem initial_iff_initial_comp [Initial F] : Initial G ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp _ _, fun _ => initial_of_initial_comp F G⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] {c : C}

lemma final_fromPUnit_of_isTerminal (hc : Limits.IsTerminal c) : (fromPUnit c).Final where
  out c' := by
    letI : Inhabited (StructuredArrow c' (fromPUnit c)) := ⟨.mk (Y := default) (hc.from c')⟩
    letI : Subsingleton (StructuredArrow c' (fromPUnit c)) :=
      ⟨fun i j ↦ StructuredArrow.obj_ext _ _ (by aesop_cat) (hc.hom_ext _ _)⟩
    infer_instance

lemma initial_fromPUnit_of_isInitial (hc : Limits.IsInitial c) : (fromPUnit c).Initial where
  out c' := by
    letI : Inhabited (CostructuredArrow (fromPUnit c) c') := ⟨.mk (Y := default) (hc.to c')⟩
    letI : Subsingleton (CostructuredArrow (fromPUnit c) c') :=
      ⟨fun i j ↦ CostructuredArrow.obj_ext _ _ (by aesop_cat) (hc.hom_ext _ _)⟩
    infer_instance

end

end Functor

section Filtered
open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Final functors preserve filteredness.

This can be seen as a generalization of `IsFiltered.of_right_adjoint` (which states that right
adjoints preserve filteredness), as right adjoints are always final, see `final_of_adjunction`.
-/
theorem IsFilteredOrEmpty.of_final (F : C ⥤ D) [Final F] [IsFilteredOrEmpty C] :
    IsFilteredOrEmpty D where
  cocone_objs X Y := ⟨F.obj (IsFiltered.max (Final.lift F X) (Final.lift F Y)),
    Final.homToLift F X ≫ F.map (IsFiltered.leftToMax _ _),
    ⟨Final.homToLift F Y ≫ F.map (IsFiltered.rightToMax _ _), trivial⟩⟩
  cocone_maps {X Y} f g := by
    let P : StructuredArrow X F → Prop := fun h => ∃ (Z : C) (q₁ : h.right ⟶ Z)
      (q₂ : Final.lift F Y ⟶ Z), h.hom ≫ F.map q₁ = f ≫ Final.homToLift F Y ≫ F.map q₂
    rsuffices ⟨Z, q₁, q₂, h⟩ : Nonempty (P (StructuredArrow.mk (g ≫ Final.homToLift F Y)))
    · refine ⟨F.obj (IsFiltered.coeq q₁ q₂),
        Final.homToLift F Y ≫ F.map (q₁ ≫ IsFiltered.coeqHom q₁ q₂), ?_⟩
      conv_lhs => rw [IsFiltered.coeq_condition]
      simp only [F.map_comp, ← reassoc_of% h, StructuredArrow.mk_hom_eq_self, Category.assoc]
    have h₀ : P (StructuredArrow.mk (f ≫ Final.homToLift F Y)) := ⟨_, 𝟙 _, 𝟙 _, by simp⟩
    refine isPreconnected_induction P ?_ ?_ h₀ _
    · rintro U V h ⟨Z, q₁, q₂, hq⟩
      obtain ⟨W, q₃, q₄, hq'⟩ := IsFiltered.span q₁ h.right
      refine ⟨W, q₄, q₂ ≫ q₃, ?_⟩
      rw [F.map_comp, ← reassoc_of% hq, ← F.map_comp, hq', F.map_comp, StructuredArrow.w_assoc]
    · rintro U V h ⟨Z, q₁, q₂, hq⟩
      exact ⟨Z, h.right ≫ q₁, q₂, by simp only [F.map_comp, StructuredArrow.w_assoc, hq]⟩

/-- Final functors preserve filteredness.

This can be seen as a generalization of `IsFiltered.of_right_adjoint` (which states that right
adjoints preserve filteredness), as right adjoints are always final, see `final_of_adjunction`.
-/
theorem IsFiltered.of_final (F : C ⥤ D) [Final F] [IsFiltered C] : IsFiltered D :=
{ IsFilteredOrEmpty.of_final F with
  nonempty := Nonempty.map F.obj IsFiltered.nonempty }

/-- Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which states that left
adjoints preserve cofilteredness), as right adjoints are always initial,
see `initial_of_adjunction`.
-/
theorem IsCofilteredOrEmpty.of_initial (F : C ⥤ D) [Initial F] [IsCofilteredOrEmpty C] :
    IsCofilteredOrEmpty D :=
  have : IsFilteredOrEmpty Dᵒᵖ := IsFilteredOrEmpty.of_final F.op
  isCofilteredOrEmpty_of_isFilteredOrEmpty_op _

/-- Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which states that left
adjoints preserve cofilteredness), as right adjoints are always initial,
see `initial_of_adjunction`.
-/
theorem IsCofiltered.of_initial (F : C ⥤ D) [Initial F] [IsCofiltered C] : IsCofiltered D :=
  have : IsFiltered Dᵒᵖ := IsFiltered.of_final F.op
  isCofiltered_of_isFiltered_op _

end Filtered

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

open Functor

/-- The functor `StructuredArrow.pre X T S` is final if `T` is final. -/
instance StructuredArrow.final_pre (T : C ⥤ D) [Final T] (S : D ⥤ E) (X : E) :
    Final (pre X T S) := by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (StructuredArrow.preEquivalence T f)]
  exact Final.out f.right

/-- The functor `CostructuredArrow.pre X T S` is initial if `T` is initial. -/
instance CostructuredArrow.initial_pre (T : C ⥤ D) [Initial T] (S : D ⥤ E) (X : E) :
    Initial (CostructuredArrow.pre T S X) := by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (CostructuredArrow.preEquivalence T f)]
  exact Initial.out f.left

end

section Grothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : D ⥤ Cat) (G : C ⥤ D)

open Functor

set_option backward.dsimp.proofs true in
/-- A prefunctor mapping structured arrows on `G` to structured arrows on `pre F G` with their
action on fibers being the identity. -/
def Grothendieck.structuredArrowToStructuredArrowPre (d : D) (f : F.obj d) :
    StructuredArrow d G ⥤q StructuredArrow ⟨d, f⟩ (pre F G) where
  obj := fun X => StructuredArrow.mk (Y := ⟨X.right, (F.map X.hom).obj f⟩)
    (Grothendieck.Hom.mk (by exact X.hom) (by dsimp; exact 𝟙 _))
  map := fun g => StructuredArrow.homMk
    (Grothendieck.Hom.mk (by exact g.right)
      (eqToHom (by dsimp; rw [← StructuredArrow.w g, map_comp, Cat.comp_obj])))
    (by simp only [StructuredArrow.mk_right]
        apply Grothendieck.ext <;> simp)

instance Grothendieck.final_pre [hG : Final G] : (Grothendieck.pre F G).Final := by
  constructor
  rintro ⟨d, f⟩
  let ⟨u, c, g⟩ : Nonempty (StructuredArrow d G) := inferInstance
  letI :  Nonempty (StructuredArrow ⟨d, f⟩ (pre F G)) :=
    ⟨u, ⟨c, (F.map g).obj f⟩, ⟨(by exact g), (by exact 𝟙 _)⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨⟨⟩⟩, ⟨bi, fi⟩, ⟨gbi, gfi⟩⟩ ⟨⟨⟨⟩⟩, ⟨bj, fj⟩, ⟨gbj, gfj⟩⟩
  dsimp at fj fi gfi gbi gbj gfj
  apply Zigzag.trans (j₂ := StructuredArrow.mk (Y := ⟨bi, ((F.map gbi).obj f)⟩)
      (Grothendieck.Hom.mk gbi (𝟙 _)))
    (.of_zag (.inr ⟨StructuredArrow.homMk (Grothendieck.Hom.mk (by dsimp; exact 𝟙 _)
      (eqToHom (by simp) ≫ gfi)) (by apply Grothendieck.ext <;> simp)⟩))
  refine Zigzag.trans (j₂ := StructuredArrow.mk (Y := ⟨bj, ((F.map gbj).obj f)⟩)
      (Grothendieck.Hom.mk gbj (𝟙 _))) ?_
    (.of_zag (.inl ⟨StructuredArrow.homMk (Grothendieck.Hom.mk (by dsimp; exact 𝟙 _)
      (eqToHom (by simp) ≫ gfj)) (by apply Grothendieck.ext <;> simp)⟩))
  exact zigzag_prefunctor_obj_of_zigzag (Grothendieck.structuredArrowToStructuredArrowPre F G d f)
    (isPreconnected_zigzag (.mk gbi) (.mk gbj))

open Limits

/-- A natural transformation `α : F ⟶ G` between functors `F G : C ⥤ Cat` which is is final on each
fiber `(α.app X)` induces an equivalence of fiberwise colimits of `map α ⋙ H` and `H` for each
functor `H : Grothendieck G ⥤ Type`. -/
def Grothendieck.fiberwiseColimitMapCompEquivalence {C : Type u₁} [Category.{v₁} C]
    {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) [∀ X, Final (α.app X)] (H : Grothendieck G ⥤ Type u₂) :
    fiberwiseColimit (map α ⋙ H) ≅ fiberwiseColimit H :=
  NatIso.ofComponents
    (fun X =>
      HasColimit.isoOfNatIso ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (ιCompMap α X) H ≪≫  Functor.associator _ _ _) ≪≫
      Final.colimitIso (α.app X) (ι G X ⋙ H))
    (fun f => colimit.hom_ext <| fun d => by
      simp only [map, Cat.comp_obj, comp_obj, ι_obj, fiberwiseColimit_obj, fiberwiseColimit_map,
        ιNatTrans, ιCompMap, Iso.trans_hom, Category.assoc, ι_colimMap_assoc, NatTrans.comp_app,
        whiskerRight_app, Functor.comp_map, Cat.eqToHom_app, map_id, Category.comp_id,
        associator_hom_app, colimit.ι_pre_assoc, HasColimit.isoOfNatIso_ι_hom_assoc, Iso.symm_hom,
        isoWhiskerRight_hom, associator_inv_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
        Final.ι_colimitIso_hom, Category.id_comp, Final.ι_colimitIso_hom_assoc, colimit.ι_pre]
      have := Functor.congr_obj (α.naturality f) d
      dsimp at this
      congr
      apply eqToHom_heq_id_dom)

/-- This is the small version of the more general lemma `Grothendieck.final_map` below. -/
private lemma Grothendieck.final_map_small {C : Type u₁} [SmallCategory C] {F G : C ⥤ Cat.{u₁, u₁}}
    (α : F ⟶ G) [hα : ∀ X, Final (α.app X)] : Final (map α) := by
  rw [final_iff_isIso_colimit_pre]
  intro H
  let i := (colimitFiberwiseColimitIso _).symm ≪≫
    HasColimit.isoOfNatIso (fiberwiseColimitMapCompEquivalence α H) ≪≫ colimitFiberwiseColimitIso _
  convert Iso.isIso_hom i
  apply colimit.hom_ext
  intro X
  simp [i, fiberwiseColimitMapCompEquivalence]

/-- The functor `Grothendieck.map α` for a natural transformation `α : F ⟶ G`, with
`F G : C ⥤ Cat`, is final if for each `X : C`, the functor `α.app X` is final. -/
lemma Grothendieck.final_map {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) [hα : ∀ X, Final (α.app X)] :
    Final (map α) := by
  let sC : C ≌ AsSmall.{max u₁ u₂ v₁ v₂} C := AsSmall.equiv
  let F' : AsSmall C ⥤ Cat := sC.inverse ⋙ F ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let G' : AsSmall C ⥤ Cat := sC.inverse ⋙ G ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let α' : F' ⟶ G' := whiskerLeft _ (whiskerRight α _)
  have : ∀ X, Final (α'.app X) := fun X =>
    inferInstanceAs (AsSmall.equiv.inverse ⋙ _ ⋙ AsSmall.equiv.functor).Final
  have hα' : (map α').Final := final_map_small _
  dsimp only [α', ← Equivalence.symm_functor] at hα'
  have i := mapWhiskerLeftIsoConjPreMap sC.symm (whiskerRight α Cat.asSmallFunctor)
    ≪≫ isoWhiskerLeft _ (isoWhiskerRight (mapWhiskerRightAsSmallFunctor α) _)
  have := final_of_natIso i
  rwa [← final_iff_equivalence_comp, ← final_iff_comp_equivalence,
    ← final_iff_equivalence_comp, ← final_iff_comp_equivalence] at this

end Grothendieck

section Prod

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable (F : C ⥤ D) (G : C' ⥤ D')

instance [F.Final] [G.Final] : (F.prod G).Final where
  out := fun ⟨d, d'⟩ => isConnected_of_equivalent (StructuredArrow.prodEquivalence d d' F G).symm

end Prod

end CategoryTheory
