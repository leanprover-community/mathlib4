/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.PUnit

#align_import category_theory.limits.final from "leanprover-community/mathlib"@"8a318021995877a44630c898d0b2bc376fceef3b"

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

From 3., we prove 1. directly in `cofinal_of_colimit_comp_coyoneda_iso_pUnit`.

Dually, we prove that if a functor `F : C ⥤ D` is initial, then any functor `G : D ⥤ E` has a
limit if and only if `F ⋙ G` does, and these limits are isomorphic via `limit.pre G F`.


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

universe v v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open Opposite

open CategoryTheory.Limits

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/--
A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected.

See <https://stacks.math.columbia.edu/tag/04E6>
-/
class Final (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (StructuredArrow d F)
#align category_theory.functor.final CategoryTheory.Functor.Final

attribute [instance] Final.out

/-- A functor `F : C ⥤ D` is initial if for every `d : D`, the comma category of morphisms
`F.obj c ⟶ d` is connected.
-/
class Initial (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (CostructuredArrow F d)
#align category_theory.functor.initial CategoryTheory.Functor.Initial

attribute [instance] Initial.out

instance final_op_of_initial (F : C ⥤ D) [Initial F] : Final F.op where
  out d := isConnected_of_equivalent (costructuredArrowOpEquivalence F (unop d))
#align category_theory.functor.final_op_of_initial CategoryTheory.Functor.final_op_of_initial

instance initial_op_of_final (F : C ⥤ D) [Final F] : Initial F.op where
  out d := isConnected_of_equivalent (structuredArrowOpEquivalence F (unop d))
#align category_theory.functor.initial_op_of_final CategoryTheory.Functor.initial_op_of_final

theorem final_of_initial_op (F : C ⥤ D) [Initial F.op] : Final F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (structuredArrowOpEquivalence F d).symm) }
#align category_theory.functor.final_of_initial_op CategoryTheory.Functor.final_of_initial_op

theorem initial_of_final_op (F : C ⥤ D) [Final F.op] : Initial F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (costructuredArrowOpEquivalence F d).symm) }
#align category_theory.functor.initial_of_final_op CategoryTheory.Functor.initial_of_final_op

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
#align category_theory.functor.final_of_adjunction CategoryTheory.Functor.final_of_adjunction

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
#align category_theory.functor.initial_of_adjunction CategoryTheory.Functor.initial_of_adjunction

instance (priority := 100) final_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] : Final F :=
  final_of_adjunction (Adjunction.ofIsRightAdjoint F)
#align category_theory.functor.final_of_is_right_adjoint CategoryTheory.Functor.final_of_isRightAdjoint

instance (priority := 100) initial_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] : Initial F :=
  initial_of_adjunction (Adjunction.ofIsLeftAdjoint F)
#align category_theory.functor.initial_of_is_left_adjoint CategoryTheory.Functor.initial_of_isLeftAdjoint

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
When `F : C ⥤ D` is cofinal, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
def lift (d : D) : C :=
  (Classical.arbitrary (StructuredArrow d F)).right
#align category_theory.functor.final.lift CategoryTheory.Functor.Final.lift

/-- When `F : C ⥤ D` is cofinal, we denote by `homToLift` an arbitrary choice of morphism
`d ⟶ F.obj (lift F d)`.
-/
def homToLift (d : D) : d ⟶ F.obj (lift F d) :=
  (Classical.arbitrary (StructuredArrow d F)).hom
#align category_theory.functor.final.hom_to_lift CategoryTheory.Functor.Final.homToLift

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
    dsimp
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.right _ a
    convert f.w.symm
    dsimp
    simp
#align category_theory.functor.final.induction CategoryTheory.Functor.Final.induction

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
            dsimp; simp
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
#align category_theory.functor.final.extend_cocone CategoryTheory.Functor.Final.extendCocone

@[simp]
theorem colimit_cocone_comp_aux (s : Cocone (F ⋙ G)) (j : C) :
    G.map (homToLift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) = s.ι.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => G.map k ≫ s.ι.app X = (s.ι.app j : _)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w]
    rw [← s.w f] at h
    simpa using h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w] at h
    rw [← s.w f]
    simpa using h
  · exact s.w (𝟙 _)
#align category_theory.functor.final.colimit_cocone_comp_aux CategoryTheory.Functor.Final.colimit_cocone_comp_aux

variable (F G)

/-- If `F` is cofinal,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
def coconesEquiv : Cocone (F ⋙ G) ≌ Cocone G where
  functor := extendCocone
  inverse := Cocones.whiskering F
  unitIso := NatIso.ofComponents fun c => Cocones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cocones.ext (Iso.refl _)
#align category_theory.functor.final.cocones_equiv CategoryTheory.Functor.Final.coconesEquiv

variable {G}

/-- When `F : C ⥤ D` is cofinal, and `t : Cocone G` for some `G : D ⥤ E`,
`t.whisker F` is a colimit cocone exactly when `t` is.
-/
def isColimitWhiskerEquiv (t : Cocone G) : IsColimit (t.whisker F) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G).symm
#align category_theory.functor.final.is_colimit_whisker_equiv CategoryTheory.Functor.Final.isColimitWhiskerEquiv

/-- When `F` is cofinal, and `t : Cocone (F ⋙ G)`,
`extendCocone.obj t` is a colimit cocone exactly when `t` is.
-/
def isColimitExtendCoconeEquiv (t : Cocone (F ⋙ G)) :
    IsColimit (extendCocone.obj t) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G)
#align category_theory.functor.final.is_colimit_extend_cocone_equiv CategoryTheory.Functor.Final.isColimitExtendCoconeEquiv

/-- Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
def colimitCoconeComp (t : ColimitCocone G) : ColimitCocone (F ⋙ G) where
  cocone := _
  isColimit := (isColimitWhiskerEquiv F _).symm t.isColimit
#align category_theory.functor.final.colimit_cocone_comp CategoryTheory.Functor.Final.colimitCoconeComp

instance (priority := 100) comp_hasColimit [HasColimit G] : HasColimit (F ⋙ G) :=
  HasColimit.mk (colimitCoconeComp F (getColimitCocone G))
#align category_theory.functor.final.comp_has_colimit CategoryTheory.Functor.Final.comp_hasColimit

instance colimit_pre_isIso [HasColimit G] : IsIso (colimit.pre G F) := by
  rw [colimit.pre_eq (colimitCoconeComp F (getColimitCocone G)) (getColimitCocone G)]
  erw [IsColimit.desc_self]
  dsimp
  infer_instance
#align category_theory.functor.final.colimit_pre_is_iso CategoryTheory.Functor.Final.colimit_pre_isIso

section

variable (G)

/-- When `F : C ⥤ D` is cofinal, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimitIso [HasColimit G] : colimit (F ⋙ G) ≅ colimit G :=
  asIso (colimit.pre G F)
#align category_theory.functor.final.colimit_iso CategoryTheory.Functor.Final.colimitIso

end

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
def colimitCoconeOfComp (t : ColimitCocone (F ⋙ G)) : ColimitCocone G where
  cocone := extendCocone.obj t.cocone
  isColimit := (isColimitExtendCoconeEquiv F _).symm t.isColimit
#align category_theory.functor.final.colimit_cocone_of_comp CategoryTheory.Functor.Final.colimitCoconeOfComp

/-- When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasColimit`.)
-/
theorem hasColimit_of_comp [HasColimit (F ⋙ G)] : HasColimit G :=
  HasColimit.mk (colimitCoconeOfComp F (getColimitCocone (F ⋙ G)))
#align category_theory.functor.final.has_colimit_of_comp CategoryTheory.Functor.Final.hasColimit_of_comp

theorem hasColimitsOfShape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape D E where
  has_colimit := fun _ => hasColimit_of_comp F

section

-- Porting note: this instance does not seem to be found automatically
--attribute [local instance] hasColimit_of_comp

/-- When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimitIso' [HasColimit (F ⋙ G)] :
    haveI : HasColimit G := hasColimit_of_comp F;
    colimit (F ⋙ G) ≅ colimit G :=
  haveI : HasColimit G := hasColimit_of_comp F;
  asIso (colimit.pre G F)
#align category_theory.functor.final.colimit_iso' CategoryTheory.Functor.Final.colimitIso'

end

end Final

end ArbitraryUniverse

section LocallySmall

variable {C : Type v} [Category.{v} C] {D : Type u₁} [Category.{v} D] (F : C ⥤ D)

namespace Final

theorem zigzag_of_eqvGen_quot_rel {F : C ⥤ D} {d : D} {f₁ f₂ : ΣX, d ⟶ F.obj X}
    (t : EqvGen (Types.Quot.Rel.{v, v} (F ⋙ coyoneda.obj (op d))) f₁ f₂) :
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
#align category_theory.functor.final.zigzag_of_eqv_gen_quot_rel CategoryTheory.Functor.Final.zigzag_of_eqvGen_quot_rel

end Final

/-- If `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit` for all `d : D`, then `F` is cofinal.
-/
theorem cofinal_of_colimit_comp_coyoneda_iso_pUnit
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
#align category_theory.functor.final.cofinal_of_colimit_comp_coyoneda_iso_punit CategoryTheory.Functor.cofinal_of_colimit_comp_coyoneda_iso_pUnit

/-- A variant of `cofinal_of_colimit_comp_coyoneda_iso_pUnit` where we bind the various claims
    about `colimit (F ⋙ coyoneda.obj (Opposite.op d))` for each `d : D` into a single claim about
    the presheaf `colimit (F ⋙ yoneda)`. -/
theorem cofinal_of_isTerminal_colimit_comp_yoneda
    (h : IsTerminal (colimit (F ⋙ yoneda))) : Final F := by
  refine cofinal_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => ?_)
  refine Types.isTerminalEquivIsoPUnit _ ?_
  let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ h
  exact b.ofIso <| preservesColimitIso ((evaluation _ _).obj (Opposite.op d)) (F ⋙ yoneda)

/-- If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda.obj (op d))`
is an isomorphism (as it always is when `F` is cofinal),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`
(simply because `colimit (coyoneda.obj (op d)) ≅ PUnit`).
-/
def Final.colimitCompCoyonedaIso (d : D) [IsIso (colimit.pre (coyoneda.obj (op d)) F)] :
    colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit :=
  asIso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ Coyoneda.colimitCoyonedaIso (op d)
#align category_theory.functor.final.colimit_comp_coyoneda_iso CategoryTheory.Functor.Final.colimitCompCoyonedaIso

end LocallySmall

section SmallCategory

variable {C : Type v} [Category.{v} C] {D : Type v} [Category.{v} D] (F : C ⥤ D)

theorem final_iff_isIso_colimit_pre : Final F ↔ ∀ G : D ⥤ Type v, IsIso (colimit.pre G F) :=
  ⟨fun _ => inferInstance,
   fun _ => cofinal_of_colimit_comp_coyoneda_iso_pUnit _ fun _ => Final.colimitCompCoyonedaIso _ _⟩

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
#align category_theory.functor.initial.lift CategoryTheory.Functor.Initial.lift

/-- When `F : C ⥤ D` is initial, we denote by `homToLift` an arbitrary choice of morphism
`F.obj (lift F d) ⟶ d`.
-/
def homToLift (d : D) : F.obj (lift F d) ⟶ d :=
  (Classical.arbitrary (CostructuredArrow F d)).hom
#align category_theory.functor.initial.hom_to_lift CategoryTheory.Functor.Initial.homToLift

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
    dsimp
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.left _ a
    convert f.w
    dsimp
    simp
#align category_theory.functor.initial.induction CategoryTheory.Functor.Initial.induction

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
            dsimp; simp
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
#align category_theory.functor.initial.extend_cone CategoryTheory.Functor.Initial.extendCone

@[simp]
theorem limit_cone_comp_aux (s : Cone (F ⋙ G)) (j : C) :
    s.π.app (lift F (F.obj j)) ≫ G.map (homToLift F (F.obj j)) = s.π.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => s.π.app X ≫ G.map k = (s.π.app j : _)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f]
    rw [← w] at h
    simpa using h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f] at h
    rw [← w]
    simpa using h
  · exact s.w (𝟙 _)
#align category_theory.functor.initial.limit_cone_comp_aux CategoryTheory.Functor.Initial.limit_cone_comp_aux

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
#align category_theory.functor.initial.cones_equiv CategoryTheory.Functor.Initial.conesEquiv

variable {G}

/-- When `F : C ⥤ D` is initial, and `t : Cone G` for some `G : D ⥤ E`,
`t.whisker F` is a limit cone exactly when `t` is.
-/
def isLimitWhiskerEquiv (t : Cone G) : IsLimit (t.whisker F) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G).symm
#align category_theory.functor.initial.is_limit_whisker_equiv CategoryTheory.Functor.Initial.isLimitWhiskerEquiv

/-- When `F` is initial, and `t : Cone (F ⋙ G)`,
`extendCone.obj t` is a limit cone exactly when `t` is.
-/
def isLimitExtendConeEquiv (t : Cone (F ⋙ G)) : IsLimit (extendCone.obj t) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G)
#align category_theory.functor.initial.is_limit_extend_cone_equiv CategoryTheory.Functor.Initial.isLimitExtendConeEquiv

/-- Given a limit cone over `G : D ⥤ E` we can construct a limit cone over `F ⋙ G`. -/
@[simps]
def limitConeComp (t : LimitCone G) : LimitCone (F ⋙ G) where
  cone := _
  isLimit := (isLimitWhiskerEquiv F _).symm t.isLimit
#align category_theory.functor.initial.limit_cone_comp CategoryTheory.Functor.Initial.limitConeComp

instance (priority := 100) comp_hasLimit [HasLimit G] : HasLimit (F ⋙ G) :=
  HasLimit.mk (limitConeComp F (getLimitCone G))
#align category_theory.functor.initial.comp_has_limit CategoryTheory.Functor.Initial.comp_hasLimit

instance limit_pre_isIso [HasLimit G] : IsIso (limit.pre G F) := by
  rw [limit.pre_eq (limitConeComp F (getLimitCone G)) (getLimitCone G)]
  erw [IsLimit.lift_self]
  dsimp
  infer_instance
#align category_theory.functor.initial.limit_pre_is_iso CategoryTheory.Functor.Initial.limit_pre_isIso

section

variable (G)

/-- When `F : C ⥤ D` is initial, and `G : D ⥤ E` has a limit, then `F ⋙ G` has a limit also and
`limit (F ⋙ G) ≅ limit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def limitIso [HasLimit G] : limit (F ⋙ G) ≅ limit G :=
  (asIso (limit.pre G F)).symm
#align category_theory.functor.initial.limit_iso CategoryTheory.Functor.Initial.limitIso

end

/-- Given a limit cone over `F ⋙ G` we can construct a limit cone over `G`. -/
@[simps]
def limitConeOfComp (t : LimitCone (F ⋙ G)) : LimitCone G where
  cone := extendCone.obj t.cone
  isLimit := (isLimitExtendConeEquiv F _).symm t.isLimit
#align category_theory.functor.initial.limit_cone_of_comp CategoryTheory.Functor.Initial.limitConeOfComp

/-- When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasLimit`.)
-/
theorem hasLimit_of_comp [HasLimit (F ⋙ G)] : HasLimit G :=
  HasLimit.mk (limitConeOfComp F (getLimitCone (F ⋙ G)))
#align category_theory.functor.initial.has_limit_of_comp CategoryTheory.Functor.Initial.hasLimit_of_comp

theorem hasLimitsOfShape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E where
  has_limit := fun _ => hasLimit_of_comp F

section

-- Porting note: this instance does not seem to be found automatically
-- attribute [local instance] hasLimit_of_comp

/-- When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also and
`limit (F ⋙ G) ≅ limit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def limitIso' [HasLimit (F ⋙ G)] :
    haveI : HasLimit G := hasLimit_of_comp F;
    limit (F ⋙ G) ≅ limit G :=
  haveI : HasLimit G := hasLimit_of_comp F;
  (asIso (limit.pre G F)).symm
#align category_theory.functor.initial.limit_iso' CategoryTheory.Functor.Initial.limitIso'

end

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

/-- See also the strictly more general `inital_comp` below. -/
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
adjoints preserve cofilteredness), as right adjoints are always initial, see `intial_of_adjunction`.
-/
theorem IsCofilteredOrEmpty.of_initial (F : C ⥤ D) [Initial F] [IsCofilteredOrEmpty C] :
    IsCofilteredOrEmpty D :=
  have : IsFilteredOrEmpty Dᵒᵖ := IsFilteredOrEmpty.of_final F.op
  isCofilteredOrEmpty_of_isFilteredOrEmpty_op _

/-- Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which states that left
adjoints preserve cofilteredness), as right adjoints are always initial, see `intial_of_adjunction`.
-/
theorem IsCofiltered.of_initial (F : C ⥤ D) [Initial F] [IsCofiltered C] : IsCofiltered D :=
  have : IsFiltered Dᵒᵖ := IsFiltered.of_final F.op
  isCofiltered_of_isFiltered_op _

end Filtered

end CategoryTheory
