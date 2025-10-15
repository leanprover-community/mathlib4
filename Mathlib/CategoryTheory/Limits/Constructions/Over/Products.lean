/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_widePullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `Over B` has `J`-indexed products.

Note that the binary case is done separately to ensure defeqs with the pullback in the base
category.

## TODO

* Generalise from arbitrary products to arbitrary limits. This is done in Toric.
* Dualise to get the `Under X` results.
-/


universe w v u -- morphism levels before object levels. See note [category_theory universes].

open CategoryTheory CategoryTheory.Limits

variable {J : Type w}
variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/-!
### Binary products

In this section we construct binary products in `Over X` and binary coproducts in `Under X`
explicitly as the pullbacks and pushouts of binary (co)fans in the base category.

For `Over X`, one could construct these binary products from the general theory of arbitrary
products from the next section, i.e.
```
(Cones.postcomposeEquivalence (diagramIsoCospan _).symm).trans
  (Over.ConstructProducts.conesEquiv _ (pair (Over.mk f) (Over.mk g)))
```
but this gives worse defeqs.

For `Under X`, there is currently no general theory of arbitrary coproducts.
-/

namespace CategoryTheory.Limits
section Over
variable {f : Y ⟶ X} {g : Z ⟶ X}

/-- Pullback cones to `X` are the same thing as binary fans in `Over X`. -/
@[simps]
def pullbackConeEquivBinaryFan : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk g) where
  functor.obj c := .mk (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk f) c.fst rfl)
      (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk g) c.snd c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Over.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := PullbackCone.mk c.fst.left c.snd.left (c.fst.w.trans c.snd.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.left
    w := by rintro (_ | _ | _) <;> simp [← Over.comp_left_assoc, ← Over.comp_left]
  }
  unitIso := NatIso.ofComponents (fun c ↦ c.eta) (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun X ↦ BinaryFan.ext (Over.isoMk (Iso.refl _)
    (by simpa using X.fst.w.symm)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp [BinaryFan.ext])
  functor_unitIso_comp c := by ext; simp [BinaryFan.ext]

/-- A binary fan in `Over X` is a limit if its corresponding pullback cone to `X` is a limit. -/
-- `IsLimit.ofConeEquiv` isn't used here because the lift it defines is `𝟙 _ ≫ pullback.lift`.
-- TODO: Define `IsLimit.copy`?
@[simps!]
def IsLimit.pullbackConeEquivBinaryFanFunctor {c : PullbackCone f g} (hc : IsLimit c) :
    IsLimit <| pullbackConeEquivBinaryFan.functor.obj c :=
  BinaryFan.isLimitMk
    -- TODO: Drop `BinaryFan.IsLimit.lift'`. Instead provide the lemmas it bundles separately.
    -- TODO: Define `abbrev BinaryFan.IsLimit (c : BinaryFan X Y) := IsLimit c` for dot notation?
    (fun s ↦ Over.homMk (hc.lift <| pullbackConeEquivBinaryFan.inverse.obj s) <| by
      simpa using s.fst.w)
    (fun s ↦ Over.OverMorphism.ext (hc.fac _ _)) (fun s ↦ Over.OverMorphism.ext (hc.fac _ _))
    fun s m e₁ e₂ ↦ by
      ext1
      apply PullbackCone.IsLimit.hom_ext hc
      · simpa using congr(($e₁).left)
      · simpa using congr(($e₂).left)

/-- A pullback cone to `X` is a limit if its corresponding binary fan in `Over X` is a limit. -/
-- This could also be `(IsLimit.ofConeEquiv pullbackConeEquivBinaryFan.symm).symm hc`, but possibly
-- bad defeqs?
def IsLimit.pullbackConeEquivBinaryFanInverse {c : BinaryFan (Over.mk f) (.mk g)} (hc : IsLimit c) :
    IsLimit <| pullbackConeEquivBinaryFan.inverse.obj c :=
  PullbackCone.IsLimit.mk
    (c.fst.w.trans c.snd.w.symm)
    (fun s ↦ (hc.lift <| pullbackConeEquivBinaryFan.functor.obj s).left)
    (fun s ↦ by simpa only using congr($(hc.fac _ _).left))
    (fun s ↦ by simpa only using congr($(hc.fac _ _).left))
    <| fun s m hm₁ hm₂ ↦ by
      change PullbackCone f g at s
      have := hc.uniq (pullbackConeEquivBinaryFan.functor.obj s) (Over.homMk m <| by
        have := c.fst.w
        simp only [pair_obj_left, Over.mk_left, Functor.id_obj, pair_obj_right,
          Functor.const_obj_obj, Over.mk_hom, Functor.id_map, CostructuredArrow.right_eq_id,
          Discrete.functor_map_id, Category.comp_id] at hm₁ this
        simp [← hm₁, this])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).left)

end Over

section Under
variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- Pushout cocones from `X` are the same thing as binary cofans in `Under X`. -/
@[simps]
def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (.mk g) where
  functor.obj c := .mk (Under.homMk (U := .mk f) (V := .mk (f ≫ c.inl)) c.inl rfl)
      (Under.homMk (U := .mk g) (V := .mk (f ≫ c.inl)) c.inr c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Under.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := .mk c.inl.right c.inr.right (c.inl.w.symm.trans c.inr.w)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.right
    w := by rintro (_ | _ | _) <;> simp [← Under.comp_right]
  }
  unitIso := NatIso.ofComponents (fun c ↦ c.eta) (fun f ↦ by ext; simp)
  counitIso := NatIso.ofComponents (fun X ↦ BinaryCofan.ext (Under.isoMk (.refl _)
    (by dsimp; simpa using X.inl.w.symm)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp)
  functor_unitIso_comp c := by ext; simp

/-- A binary cofan in `Under X` is a colimit if its corresponding pushout cocone from `X` is a
colimit. -/
-- `IsColimit.ofCoconeEquiv` isn't used here because the lift it defines is `pushout.desc ≫ 𝟙 _`.
-- TODO: Define `IsColimit.copy`?
@[simps!]
def IsColimit.pushoutCoconeEquivBinaryCofanFunctor {c : PushoutCocone f g} (hc : IsColimit c) :
    IsColimit <| pushoutCoconeEquivBinaryCofan.functor.obj c :=
  BinaryCofan.isColimitMk
    (fun s ↦ Under.homMk
      (hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.symm.trans s.inr.w))) <| by
        simpa using s.inl.w.symm)
    (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _)) (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ ↦ by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using congr(($e₁).right)
    · simpa using congr(($e₂).right)

/-- A pushout cocone from `X` is a colimit if its corresponding binary cofan in `Under X` is a
colimit. -/
-- This could also be `(IsColimit.ofCoconeEquiv pushoutCoconeEquivBinaryCofan.symm).symm hc`,
-- but possibly bad defeqs?
def IsColimit.pushoutCoconeEquivBinaryCofanInverse {c : BinaryCofan (Under.mk f) (.mk g)}
    (hc : IsColimit c) : IsColimit <| pushoutCoconeEquivBinaryCofan.inverse.obj c :=
  PushoutCocone.IsColimit.mk
    (c.inl.w.symm.trans c.inr.w)
    (fun s ↦ (hc.desc <| pushoutCoconeEquivBinaryCofan.functor.obj s).right)
    (fun s ↦ by simpa only using congr($(hc.fac _ _).right))
    (fun s ↦ by simpa only using congr($(hc.fac _ _).right))
    <| fun s m hm₁ hm₂ ↦ by
      change PushoutCocone f g at s
      have := hc.uniq (pushoutCoconeEquivBinaryCofan.functor.obj s) (Under.homMk m <| by
        have := c.inl.w
        simp only [pair_obj_left, Functor.const_obj_obj, Functor.id_obj, StructuredArrow.left_eq_id,
          Discrete.functor_map_id, Category.id_comp, Under.mk_right, Under.mk_hom, Functor.id_map,
          pair_obj_right] at this hm₁
        simp [← hm₁, ← Category.assoc, ← this])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).right)

end Under
end Limits

namespace Over
section BinaryProduct
variable {X : C} {Y Z : Over X}

open Limits

lemma isPullback_of_binaryFan_isLimit (c : BinaryFan Y Z) (hc : IsLimit c) :
    IsPullback c.fst.left c.snd.left Y.hom Z.hom :=
  ⟨by simp, ⟨hc.pullbackConeEquivBinaryFanInverse⟩⟩

variable (Y Z) [HasPullback Y.hom Z.hom] [HasBinaryProduct Y Z]

/-- The product of `Y` and `Z` in `Over X` is isomorphic to `Y ×ₓ Z`. -/
noncomputable
def prodLeftIsoPullback :
    (Y ⨯ Z).left ≅ pullback Y.hom Z.hom :=
  (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).isoPullback

@[reassoc (attr := simp)]
lemma prodLeftIsoPullback_hom_fst :
    (prodLeftIsoPullback Y Z).hom ≫ pullback.fst _ _ = (prod.fst (X := Y)).left :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma prodLeftIsoPullback_hom_snd :
    (prodLeftIsoPullback Y Z).hom ≫ pullback.snd _ _ = (prod.snd (X := Y)).left :=
  IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)]
lemma prodLeftIsoPullback_inv_fst :
    (prodLeftIsoPullback Y Z).inv ≫ (prod.fst (X := Y)).left = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

@[reassoc (attr := simp)]
lemma prodLeftIsoPullback_inv_snd :
    (prodLeftIsoPullback Y Z).inv ≫ (prod.snd (X := Y)).left = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

end BinaryProduct

/-!
### Arbitrary products

In this section, we prove that `J`-indexed products in `Over X` correspond to `J`-indexed pullbacks
in `C`.
-/

namespace ConstructProducts

/-- (Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
abbrev widePullbackDiagramOfDiagramOver (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    WidePullbackShape J ⥤ C :=
  WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).hom

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverseObj (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F) :
    Cone (widePullbackDiagramOfDiagramOver B F) where
  pt := c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [Category.id_comp, Category.comp_id]
        · rw [Over.w, Category.id_comp]
        · rw [Category.id_comp, Category.comp_id] }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverse (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone F ⥤ Cone (widePullbackDiagramOfDiagramOver B F) where
  obj := conesEquivInverseObj B F
  map f :=
    { hom := f.hom.left
      w := fun j => by
        obtain - | j := j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }

-- Porting note: this should help with the additional `naturality` proof we now have to give in
-- `conesEquivFunctor`, but doesn't.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Discrete

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivFunctor (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ⥤ Cone F where
  obj c :=
    { pt := Over.mk (c.π.app none)
      π :=
        { app := fun ⟨j⟩ => Over.homMk (c.π.app (some j)) (c.w (WidePullbackShape.Hom.term j))
          -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10888): added proof for `naturality`
          naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by dsimp at f ⊢; cat_disch } }
  map f := { hom := Over.homMk f.hom }

-- Porting note: unfortunately `aesop` can't cope with a `cases` rule here for the type synonym
-- `WidePullbackShape`.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WidePullbackShape
-- If this worked we could avoid the `rintro` in `conesEquivUnitIso`.

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps!]
def conesEquivUnitIso (B : C) (F : Discrete J ⥤ Over B) :
    𝟭 (Cone (widePullbackDiagramOfDiagramOver B F)) ≅
      conesEquivFunctor B F ⋙ conesEquivInverse B F :=
  NatIso.ofComponents fun _ => Cones.ext
    { hom := 𝟙 _
      inv := 𝟙 _ }
    (by rintro (j | j) <;> cat_disch)

-- TODO: Can we add `:= by aesop` to the second arguments of `NatIso.ofComponents` and
--       `Cones.ext`?
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps!]
def conesEquivCounitIso (B : C) (F : Discrete J ⥤ Over B) :
    conesEquivInverse B F ⋙ conesEquivFunctor B F ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun _ => Cones.ext
    { hom := Over.homMk (𝟙 _)
      inv := Over.homMk (𝟙 _) }

/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
def conesEquiv (B : C) (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ≌ Cone F where
  functor := conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F

/-- Use the above equivalence to prove we have a limit. -/
theorem has_over_limit_discrete_of_widePullback_limit {B : C} (F : Discrete J ⥤ Over B)
    [HasLimit (widePullbackDiagramOfDiagramOver B F)] : HasLimit F :=
  HasLimit.mk
    { cone := _
      isLimit := IsLimit.ofRightAdjoint (conesEquiv B F).symm.toAdjunction
        (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
theorem over_product_of_widePullback [HasLimitsOfShape (WidePullbackShape J) C] {B : C} :
    HasLimitsOfShape (Discrete J) (Over B) :=
  { has_limit := fun F => has_over_limit_discrete_of_widePullback_limit F }

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
theorem over_binaryProduct_of_pullback [HasPullbacks C] {B : C} : HasBinaryProducts (Over B) :=
  over_product_of_widePullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
theorem over_products_of_widePullbacks [HasWidePullbacks.{w} C] {B : C} :
    HasProducts.{w} (Over B) :=
  fun _ => over_product_of_widePullback

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
theorem over_finiteProducts_of_finiteWidePullbacks [HasFiniteWidePullbacks C] {B : C} :
    HasFiniteProducts (Over B) :=
  ⟨fun _ => over_product_of_widePullback⟩

end ConstructProducts

/-- Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_widePullback` above.)
-/
theorem over_hasTerminal (B : C) : HasTerminal (Over B) where
  has_limit F := HasLimit.mk
    { cone :=
        { pt := Over.mk (𝟙 _)
          π :=
            { app := fun p => p.as.elim } }
      isLimit :=
        { lift := fun s => Over.homMk s.pt.hom
          fac := fun _ j => j.as.elim
          uniq := fun s m _ => by
            simp only
            ext
            rw [Over.homMk_left _]
            have := m.w
            dsimp at this
            rwa [Category.comp_id, Category.comp_id] at this } }

end CategoryTheory.Over
