/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.CharacterModule

/-!
This file shows that the functors `Grp.uliftFunctor` and `CommGrp.uliftFunctor`
(as well as the additive versions) are fully faithful, preserves all limits and
create small limits.

It also shows that `AddCommGrp.uliftFunctor` preserves all colimits, creates small colimits,
preserves zero morphisms and is an additive functor.

-/

universe v w w' u

open CategoryTheory Limits

namespace Grp

/-- The universe lift functor for groups is faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

/-- The universe lift functor for groups is full.
-/
@[to_additive
  "The universe lift functor for additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ Grp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
      preserves {c} lc := by
        apply ReflectsLimit.reflects (F := forget Grp.{max u v})
        set e : CategoryTheory.uliftFunctor.{v,u}.mapCone ((forget Grp).mapCone c) ≅
            (forget Grp).mapCone (uliftFunctor.mapCone c) := Cones.ext (Iso.refl _) (fun _ ↦ rfl)
        exact IsLimit.ofIsoLimit (Classical.choice (PreservesLimit.preserves
          (F := CategoryTheory.uliftFunctor) (Classical.choice (PreservesLimit.preserves
          (F := forget Grp) lc)))) e

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where
      preservesLimit := inferInstance

/--
The universe lift for groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
      preservesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance uliftFunctor_preservesLimits :
    PreservesLimits uliftFunctor.{v, u} := uliftFunctor_preservesLimitsOfSize

/--
The universe lift functor on `Grp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddGrp.{u}` creates `u`-small limits."
]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end Grp

namespace CommGrp

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  "The universe lift functor for commutative additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  "The universe lift functor for commutative additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ CommGrp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
      preserves {c} lc := by
        apply ReflectsLimit.reflects (F := forget CommGrp.{max u v})
        set e : CategoryTheory.uliftFunctor.{v,u}.mapCone ((forget CommGrp).mapCone c) ≅
            (forget CommGrp).mapCone (uliftFunctor.mapCone c) :=
          Cones.ext (Iso.refl _) (fun _ ↦ rfl)
        exact IsLimit.ofIsoLimit (Classical.choice (PreservesLimit.preserves
          (F := CategoryTheory.uliftFunctor) (Classical.choice (PreservesLimit.preserves
          (F := forget CommGrp) lc)))) e

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where
      preservesLimit := inferInstance

/--
The universe lift for commutative groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for commutative additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
      preservesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance uliftFunctor_preservesLimits :
    PreservesLimits uliftFunctor.{v, u} := uliftFunctor_preservesLimitsOfSize

/--
The universe lift functor on `CommGrp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddCommGrp.{u}` creates `u`-small limits."
]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end CommGrp

namespace AddCommGroup

/-- The universe lift for commutative additive groups preserves zero morphisms.
-/
instance uliftFunctor_preservesZeroMorphisms :
    AddCommGrp.uliftFunctor.{u,v}.PreservesZeroMorphisms := {map_zero := fun X Y ↦ by rfl}

instance uliftFunctor_additive :
    AddCommGrp.uliftFunctor.{u,v}.Additive where map_add := rfl

end AddCommGroup

namespace AddCommGrp

variable {J : Type w} [Category.{w'} J] {K : J ⥤ AddCommGrp.{u}} {c : Cocone K} (hc : IsColimit c)
  {lc : Cocone (K ⋙ AddCommGrp.uliftFunctor.{v,u})}

variable {A A' : Type} [AddCommGroup A] [AddCommGroup A']

def coconeOfChar (f : lc.pt →+ A) : Cocone K where
  pt := AddCommGrp.of (ULift A)
  ι :=
  { app j := AddCommGrp.ofHom (((@AddEquiv.ulift A _).symm.toAddMonoidHom.comp f).comp
             ((lc.ι.app j).comp (@AddEquiv.ulift (K.obj j) _).symm.toAddMonoidHom))
    naturality {j j'} u := by
      ext a
      have := lc.ι.naturality u
      apply_fun (fun f ↦ f {down := a}) at this
      change lc.ι.app j' {down := K.map u a} = _ at this
      change ({down := f (lc.ι.app j' {down := K.map u a})} : ULift A) = _
      rw [this]; rfl
  }

def descChar (f : lc.pt →+ A) : c.pt →+ A :=
  AddEquiv.ulift.toAddMonoidHom.comp (hc.desc (coconeOfChar f))

lemma descChar_fac (f : lc.pt →+ A) (j : J) (a : K.obj j) :
    (descChar hc f) (c.ι.app j a) = f ((lc.ι.app j {down := a})) := by
  have := hc.fac (coconeOfChar f) j
  apply_fun (fun f ↦ f a) at this
  change hc.desc (coconeOfChar f) ((c.ι.app j) a) = _ at this
  simp only [descChar, AddEquiv.toAddMonoidHom_eq_coe, Functor.const_obj_obj, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply, Functor.comp_obj, uliftFunctor_obj, coe_of]
  conv_lhs => erw [this]
  rfl

lemma descChar_uniq (f : lc.pt →+ A) (m : c.pt →+ A) (hm : ∀ (j : J) (a : K.obj j),
    m (c.ι.app j a) = f ((lc.ι.app j {down := a}))) : m = descChar hc f := by
  refine AddMonoidHom.ext_iff.mpr (congrFun ?_)
  dsimp [descChar]
  rw [← AddEquiv.symm_comp_eq]
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp m = hc.desc (coconeOfChar f) by
    rw [← this]; rfl
  refine hc.uniq (coconeOfChar f) ((@AddEquiv.ulift A _).symm.toAddMonoidHom.comp m) (fun j ↦ ?_)
  ext a
  change ({down := m (c.ι.app j a)} : ULift A) = _
  rw [hm j a]
  rfl

lemma descChar_comp (f : lc.pt →+ A) (g : A →+ A') :
    descChar hc (g.comp f) = g.comp (descChar hc f) := by
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp (descChar hc (g.comp f)) =
      (@AddEquiv.ulift A' _).symm.toAddMonoidHom.comp (g.comp (descChar hc f)) by
    ext a
    apply_fun (fun f ↦ f a) at this
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  refine (hc.uniq (coconeOfChar (g.comp f)) (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (g.comp (descChar hc f))) (fun j ↦ ?_)).symm
  ext a
  simp [coconeOfChar]
  conv_lhs => erw [descChar_fac hc f j a]
  rfl

lemma descChar_zero_eq_zero : descChar hc (0 : lc.pt →+ A) = 0 := by
  have heq : (0 : lc.pt →+ A) = (0 : Unit →+ A).comp (0 : lc.pt →+ Unit) := by
    ext _; simp
  rw [heq, descChar_comp]
  simp

variable {ι : Type*} (B : ι → Type) [∀ (i : ι), AddCommGroup (B i)]
    (f : (i : ι) → lc.pt →+ B i)

def descCharFamily : c.pt →+ ((i : ι) → B i) := Pi.addMonoidHom (fun i ↦ descChar hc (f i))

lemma descCharFamily_comp (g : ((i : ι) → B i) →+ A) :
    descChar hc (g.comp (Pi.addMonoidHom f)) = g.comp (descCharFamily hc B f) := by
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp (descChar hc (g.comp (Pi.addMonoidHom f))) =
      (@AddEquiv.ulift A _).symm.toAddMonoidHom.comp (g.comp (descCharFamily hc B f)) by
    ext a
    apply_fun (fun f ↦ f a) at this
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  refine (hc.uniq (coconeOfChar (g.comp (Pi.addMonoidHom f)))
    (AddEquiv.ulift.symm.toAddMonoidHom.comp (g.comp (descCharFamily hc B f)))
    (fun j ↦ ?_)).symm
  ext a
  simp [coconeOfChar]
  congr 1
  ext i
  simp [descCharFamily]
  conv_lhs => erw [descChar_fac hc (f i) j a]
  rfl

variable (lc)

open CharacterModule in
noncomputable def descHom : c.pt →+ lc.pt := by
  set u := descCharFamily hc (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) (fun c ↦ c)
  have h : (QuotientAddGroup.mk' (AddMonoidHom.range (hom_to_pi lc.pt))).comp u = 0 := by
    refine hom_eq_zero_of_character_apply (fun c ↦ ?_)
    rw [← AddMonoidHom.comp_assoc, ← descCharFamily_comp hc
      (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) (fun c ↦ c)]
    convert descChar_zero_eq_zero hc
    ext _
    change (c.comp ((QuotientAddGroup.mk' (AddMonoidHom.range (hom_to_pi lc.pt))).comp
      (hom_to_pi lc.pt))) _ = 0
    rw [(AddMonoidHom.range_le_ker_iff _ _).mp (le_of_eq (QuotientAddGroup.ker_mk' _).symm),
      c.comp_zero, AddMonoidHom.zero_apply]
  rw [← AddMonoidHom.range_le_ker_iff, ← (QuotientAddGroup.ker_mk' _).symm] at h
  exact (AddMonoidHom.ofInjective (hom_to_pi_injective lc.pt)).symm.toAddMonoidHom.comp
    ((AddSubgroup.inclusion h).comp (AddMonoidHom.rangeRestrict u))

open CharacterModule in
lemma descHom_property (χ : lc.pt →+ AddCircle (1 : ℚ)) : χ.comp (descHom hc lc) =
    descChar hc χ := by
  change ((Pi.evalAddMonoidHom (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) χ).comp
    (hom_to_pi lc.pt)).comp (descHom hc lc) = _
  refine AddMonoidHom.ext (fun a ↦ ?_)
  conv_lhs => rw [AddMonoidHom.comp_assoc, AddMonoidHom.comp_apply]
  erw [AddMonoidHom.apply_ofInjective_symm (hom_to_pi_injective lc.pt),
    AddMonoidHom.coe_rangeRestrict]
  conv_lhs => erw [← AddMonoidHom.comp_apply (Pi.evalAddMonoidHom (fun x ↦ AddCircle 1) χ)
                (descCharFamily hc (fun x ↦ AddCircle 1) fun c ↦ c)]
              rw [← descCharFamily_comp]
  rfl

lemma descHom_fac (j : J) (a : K.obj j) :
    descHom hc lc (c.ι.app j a) = lc.ι.app j {down := a} := by
  rw [← add_neg_eq_zero]
  refine CharacterModule.eq_zero_of_character_apply (fun χ ↦ ?_)
  rw [χ.map_add]
  change (χ.comp ((descHom hc lc).comp (c.ι.app j))) a + _ = 0
  rw [← AddMonoidHom.comp_assoc, descHom_property]
  erw [descChar_fac]
  simp

lemma descHom_uniq (m : c.pt →+ lc.pt) (hm : ∀ (j : J) (a : K.obj j),
    m (c.ι.app j a) = lc.ι.app j {down := a}) : m = descHom hc lc := by
  rw [← add_neg_eq_zero]
  refine CharacterModule.hom_eq_zero_of_character_apply (fun χ ↦ ?_)
  rw [AddMonoidHom.comp_add, AddMonoidHom.comp_neg, descHom_property, add_neg_eq_zero]
  refine descChar_uniq _ _ _ (fun j a ↦ ?_)
  simp only [Functor.const_obj_obj, AddMonoidHom.coe_comp, Function.comp_apply, Functor.comp_obj,
    uliftFunctor_obj, coe_of]
  erw [hm j a]
  rfl

/--
The functor `AddCommGr.uliftFunctor.{v,u} : AddCommGrp.{u} ⥤ AddCommGrp.{max v u}`
preserves colimits of arbitrary size.
-/
noncomputable instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J _} :=
  { preservesColimit := fun {F} ↦
    { preserves := fun {c} hc ↦ ⟨{
        desc := fun lc ↦ AddCommGrp.ofHom ((descHom hc lc).comp AddEquiv.ulift.toAddMonoidHom)
        fac := fun lc j ↦ by ext ⟨⟩; erw [← descHom_fac hc lc j]; rfl
        uniq := fun lc f hf ↦ by
          apply (AddMonoidHom.precompEquiv AddEquiv.ulift.symm _).injective
          refine descHom_uniq hc lc (f.comp AddEquiv.ulift.symm.toAddMonoidHom) (fun j a ↦ ?_)
          simp only [Functor.mapCocone_pt, uliftFunctor_obj, coe_of, AddEquiv.toAddMonoidHom_eq_coe,
            Functor.const_obj_obj, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
            Functor.comp_obj]
          rw [← hf j]
          rfl }⟩ } }

/--
The functor `AddCommGrp.uliftFunctor.{v,u} : AddCommGrp.{u} ⥤ AddCommGrp.{max v u}`
creates `u`-small colimits.
-/
noncomputable instance : CreatesColimitsOfSize.{u, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape := { CreatesColimit := fun {_} ↦ createsColimitOfFullyFaithfulOfPreserves }

end AddCommGrp
