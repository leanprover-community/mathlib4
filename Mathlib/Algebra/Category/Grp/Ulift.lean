/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.CharacterModule

/-!
This file shows that the functors `Grp.uliftFunctor` and `CommGrp.uliftFunctor`
(as well as the additive versions) are fully faithful, preserves all limits and
create small limits.

It also shows that `AddCommGrp.uliftFunctor` preserves zero morphisms and is an additive functor.

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

variable {J : Type w} [Category.{w'} J] {K : J ⥤ AddCommGrp.{u}} {c : Cocone K}
  {lc : Cocone (K ⋙ AddCommGrp.uliftFunctor.{v,u})} (hc : IsColimit c)

variable {A A' : Type u} [AddCommGroup A] [AddCommGroup A']

def coconeOfChar (f : lc.pt →+ A) : Cocone K where
  pt := AddCommGrp.of A
  ι :=
  { app j := AddCommGrp.ofHom (f.comp ((lc.ι.app j).comp
      (@AddEquiv.ulift (K.obj j) _).symm.toAddMonoidHom))
    naturality {j j'} u := by
      ext a
      have := lc.ι.naturality u
      apply_fun (fun f ↦ f {down := a}) at this
      change lc.ι.app j' {down := K.map u a} = _ at this
      change f (lc.ι.app j' {down := K.map u a}) = f (lc.ι.app j {down := a})
      rw [this]; rfl
  }

/-
def coconeOfChar_map (f : lc.pt →+ A) (g : A →+ A') :
    coconeOfChar f ⟶ coconeOfChar (g.comp f) :=
  CoconeMorphism.mk g (fun j ↦ by ext _; simp [coconeOfChar])
-/

def descChar (f : lc.pt →+A) : c.pt →+ A := hc.desc (coconeOfChar f)

lemma descChar_ι_app (f : lc.pt →+ A) (j : J) (a : K.obj j) :
    (descChar hc f) (c.ι.app j a) = f ((lc.ι.app j {down := a})) := by
  have := hc.fac (coconeOfChar f) j
  apply_fun (fun f ↦ f a) at this
  change hc.desc (coconeOfChar f) ((c.ι.app j) a) = _ at this
  conv_lhs => erw [this]
  rfl

lemma descChar_comp (f : lc.pt →+ A) (g : A →+ A') :
    descChar hc (g.comp f) = g.comp (descChar hc f) := by
  refine (hc.uniq (coconeOfChar (g.comp f)) (g.comp (descChar hc f)) (fun j ↦ ?_)).symm
  ext a
  simp [coconeOfChar]
  conv_lhs => erw [descChar_ι_app hc f j a]
  rfl

lemma descChar_zero_eq_zero : descChar hc (0 : lc.pt →+ A) = 0 := by
  have heq : (0 : lc.pt →+ A) = (0 : ULift.{u} Unit →+ A).comp (0 : lc.pt →+ ULift Unit) := by
    ext _; simp
  rw [heq, descChar_comp]
  simp

variable {ι : Type*} (B : ι → Type u) [∀ (i : ι), AddCommGroup (B i)]
    (f : (i : ι) → lc.pt →+ B i)

def descCharFamily : c.pt →+ ((i : ι) → B i) := Pi.addMonoidHom (fun i ↦ descChar hc (f i))

lemma descCharFamily_comp (g : ((i : ι) → B i) →+ A) :
    descChar hc (g.comp (Pi.addMonoidHom f)) = g.comp (descCharFamily hc B f) := by
  refine (hc.uniq (coconeOfChar (g.comp (Pi.addMonoidHom f)))
    (g.comp (descCharFamily hc B f)) (fun j ↦ ?_)).symm
  ext a
  simp [coconeOfChar]
  congr 1
  ext i
  simp [descCharFamily]
  conv_lhs => erw [descChar_ι_app hc (f i) j a]
  rfl

abbrev truc (C : Type*) [AddCommGroup C] :
    C →+ ((c : CharacterModule C) → ULift.{u} (AddCircle (1 : ℚ))) where
  toFun a c := {down := c a}
  map_zero' := by ext _; simp
  map_add' _ _ := by ext _; simp

lemma truc_injective (C : Type*) [AddCommGroup C] : Function.Injective (truc C) := by
  refine (injective_iff_map_eq_zero _).mpr (fun a ha ↦ CharacterModule.eq_zero_of_character_apply
    (fun c ↦ ?_))
  apply_fun (fun f ↦ f c) at ha
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at ha
  rw [← ULift.down_up (c a), ha, ULift.zero_down]

variable (lc)

noncomputable def descHom : c.pt →+ lc.pt := by
  set u : lc.pt →+ ((c : CharacterModule lc.pt) → ULift.{u} (AddCircle (1 : ℚ))) := truc lc.pt
  set u' := descCharFamily hc (fun (c : CharacterModule lc.pt) ↦ ULift.{u} (AddCircle (1 : ℚ)))
    (fun c ↦ AddEquiv.ulift.symm.toAddMonoidHom.comp c) with hdef'
  set π := (QuotientAddGroup.mk' (AddMonoidHom.range u)) with hπ
  have h : u.range = π.ker := sorry
  have h' : π.comp u' = 0 := by
    refine CharacterModule.hom_eq_zero_of_character_apply (fun c ↦ ?_)
    suffices h'' : ((AddEquiv.ulift.{0,u}.symm.toAddMonoidHom.comp c).comp π).comp u' = 0 by
      apply_fun (fun h ↦ AddEquiv.ulift.{0,u}.toAddMonoidHom.comp h) at h''
      rw [AddMonoidHom.comp_zero] at h''
      rw [← h'']
      ext _; simp
    rw [← descCharFamily_comp hc (fun (c : CharacterModule lc.pt) ↦ ULift.{u} (AddCircle (1 : ℚ)))
      (fun c ↦ AddEquiv.ulift.symm.toAddMonoidHom.comp c)]
    suffices (((AddEquiv.ulift.symm.toAddMonoidHom.comp c).comp π).comp
        (Pi.addMonoidHom fun c ↦ AddEquiv.ulift.symm.toAddMonoidHom.comp c)) = 0 by
      rw [this]; exact descChar_zero_eq_zero hc
    ext a
    change (c.comp (π.comp u)) a = 0
    rw [(AddMonoidHom.range_le_ker_iff _ _).mp (le_of_eq h), c.comp_zero,
      AddMonoidHom.zero_apply]
  rw [← AddMonoidHom.range_le_ker_iff, ← h] at h'
  exact (AddMonoidHom.ofInjective (truc_injective lc.pt)).symm.toAddMonoidHom.comp
    ((AddSubgroup.inclusion h').comp (AddMonoidHom.rangeRestrict u'))

variable {lc}

lemma descHom_fac (j : J) (a : K.obj j) :
    descHom lc hc (c.ι.app j a) = lc.ι.app j {down := a} := by
  simp [descHom]
  sorry



end AddCommGrp
