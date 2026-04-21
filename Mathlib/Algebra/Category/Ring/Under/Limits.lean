/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Limits in `Under R` for a commutative ring `R`

We show that `Under.pushout f` is left-exact, i.e. preserves finite limits, if `f : R ⟶ S` is
flat.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

universe v u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat.Under

section Algebra

variable [Algebra R S]

section Pi

variable {ι : Type u} (P : ι → Under R)

/-- The canonical fan on `P : ι → Under R` given by `∀ i, P i`. -/
def piFan : Fan P :=
  Fan.mk (Under.mk <| ofHom <| Pi.ringHom (fun i ↦ (P i).hom.hom))
    (fun i ↦ Under.homMk (ofHom <| Pi.evalRingHom _ i))

/-- The canonical fan is limiting. -/
def piFanIsLimit : IsLimit (piFan P) :=
  isLimitOfReflects (Under.forget R) <|
    (isLimitMapConeFanMkEquiv (Under.forget R) P _).symm <|
      CommRingCat.piFanIsLimit (fun i ↦ (P i).right)

variable (S) in
/-- The fan on `i ↦ S ⊗[R] P i` given by `S ⊗[R] ∀ i, P i` -/
def tensorProductFan : Fan (fun i ↦ mkUnder S (S ⊗[R] (P i).right)) :=
  Fan.mk (mkUnder S <| S ⊗[R] ∀ i, (P i).right)
    (fun i ↦ AlgHom.toUnder <|
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom R (fun j ↦ (P j).right) i))

variable (S) in
/-- The fan on `i ↦ S ⊗[R] P i` given by `∀ i, S ⊗[R] P i` -/
def tensorProductFan' : Fan (fun i ↦ mkUnder S (S ⊗[R] (P i).right)) :=
  Fan.mk (mkUnder S <| ∀ i, S ⊗[R] (P i).right)
    (fun i ↦ AlgHom.toUnder <| Pi.evalAlgHom S _ i)

set_option backward.isDefEq.respectTransparency false in
/-- The two fans on `i ↦ S ⊗[R] P i` agree if `ι` is finite. -/
def tensorProductFanIso [Fintype ι] [DecidableEq ι] :
    tensorProductFan S P ≅ tensorProductFan' S P :=
  Fan.ext (Algebra.TensorProduct.piRight R S _ _).toUnder <| fun i ↦ by
    dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
    apply CommRingCat.mkUnder_ext
    intro c
    induction c
    · simp only [map_zero, Under.comp_right]
    · simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Pi.evalAlgHom_apply, Under.comp_right, comp_apply, AlgEquiv.toUnder_hom_right_apply,
        Algebra.TensorProduct.piRight_tmul]
    · simp_all

open Classical in
/-- The fan on `i ↦ S ⊗[R] P i` given by `S ⊗[R] ∀ i, P i` is limiting if `ι` is finite. -/
def tensorProductFanIsLimit [Finite ι] : IsLimit (tensorProductFan S P) :=
  letI : Fintype ι := Fintype.ofFinite ι
  (IsLimit.equivIsoLimit (tensorProductFanIso P)).symm (Under.piFanIsLimit _)

/-- `tensorProd R S` preserves the limit of the canonical fan on `P`. -/
noncomputable -- marked noncomputable for performance (only)
def piFanTensorProductIsLimit [Finite ι] : IsLimit ((tensorProd R S).mapCone (Under.piFan P)) :=
  (isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm <| tensorProductFanIsLimit P

instance (J : Type u) [Finite J] (f : J → Under R) :
    PreservesLimit (Discrete.functor f) (tensorProd R S) :=
  let c : Fan _ := Under.piFan f
  have hc : IsLimit c := Under.piFanIsLimit f
  preservesLimit_of_preserves_limit_cone hc (piFanTensorProductIsLimit f)

instance : PreservesFiniteProducts (tensorProd R S) where
  preserves n :=
    let J : Type u := ULift.{u} (Fin n)
    have : PreservesLimitsOfShape (Discrete J) (tensorProd R S) :=
      preservesLimitsOfShape_of_discrete (tensorProd R S)
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) (R.tensorProd S)

end Pi

section Equalizer

lemma equalizer_comp {A B : Under R} (f g : A ⟶ B) :
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ f =
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ g := by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property

set_option backward.isDefEq.respectTransparency false in
/-- The canonical fork on `f g : A ⟶ B` given by the equalizer. -/
def equalizerFork {A B : Under R} (f g : A ⟶ B) :
    Fork f g :=
  Fork.ofι ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)
    (by rw [equalizer_comp])

@[simp]
lemma equalizerFork_ι {A B : Under R} (f g : A ⟶ B) :
    (Under.equalizerFork f g).ι = (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder := rfl

/-- Variant of `Under.equalizerFork'` for algebra maps. This is definitionally equal to
`Under.equalizerFork` but this is costly in applications. -/
def equalizerFork' {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) :
    Fork f.toUnder g.toUnder :=
  Fork.ofι ((AlgHom.equalizer f g).val.toUnder) <| by ext a; exact a.property

@[simp]
lemma equalizerFork'_ι {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) :
    (Under.equalizerFork' f g).ι = (AlgHom.equalizer f g).val.toUnder := rfl

/-- The canonical fork on `f g : A ⟶ B` is limiting. -/
-- marked noncomputable for performance (only)
noncomputable def equalizerForkIsLimit {A B : Under R} (f g : A ⟶ B) :
    IsLimit (Under.equalizerFork f g) :=
  isLimitOfReflects (Under.forget R) <|
    (isLimitMapConeForkEquiv (Under.forget R) (equalizer_comp f g)).invFun <|
      CommRingCat.equalizerForkIsLimit f.right g.right

/-- Variant of `Under.equalizerForkIsLimit` for algebra maps. -/
def equalizerFork'IsLimit {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f g : A →ₐ[R] B) :
    IsLimit (Under.equalizerFork' f g) :=
  Under.equalizerForkIsLimit f.toUnder g.toUnder

set_option backward.isDefEq.respectTransparency false in
/-- The fork on `𝟙 ⊗[R] f` and `𝟙 ⊗[R] g` given by `S ⊗[R] eq(f, g)`. -/
def tensorProdEqualizer {A B : Under R} (f g : A ⟶ B) :
    Fork ((tensorProd R S).map f) ((tensorProd R S).map g) :=
  Fork.ofι
    ((tensorProd R S).map ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)) <| by
    rw [← Functor.map_comp, equalizer_comp, Functor.map_comp]

@[simp]
lemma tensorProdEqualizer_ι {A B : Under R} (f g : A ⟶ B) :
    (tensorProdEqualizer f g).ι = (tensorProd R S).map
      ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder) :=
  rfl

/-- If `S` is `R`-flat, `S ⊗[R] eq(f, g)` is isomorphic to `eq(𝟙 ⊗[R] f, 𝟙 ⊗[R] g)`. -/
-- marked noncomputable for performance (only)
noncomputable def equalizerForkTensorProdIso [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    tensorProdEqualizer f g ≅ Under.equalizerFork'
        (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f))
        (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom g)) :=
  Fork.ext (AlgHom.tensorEqualizerEquiv S S (toAlgHom f) (toAlgHom g)).toUnder <| by
    ext
    apply AlgHom.coe_tensorEqualizer

/-- If `S` is `R`-flat, `tensorProd R S` preserves the equalizer of `f` and `g`. -/
noncomputable -- marked noncomputable for performance (only)
def tensorProdMapEqualizerForkIsLimit [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    IsLimit ((tensorProd R S).mapCone <| Under.equalizerFork f g) :=
  (isLimitMapConeForkEquiv (tensorProd R S) _).symm <|
    (IsLimit.equivIsoLimit (equalizerForkTensorProdIso f g).symm) <|
    Under.equalizerFork'IsLimit _ _

instance [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    PreservesLimit (parallelPair f g) (tensorProd R S) :=
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let hc' : IsLimit ((tensorProd R S).mapCone c) :=
    tensorProdMapEqualizerForkIsLimit f g
  preservesLimit_of_preserves_limit_cone hc hc'

instance [Module.Flat R S] : PreservesLimitsOfShape WalkingParallelPair (tensorProd R S) where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

instance [Module.Flat R S] : PreservesFiniteLimits (tensorProd R S) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (tensorProd R S)

end Equalizer

end Algebra

variable (f : R ⟶ S)

/-- `Under.pushout f` preserves finite products. -/
instance : PreservesFiniteProducts (Under.pushout f) where
  preserves _ :=
    letI : Algebra R S := f.hom.toAlgebra
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

/-- `Under.pushout f` preserves finite limits if `f` is flat. -/
lemma preservesFiniteLimits_of_flat (hf : RingHom.Flat f.hom) :
    PreservesFiniteLimits (Under.pushout f) where
  preservesFiniteLimits _ :=
    letI : Algebra R S := f.hom.toAlgebra
    haveI : Module.Flat R S := hf
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

end CommRingCat.Under
