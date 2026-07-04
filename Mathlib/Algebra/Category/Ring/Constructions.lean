/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Mathlib.RingTheory.FreeCommRing
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Constructions of (co)limits in `CommRingCat`

In this file we provide the explicit (co)cones for various (co)limits in `CommRingCat`, including
* tensor product is the pushout
* tensor product over `ℤ` is the binary coproduct
* `ℤ` is the initial object
* `0` is the strict terminal object
* Cartesian product is the product
* arbitrary direct product of a family of rings is the product object (Pi object)
* `RingHom.eqLocus` is the equalizer

-/

@[expose] public section

universe u u'

open CategoryTheory Limits TensorProduct

namespace CommRingCat

section Pushout

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The explicit cocone with tensor products as the fibered product in `CommRingCat`. -/
def pushoutCocone : Limits.PushoutCocone
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) := by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A ⊗[R] B)
  · exact ofHom <| Algebra.TensorProduct.includeLeftRingHom (A := A)
  · exact ofHom <| Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A ⊗[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm

@[simp]
theorem pushoutCocone_inl :
    (pushoutCocone R A B).inl = ofHom (Algebra.TensorProduct.includeLeftRingHom (A := A)) :=
  rfl

@[simp]
theorem pushoutCocone_inr :
    (pushoutCocone R A B).inr = ofHom (Algebra.TensorProduct.includeRight.toRingHom (A := B)) :=
  rfl

@[simp]
theorem pushoutCocone_pt :
    (pushoutCocone R A B).pt = CommRingCat.of (A ⊗[R] B) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone R A B) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra (s.inl.hom.comp (algebraMap R A))
    let f' : A →ₐ[R] s.pt :=
      { s.inl.hom with
        commutes' := fun r => rfl }
    let g' : B →ₐ[R] s.pt :=
      { s.inr.hom with
        commutes' := DFunLike.congr_fun <| congrArg Hom.hom
          ((s.ι.naturality Limits.WalkingSpan.Hom.snd).trans
            (s.ι.naturality Limits.WalkingSpan.Hom.fst).symm) }
    letI : Algebra R (pushoutCocone R A B).pt := show Algebra R (A ⊗[R] B) by infer_instance
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use ofHom (AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g'))
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_left_apply (A := A) _ _ x
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_right_apply (B := B) _ _ x
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.pt :=
      { h.hom with
        commutes' := fun r => by
          change h (algebraMap R A r ⊗ₜ[R] 1) = s.inl (algebraMap R A r)
          rw [← eq1]
          simp only [pushoutCocone_pt, coe_of]
          rfl }
    suffices h' = Algebra.TensorProduct.productMap f' g' by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [f', g', ← eq1, pushoutCocone_pt, ← eq2, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.coe_mk]
    change _ = h (a ⊗ₜ 1) * h (1 ⊗ₜ b)
    rw [← h.hom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl

lemma isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsPushout (ofHom <| algebraMap R A) (ofHom <| algebraMap R B)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeRight.toRingHom) where
  w := by
    ext
    simp
  isColimit' := ⟨pushoutCoconeIsColimit R A B⟩

lemma isPushout_of_isPushout (R S A B : Type u) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R A))
      (ofHom (algebraMap S B)) (ofHom (algebraMap A B)) :=
  (isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Algebra.IsPushout.equiv R S A B).toCommRingCatIso (by simp) (by simp)
    (by ext; simp [Algebra.IsPushout.equiv_tmul]) (by ext; simp [Algebra.IsPushout.equiv_tmul])

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S)
      (ofHom <| algebraMap R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S' := by
  refine ⟨fun h ↦ ?_, fun h ↦ isPushout_of_isPushout ..⟩
  let e : R' ⊗[R] S ≃+* S' := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r ⊗ₜ 1) = (pushout.inl (ofHom _) (ofHom _)) r :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inl_isoPushout_hom).hom r)
  have h3 (x : R') := congr($(h.inl_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h3
  let e' : R' ⊗[R] S ≃ₐ[R'] S' := {
    __ := e
    commutes' r := by simp [Iso.commRingCatIsoToRingEquiv, h2, e, h3] }
  refine Algebra.IsPushout.of_equiv e' ?_
  ext s
  have h1 : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (algebraMap S (R' ⊗[R] S) s) = (pushout.inr (ofHom _) (ofHom _)) s :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inr_isoPushout_hom).hom s)
  have h4 (x : S) := congr($(h.inr_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h4
  simp [Iso.commRingCatIsoToRingEquiv, h1, e', e, h4]

lemma isPushout_of_isLocalization {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing Rₘ] [Algebra R Rₘ] [CommRing S] [CommRing Sₘ] [Algebra S Sₘ]
    (f : R →+* S) (fₘ : Rₘ →+* Sₘ) (H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp f)
    (M : Submonoid R) [IsLocalization M Rₘ] [IsLocalization (M.map f) Sₘ] :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R Rₘ))
      (CommRingCat.ofHom (algebraMap S Sₘ)) (CommRingCat.ofHom fₘ) := by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)

lemma closure_range_union_range_eq_top_of_isPushout
    {R A B X : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B} {a : A ⟶ X} {b : B ⟶ X}
    (H : IsPushout f g a b) :
    Subring.closure (Set.range a ∪ Set.range b) = ⊤ := by
  algebraize [f.hom, g.hom]
  let e := ((isPushout_tensorProduct R A B).isoIsPushout A B H).commRingCatIsoToRingEquiv
  rw [← Subring.comap_map_eq_self_of_injective e.symm.injective (.closure _), RingHom.map_closure,
    ← top_le_iff, ← Subring.map_le_iff_le_comap, Set.image_union]
  simp only [AlgHom.toRingHom_eq_coe, ← Set.range_comp, ← RingHom.coe_comp]
  rw [← hom_comp, ← hom_comp, IsPushout.inl_isoIsPushout_inv, IsPushout.inr_isoIsPushout_inv,
    hom_ofHom, hom_ofHom]
  exact le_top.trans (Algebra.TensorProduct.closure_range_union_range_eq_top R A B).ge

end Pushout

section BinaryCoproduct

variable (A B : CommRingCat.{u})

/-- The tensor product `A ⊗[ℤ] B` forms a cocone for `A` and `B`. -/
@[simps! pt ι]
def coproductCocone : BinaryCofan A B :=
  BinaryCofan.mk
    (ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom : A ⟶ of (A ⊗[ℤ] B))
    (ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom : B ⟶ of (A ⊗[ℤ] B))

@[simp]
theorem coproductCocone_inl :
    (coproductCocone A B).inl = ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom := rfl

@[simp]
theorem coproductCocone_inr :
    (coproductCocone A B).inr = ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product `A ⊗[ℤ] B` is a coproduct for `A` and `B`. -/
@[simps]
def coproductCoconeIsColimit : IsColimit (coproductCocone A B) where
  desc (s : BinaryCofan A B) :=
    ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom
      (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := fun ⟨j⟩ => by cases j <;> ext a <;> simp
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A ⊗[ℤ] B →+* s.pt⟩ hm
    apply CommRingCat.hom_ext
    apply RingHom.toIntAlgHom_injective
    apply Algebra.TensorProduct.liftEquiv.symm.injective
    apply Subtype.ext
    rw [Algebra.TensorProduct.liftEquiv_symm_apply_coe, Prod.mk.injEq]
    constructor
    · ext a
      simp [map_one, mul_one, ← hm (Discrete.mk WalkingPair.left)]
    · ext b
      simp [map_one, ← hm (Discrete.mk WalkingPair.right)]

/-- The limit cone of the tensor product `A ⊗[ℤ] B` in `CommRingCat`. -/
def coproductColimitCocone : Limits.ColimitCocone (pair A B) :=
  ⟨_, coproductCoconeIsColimit A B⟩

end BinaryCoproduct


section Terminal

instance (X : CommRingCat.{u}) : Unique (X ⟶ CommRingCat.of.{u} PUnit) :=
  ⟨⟨ofHom <| ⟨1, rfl, by simp⟩⟩, fun f ↦ by ext⟩

/-- The trivial ring is the (strict) terminal object of `CommRingCat`. -/
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) :=
  IsTerminal.ofUnique _

instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} := by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨ofHom ⟨1, rfl, by simp⟩, ?_, ?_⟩
  · ext
  · ext x
    have e : (0 : X) = 1 := by
      rw [← f.hom.map_one, ← f.hom.map_zero]
    replace e : 0 * x = 1 * x := congr_arg (· * x) e
    rw [one_mul, zero_mul, ← f.hom.map_zero] at e
    exact e

theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

/-- `ℤ` is the initial object of `CommRingCat`. -/
def zIsInitial : IsInitial (CommRingCat.of ℤ) :=
  IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| Int.castRingHom R⟩,
    fun a => hom_ext <| a.hom.ext_int _⟩)

/-- `ULift.{u} ℤ` is initial in `CommRingCat`. -/
def isInitial : IsInitial (CommRingCat.of (ULift.{u} ℤ)) :=
  IsInitial.ofUnique (h := fun R ↦ ⟨⟨ofHom <| (Int.castRingHom R).comp ULift.ringEquiv.toRingHom⟩,
    fun _ ↦ by
      ext : 1
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0, u} (R := ℤ)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int⟩)

end Terminal

section Product

variable (A B : CommRingCat.{u})

/-- The product in `CommRingCat` is the Cartesian product. This is the binary fan. -/
@[simps! pt]
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The product in `CommRingCat` is the Cartesian product. -/
def prodFanIsLimit : IsLimit (prodFan A B) where
  lift c := ofHom <| RingHom.prod (c.π.app ⟨WalkingPair.left⟩).hom (c.π.app ⟨WalkingPair.right⟩).hom
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right] <;> rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    have eq1 : (m ≫ (A.prodFan B).fst) x = (BinaryFan.fst s) x :=
      ConcreteCategory.congr_hom (h ⟨WalkingPair.left⟩) x
    have eq2 : (m ≫ (A.prodFan B).snd) x = (BinaryFan.snd s) x :=
      ConcreteCategory.congr_hom (h ⟨WalkingPair.right⟩) x
    rw [← eq1, ← eq2]
    simp [prodFan]

end Product

section Pi

variable {ι : Type u} (R : ι → CommRingCat.{u})

/--
The categorical product of rings is the Cartesian product of rings. This is its `Fan`.
-/
@[simps! pt]
def piFan : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) → R i)) (fun i ↦ ofHom <| Pi.evalRingHom _ i)

/--
The categorical product of rings is the Cartesian product of rings.
-/
def piFanIsLimit : IsLimit (piFan R) where
  lift s := ofHom <| RingHom.pi fun i ↦ (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
  uniq _ _ h := hom_ext <| DFunLike.ext _ _ fun x ↦ funext fun i ↦
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

/--
The categorical product and the usual product agree
-/
noncomputable def piIsoPi : ∏ᶜ R ≅ CommRingCat.of ((i : ι) → R i) :=
  limit.isoLimitCone ⟨_, piFanIsLimit R⟩

/--
The categorical product and the usual product agree
-/
noncomputable def _root_.RingEquiv.piEquivPi (R : ι → Type u) [∀ i, CommRing (R i)] :
    (∏ᶜ (fun i : ι ↦ CommRingCat.of (R i)) : CommRingCat.{u}) ≃+* ((i : ι) → R i) :=
  (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv

end Pi

namespace Limits

variable {J : Type u'} [SmallCategory J] (F : J ⥤ CommRingCat.{u}) {c : Cone F}

set_option backward.isDefEq.respectTransparency false in
theorem isUnit_iff_forall_isUnit (hc : IsLimit c) (r : c.pt) : IsUnit r ↔
    ∀ (j : J), IsUnit (c.π.app j r) := by
  refine ⟨fun h _ ↦ h.map _, fun h ↦ ?_⟩
  simp only [isUnit_iff_exists_inv] at h ⊢
  choose inv h_inv using h
  have map_inv {j k : J} (f : j ⟶ k) : F.map f (inv j) = inv k := by
    have h := congr(F.map f $(h_inv j))
    have : F.map f (c.π.app j r) = c.π.app k r :=
      DFunLike.congr_fun (congr(Hom.hom $(c.w f))) r
    rw [map_mul, map_one, this] at h
    rw [← mul_one (F.map f (inv j)), ← h_inv k, ← mul_assoc]
    nth_rw 2 [mul_comm]; rw [h, one_mul]
  let inv_r : Cone F := .mk (CommRingCat.of (FreeCommRing PUnit)) {
    app j := ConcreteCategory.ofHom (FreeCommRing.lift (fun _ ↦ inv j))
    naturality j k f := by
      ext1; change FreeCommRing.lift (fun _ => inv k) = _
      ext; simp [map_inv f] }
  use hc.lift inv_r (FreeCommRing.of PUnit.unit)
  refine Concrete.isLimit_ext _ hc _ _ fun j ↦ ?_
  rw [RingHom.map_mul, RingHom.map_one]; convert h_inv j
  change (hc.lift inv_r ≫ c.π.app j) (FreeCommRing.of PUnit.unit) = inv j
  rw [IsLimit.fac]; exact FreeCommRing.lift_of ..

-- The assumption `hj` can be generalized to a zigzag-like assumption of finite steps.
theorem π_isLocalHom (hc : IsLimit c) (j : J) (hj : ∀ (x : c.pt), IsUnit (c.π.app j x) →
    ∀ (i : J), ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), IsLocalHom (F.map f).hom ∧
      F.map f (c.π.app i x) = F.map g (c.π.app j x)) :
    IsLocalHom (c.π.app j).hom := by
  refine ⟨fun (x : c.pt) hx ↦ (?_ : IsUnit x)⟩
  rw [isUnit_iff_forall_isUnit F hc]; intro i
  obtain ⟨k, f, g, lh, eq⟩ := hj x hx i
  exact lh.map_nonunit _ (eq ▸ hx.map _)

theorem isLocalRing (hc : IsLimit c) (j : J) [IsLocalRing (F.obj j)]
    (hj : ∀ (x : c.pt), IsUnit (c.π.app j x) → ∀ (i : J), ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      IsLocalHom (F.map f).hom ∧ F.map f (c.π.app i x) = F.map g (c.π.app j x)) :
    IsLocalRing c.pt := by
  have := π_isLocalHom F hc j hj
  apply RingHom.domain_isLocalRing (c.π.app j).hom

end Limits

section Equalizer

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

/-- The equalizer in `CommRingCat` is the equalizer as sets. This is the equalizer fork. -/
def equalizerFork : Fork f g :=
  Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f.hom g.hom).subtype) <| by
      ext ⟨x, e⟩
      simpa using e

/-- The equalizer in `CommRingCat` is the equalizer as sets. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
  use ofHom <| s.ι.hom.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x :)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
    exact Subtype.ext <| RingHom.congr_fun (congrArg Hom.hom hm) x

instance : IsLocalHom (equalizerFork f g).ι.hom :=
  inferInstanceAs <| IsLocalHom (f.hom.eqLocus g.hom).subtype

open WalkingParallelPair WalkingParallelPairHom Opposite

instance equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) zero fun x hx i ↦ ?_
  rcases i with _ | _
  · exact ⟨zero, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, 𝟙 _, left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π, RingHom.id_apply]
    exact (limit.w_apply F left x).symm

theorem equalizer_limit_isLocalRing (F : WalkingParallelPair ⥤ CommRingCat.{u})
    [IsLocalRing (F.obj zero)] : IsLocalRing ↑(limit F) :=
  RingHom.domain_isLocalRing (limit.π F WalkingParallelPair.zero).hom

instance equalizer_ι_isLocalHom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F (op one)).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) (op one) fun x hx i ↦ ?_
  rcases i with _ | _
  · refine ⟨op zero, 𝟙 _, op left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π,
      RingHom.id_apply]
    exact (limit.w_apply F (op left) x).symm
  · exact ⟨op one, 𝟙 _, 𝟙 _, inferInstance, by simp⟩

end Equalizer

section Pullback

variable {A B C : CommRingCat.{u}}

/-- In the category of `CommRingCat`, the pullback of `f : A ⟶ C` and `g : B ⟶ C` is the `eqLocus`
of the two maps `A × B ⟶ C`. This is the constructed pullback cone.
-/
def pullbackCone (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (by
      ext ⟨x, e⟩
      simpa [CommRingCat.ofHom] using e)

/-- The constructed pullback cone is indeed the limit. -/
def pullbackConeIsLimit (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) := by
  fapply PullbackCone.IsLimit.mk
  · intro s
    refine ofHom ((s.fst.hom.prod s.snd.hom).codRestrict _ ?_)
    intro x
    exact congr_arg (fun f : s.pt →+* C => f x) (congrArg Hom.hom s.condition)
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
    refine hom_ext <| RingHom.ext fun (x : s.pt) => Subtype.ext ?_
    change (m x).1 = (_, _)
    have eq1 := (congr_arg (fun f : s.pt →+* A => f x) (congrArg Hom.hom e₁) :)
    have eq2 := (congr_arg (fun f : s.pt →+* B => f x) (congrArg Hom.hom e₂) :)
    rw [← eq1, ← eq2]
    rfl

open WalkingCospan

instance pullbackFst_isLocalHom (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] :
    IsLocalHom (pullback.fst f g).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) left fun x hx i ↦ ?_
  rcases i with _ | _ | _
  · exact ⟨one, 𝟙 _, Hom.inl, inferInstance, by simp; rfl⟩
  · exact ⟨left, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, Hom.inr, Hom.inl, ‹_›, ?_⟩
    exact DFunLike.congr_fun (congr(Hom.hom $(pullback.condition (f := f) (g := g)))) x |>.symm

theorem pullback_isLocalRing (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] [IsLocalRing A] :
    IsLocalRing ↑(pullback f g) :=
  RingHom.domain_isLocalRing (pullback.fst f g).hom

end Pullback

end CommRingCat
