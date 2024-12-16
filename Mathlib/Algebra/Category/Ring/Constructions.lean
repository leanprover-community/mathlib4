/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Constructions of (co)limits in `CommRingCat`

In this file we provide the explicit (co)cones for various (co)limits in `CommRingCat`, including
* tensor product is the pushout
* `Z` is the initial object
* `0` is the strict terminal object
* cartesian product is the product
* arbitrary direct product of a family of rings is the product object (Pi object)
* `RingHom.eqLocus` is the equalizer

-/

suppress_compilation

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
          simp only [pushoutCocone_pt, coe_of, AlgHom.toRingHom_eq_coe]
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

end Pushout

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
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0, u} (α := ℤ)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int⟩)

end Terminal

section Product

variable (A B : CommRingCat.{u})

/-- The product in `CommRingCat` is the cartesian product. This is the binary fan. -/
@[simps! pt]
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)

/-- The product in `CommRingCat` is the cartesian product. -/
def prodFanIsLimit : IsLimit (prodFan A B) where
  lift c := ofHom <| RingHom.prod (c.π.app ⟨WalkingPair.left⟩).hom (c.π.app ⟨WalkingPair.right⟩).hom
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right,
      FunctorToTypes.map_comp_apply, forget_map, coe_of, RingHom.prod_apply] <;>
    rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    have eq1 : (m ≫ (A.prodFan B).fst) x = (BinaryFan.fst s) x :=
      congr_hom (h ⟨WalkingPair.left⟩) x
    have eq2 : (m ≫ (A.prodFan B).snd) x = (BinaryFan.snd s) x :=
      congr_hom (h ⟨WalkingPair.right⟩) x
    rw [← eq1, ← eq2]
    simp [prodFan]

end Product

section Pi

variable {ι : Type u} (R : ι → CommRingCat.{u})

/--
The categorical product of rings is the cartesian product of rings. This is its `Fan`.
-/
@[simps! pt]
def piFan : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) → R i)) (fun i ↦ ofHom <| Pi.evalRingHom _ i)

/--
The categorical product of rings is the cartesian product of rings.
-/
def piFanIsLimit : IsLimit (piFan R) where
  lift s := ofHom <| Pi.ringHom fun i ↦ (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
  uniq _ _ h := hom_ext <| DFunLike.ext _ _ fun x ↦ funext fun i ↦
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

/--
The categorical product and the usual product agrees
-/
def piIsoPi : ∏ᶜ R ≅ CommRingCat.of ((i : ι) → R i) :=
  limit.isoLimitCone ⟨_, piFanIsLimit R⟩

/--
The categorical product and the usual product agrees
-/
def _root_.RingEquiv.piEquivPi (R : ι → Type u) [∀ i, CommRing (R i)] :
    (∏ᶜ (fun i : ι ↦ CommRingCat.of (R i)) : CommRingCat.{u}) ≃+* ((i : ι) → R i) :=
  (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv

end Pi

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
  use ofHom <| s.ι.hom.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x : _)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
    exact Subtype.ext <| RingHom.congr_fun (congrArg Hom.hom hm) x

instance : IsLocalHom (equalizerFork f g).ι.hom := by
  constructor
  rintro ⟨a, h₁ : _ = _⟩ (⟨⟨x, y, h₃, h₄⟩, rfl : x = _⟩ : IsUnit a)
  have : y ∈ RingHom.eqLocus f.hom g.hom := by
    apply (f.hom.isUnit_map ⟨⟨x, y, h₃, h₄⟩, rfl⟩ : IsUnit (f x)).mul_left_inj.mp
    conv_rhs => rw [h₁]
    rw [← f.hom.map_mul, ← g.hom.map_mul, h₄, f.hom.map_one, g.hom.map_one]
  rw [isUnit_iff_exists_inv]
  exact ⟨⟨y, this⟩, Subtype.eq h₃⟩

@[instance]
theorem equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero).hom := by
  have := limMap_π (diagramIsoParallelPair F).hom WalkingParallelPair.zero
  rw [← IsIso.comp_inv_eq] at this
  rw [← this]
  rw [← limit.isoLimitCone_hom_π
      ⟨_,
        equalizerForkIsLimit (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)⟩
      WalkingParallelPair.zero]
  change IsLocalHom ((lim.map _ ≫ _ ≫ (equalizerFork _ _).ι) ≫ _).hom
  infer_instance

@[deprecated (since := "2024-10-10")]
alias equalizer_ι_isLocalRingHom := equalizer_ι_isLocalHom

open CategoryTheory.Limits.WalkingParallelPair Opposite

open CategoryTheory.Limits.WalkingParallelPairHom

instance equalizer_ι_is_local_ring_hom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F (Opposite.op WalkingParallelPair.one)).hom := by
  have : _ = limit.π F (walkingParallelPairOpEquiv.functor.obj _) :=
    (limit.isoLimitCone_inv_π
        ⟨_, IsLimit.whiskerEquivalence (limit.isLimit F) walkingParallelPairOpEquiv⟩
        WalkingParallelPair.zero : _)
  erw [← this]
  -- note: this was not needed before https://github.com/leanprover-community/mathlib4/pull/19757
  haveI : IsLocalHom (limit.π (walkingParallelPairOpEquiv.functor ⋙ F) zero).hom := by
    infer_instance
  infer_instance

end Equalizer

section Pullback

/-- In the category of `CommRingCat`, the pullback of `f : A ⟶ C` and `g : B ⟶ C` is the `eqLocus`
of the two maps `A × B ⟶ C`. This is the constructed pullback cone.
-/
def pullbackCone {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
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
def pullbackConeIsLimit {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) :
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
    have eq1 := (congr_arg (fun f : s.pt →+* A => f x) (congrArg Hom.hom e₁) : _)
    have eq2 := (congr_arg (fun f : s.pt →+* B => f x) (congrArg Hom.hom e₂) : _)
    rw [← eq1, ← eq2]
    rfl

end Pullback

end CommRingCat
