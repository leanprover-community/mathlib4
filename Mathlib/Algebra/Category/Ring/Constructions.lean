/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebra.category.Ring.constructions
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.RingTheory.TensorProduct
import Mathbin.Algebra.Category.Ring.Limits
import Mathbin.Algebra.Category.Ring.Instances
import Mathbin.CategoryTheory.Limits.Shapes.StrictInitial
import Mathbin.RingTheory.Subring.Basic

/-!
# Constructions of (co)limits in CommRing

In this file we provide the explicit (co)cones for various (co)limits in `CommRing`, including
* tensor product is the pushout
* `Z` is the initial object
* `0` is the strict terminal object
* cartesian product is the product
* `ring_hom.eq_locus` is the equalizer

-/


universe u u'

open CategoryTheory CategoryTheory.Limits

open TensorProduct

namespace CommRingCat

section Pushout

variable {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B)

/-- The explicit cocone with tensor products as the fibered product in `CommRing`. -/
def pushoutCocone : Limits.PushoutCocone f g :=
  by
  letI := RingHom.toAlgebra f
  letI := RingHom.toAlgebra g
  apply limits.pushout_cocone.mk
  show CommRingCat; exact CommRingCat.of (A ⊗[R] B)
  show A ⟶ _; exact algebra.tensor_product.include_left.to_ring_hom
  show B ⟶ _; exact algebra.tensor_product.include_right.to_ring_hom
  ext r
  trans algebraMap R (A ⊗[R] B) r
  · exact algebra.tensor_product.include_left.commutes r
  · exact (algebra.tensor_product.include_right.commutes r).symm
#align CommRing.pushout_cocone CommRingCat.pushoutCocone

@[simp]
theorem pushoutCocone_inl :
    (pushoutCocone f g).inl = by
      letI := f.to_algebra
      letI := g.to_algebra
      exact algebra.tensor_product.include_left.to_ring_hom :=
  rfl
#align CommRing.pushout_cocone_inl CommRingCat.pushoutCocone_inl

@[simp]
theorem pushoutCocone_inr :
    (pushoutCocone f g).inr = by
      letI := f.to_algebra
      letI := g.to_algebra
      exact algebra.tensor_product.include_right.to_ring_hom :=
  rfl
#align CommRing.pushout_cocone_inr CommRingCat.pushoutCocone_inr

@[simp]
theorem pushoutCocone_pt :
    (pushoutCocone f g).pt = by
      letI := f.to_algebra
      letI := g.to_algebra
      exact CommRingCat.of (A ⊗[R] B) :=
  rfl
#align CommRing.pushout_cocone_X CommRingCat.pushoutCocone_pt

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone f g) :=
  Limits.PushoutCocone.isColimitAux' _ fun s =>
    by
    letI := RingHom.toAlgebra f
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra (f ≫ s.inl)
    let f' : A →ₐ[R] s.X :=
      { s.inl with
        commutes' := fun r => by
          change s.inl.to_fun (f r) = (f ≫ s.inl) r
          rfl }
    let g' : B →ₐ[R] s.X :=
      { s.inr with
        commutes' := fun r => by
          change (g ≫ s.inr) r = (f ≫ s.inl) r
          congr 1
          exact
            (s.ι.naturality limits.walking_span.hom.snd).trans
              (s.ι.naturality limits.walking_span.hom.fst).symm }
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
    simp only [pushout_cocone_inl, pushout_cocone_inr]
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_left_apply _ _ x
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_right_apply _ _ x
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.X :=
      { h with
        commutes' := fun r => by
          change h (f r ⊗ₜ[R] 1) = s.inl (f r)
          rw [← eq1]
          simp }
    suffices h' = Algebra.TensorProduct.productMap f' g'
      by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext
    intro a b
    simp [← eq1, ← eq2, ← h.map_mul]
#align CommRing.pushout_cocone_is_colimit CommRingCat.pushoutCoconeIsColimit

end Pushout

section Terminal

/-- The trivial ring is the (strict) terminal object of `CommRing`. -/
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) :=
  by
  apply (config := { instances := false }) is_terminal.of_unique
  tidy
#align CommRing.punit_is_terminal CommRingCat.punitIsTerminal

instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} :=
  by
  apply has_strict_terminal_objects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine' ⟨⟨by tidy, by ext, _⟩⟩
  ext
  have e : (0 : X) = 1 := by
    rw [← f.map_one, ← f.map_zero]
    congr
  replace e : 0 * x = 1 * x := congr_arg (fun a => a * x) e
  rw [one_mul, MulZeroClass.zero_mul, ← f.map_zero] at e
  exact e
#align CommRing.CommRing_has_strict_terminal_objects CommRingCat.commRingCat_hasStrictTerminalObjects

theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)
#align CommRing.subsingleton_of_is_terminal CommRingCat.subsingleton_of_isTerminal

/-- `ℤ` is the initial object of `CommRing`. -/
def zIsInitial : IsInitial (CommRingCat.of ℤ) :=
  by
  apply (config := { instances := false }) is_initial.of_unique
  exact fun R => ⟨⟨Int.castRingHom R⟩, fun a => a.ext_int _⟩
#align CommRing.Z_is_initial CommRingCat.zIsInitial

end Terminal

section Product

variable (A B : CommRingCat.{u})

/-- The product in `CommRing` is the cartesian product. This is the binary fan. -/
@[simps pt]
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)
#align CommRing.prod_fan CommRingCat.prodFan

/-- The product in `CommRing` is the cartesian product. -/
def prodFanIsLimit : IsLimit (prodFan A B)
    where
  lift c := RingHom.prod (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩)
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
      simpa only [binary_fan.π_app_left, binary_fan.π_app_right, comp_apply, RingHom.prod_apply]
  uniq s m h := by
    ext
    · simpa using congr_hom (h ⟨walking_pair.left⟩) x
    · simpa using congr_hom (h ⟨walking_pair.right⟩) x
#align CommRing.prod_fan_is_limit CommRingCat.prodFanIsLimit

end Product

section Equalizer

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

/-- The equalizer in `CommRing` is the equalizer as sets. This is the equalizer fork. -/
def equalizerFork : Fork f g :=
  Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f g).Subtype)
    (by
      ext ⟨x, e⟩
      simpa using e)
#align CommRing.equalizer_fork CommRingCat.equalizerFork

/-- The equalizer in `CommRing` is the equalizer as sets. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) :=
  by
  fapply fork.is_limit.mk'
  intro s
  use s.ι.cod_restrict _ fun x => (concrete_category.congr_hom s.condition x : _)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
    exact concrete_category.congr_hom hm x
#align CommRing.equalizer_fork_is_limit CommRingCat.equalizerForkIsLimit

instance : IsLocalRingHom (equalizerFork f g).ι :=
  by
  constructor
  rintro ⟨a, h₁ : _ = _⟩ (⟨⟨x, y, h₃, h₄⟩, rfl : x = _⟩ : IsUnit a)
  have : y ∈ RingHom.eqLocus f g :=
    by
    apply (f.is_unit_map ⟨⟨x, y, h₃, h₄⟩, rfl⟩ : IsUnit (f x)).mul_left_inj.mp
    conv_rhs => rw [h₁]
    rw [← f.map_mul, ← g.map_mul, h₄, f.map_one, g.map_one]
  rw [isUnit_iff_exists_inv]
  exact ⟨⟨y, this⟩, Subtype.eq h₃⟩

instance equalizer_ι_isLocalRingHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalRingHom (limit.π F WalkingParallelPair.zero) :=
  by
  have := lim_map_π (diagram_iso_parallel_pair F).Hom walking_parallel_pair.zero
  rw [← is_iso.comp_inv_eq] at this
  rw [← this]
  rw [←
    limit.iso_limit_cone_hom_π
      ⟨_,
        equalizer_fork_is_limit (F.map walking_parallel_pair_hom.left)
          (F.map walking_parallel_pair_hom.right)⟩
      walking_parallel_pair.zero]
  change IsLocalRingHom ((lim.map _ ≫ _ ≫ (equalizer_fork _ _).ι) ≫ _)
  infer_instance
#align CommRing.equalizer_ι_is_local_ring_hom CommRingCat.equalizer_ι_isLocalRingHom

open CategoryTheory.Limits.WalkingParallelPair Opposite

open CategoryTheory.Limits.WalkingParallelPairHom

instance equalizer_ι_is_local_ring_hom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalRingHom (limit.π F (Opposite.op WalkingParallelPair.one)) :=
  by
  have : _ = limit.π F (walking_parallel_pair_op_equiv.functor.obj _) :=
    (limit.iso_limit_cone_inv_π
        ⟨_, is_limit.whisker_equivalence (limit.is_limit F) walking_parallel_pair_op_equiv⟩
        walking_parallel_pair.zero :
      _)
  erw [← this]
  infer_instance
#align CommRing.equalizer_ι_is_local_ring_hom' CommRingCat.equalizer_ι_is_local_ring_hom'

end Equalizer

section Pullback

/-- In the category of `CommRing`, the pullback of `f : A ⟶ C` and `g : B ⟶ C` is the `eq_locus` of
the two maps `A × B ⟶ C`. This is the constructed pullback cone.
-/
def pullbackCone {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))).Subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))).Subtype)
    (by
      ext ⟨x, e⟩
      simpa [CommRingCat.ofHom] using e)
#align CommRing.pullback_cone CommRingCat.pullbackCone

/-- The constructed pullback cone is indeed the limit. -/
def pullbackConeIsLimit {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) :=
  by
  fapply pullback_cone.is_limit.mk
  · intro s
    apply (s.fst.prod s.snd).codRestrict
    intro x
    exact congr_arg (fun f : s.X →+* C => f x) s.condition
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
    ext
    · exact (congr_arg (fun f : s.X →+* A => f x) e₁ : _)
    · exact (congr_arg (fun f : s.X →+* B => f x) e₂ : _)
#align CommRing.pullback_cone_is_limit CommRingCat.pullbackConeIsLimit

end Pullback

end CommRingCat

