/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.Algebra.Ring.Subring.Basic

#align_import algebra.category.Ring.constructions from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CommRingCat

section Pushout

variable {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B)

/-- The explicit cocone with tensor products as the fibered product in `CommRingCat`. -/
def pushoutCocone : Limits.PushoutCocone f g := by
  letI := RingHom.toAlgebra f
  letI := RingHom.toAlgebra g
  fapply Limits.PushoutCocone.mk
  · show CommRingCat; exact CommRingCat.of (A ⊗[R] B)
  · show A ⟶ _; exact Algebra.TensorProduct.includeLeftRingHom
  · show B ⟶ _; exact Algebra.TensorProduct.includeRight.toRingHom
  · ext r
    trans algebraMap R (A ⊗[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone CommRingCat.pushoutCocone

@[simp]
theorem pushoutCocone_inl :
    (pushoutCocone f g).inl = by
      letI := f.toAlgebra
      letI := g.toAlgebra
      exact Algebra.TensorProduct.includeLeftRingHom :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_inl CommRingCat.pushoutCocone_inl

@[simp]
theorem pushoutCocone_inr :
    (pushoutCocone f g).inr = by
      letI := f.toAlgebra
      letI := g.toAlgebra
      exact Algebra.TensorProduct.includeRight.toRingHom :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_inr CommRingCat.pushoutCocone_inr

@[simp]
theorem pushoutCocone_pt :
    (pushoutCocone f g).pt = by
      letI := f.toAlgebra
      letI := g.toAlgebra
      exact CommRingCat.of (A ⊗[R] B) :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_X CommRingCat.pushoutCocone_pt

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone f g) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra f
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra (f ≫ s.inl)
    let f' : A →ₐ[R] s.pt :=
      { s.inl with
        commutes' := fun r => rfl }
    let g' : B →ₐ[R] s.pt :=
      { s.inr with
        commutes' := fun r => by
          change (g ≫ s.inr) r = (f ≫ s.inl) r
          congr 1
          exact
            (s.ι.naturality Limits.WalkingSpan.Hom.snd).trans
              (s.ι.naturality Limits.WalkingSpan.Hom.fst).symm }
    -- Porting note: Lean has forget why `A ⊗[R] B` makes sense
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R B := g.toAlgebra
    letI : Algebra R (pushoutCocone f g).pt := show Algebra R (A ⊗[R] B) by infer_instance
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    constructor
    · ext x
      -- Porting note: Lean can't see through `forget` functor
      letI : Semiring ((forget CommRingCat).obj A) := A.str.toSemiring
      letI : Algebra R ((forget CommRingCat).obj A) := show Algebra R A by infer_instance
      exact Algebra.TensorProduct.productMap_left_apply _ _ x
    constructor
    · ext x
      -- Porting note: Lean can't see through `forget` functor
      letI : Semiring ((forget CommRingCat).obj B) := B.str.toSemiring
      letI : Algebra R ((forget CommRingCat).obj B) := show Algebra R B by infer_instance
      exact Algebra.TensorProduct.productMap_right_apply _ _ x
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.pt :=
      { h with
        commutes' := fun r => by
          change h (f r ⊗ₜ[R] 1) = s.inl (f r)
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
    rw [← h.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_is_colimit CommRingCat.pushoutCoconeIsColimit

end Pushout

section Terminal

/-- The trivial ring is the (strict) terminal object of `CommRingCat`. -/
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) := by
  refine IsTerminal.ofUnique (h := fun X => ⟨⟨⟨⟨1, rfl⟩, fun _ _ => rfl⟩, ?_, ?_⟩, ?_⟩)
  · rfl
  · intros; simp; ext
  · intros f; ext; rfl
set_option linter.uppercaseLean3 false in
#align CommRing.punit_is_terminal CommRingCat.punitIsTerminal

instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} := by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨⟨⟨1, rfl, fun _ _ => rfl⟩, by ext; rfl, ?_⟩⟩
  ext x
  have e : (0 : X) = 1 := by
    rw [← f.map_one, ← f.map_zero]
    congr
  replace e : 0 * x = 1 * x := congr_arg (· * x) e
  rw [one_mul, zero_mul, ← f.map_zero] at e
  exact e
set_option linter.uppercaseLean3 false in
#align CommRing.CommRing_has_strict_terminal_objects CommRingCat.commRingCat_hasStrictTerminalObjects

theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)
set_option linter.uppercaseLean3 false in
#align CommRing.subsingleton_of_is_terminal CommRingCat.subsingleton_of_isTerminal

/-- `ℤ` is the initial object of `CommRingCat`. -/
def zIsInitial : IsInitial (CommRingCat.of ℤ) :=
  IsInitial.ofUnique (h := fun R => ⟨⟨Int.castRingHom R⟩, fun a => a.ext_int _⟩)
set_option linter.uppercaseLean3 false in
#align CommRing.Z_is_initial CommRingCat.zIsInitial

end Terminal

section Product

variable (A B : CommRingCat.{u})

/-- The product in `CommRingCat` is the cartesian product. This is the binary fan. -/
@[simps! pt]
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)
set_option linter.uppercaseLean3 false in
#align CommRing.prod_fan CommRingCat.prodFan

/-- The product in `CommRingCat` is the cartesian product. -/
def prodFanIsLimit : IsLimit (prodFan A B) where
  lift c := RingHom.prod (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩)
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right,
      FunctorToTypes.map_comp_apply, forget_map, coe_of, RingHom.prod_apply] <;>
    rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    have eq1 := congr_hom (h ⟨WalkingPair.left⟩) x
    have eq2 := congr_hom (h ⟨WalkingPair.right⟩) x
    dsimp at eq1 eq2
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [← eq1, ← eq2]
    rfl
set_option linter.uppercaseLean3 false in
#align CommRing.prod_fan_is_limit CommRingCat.prodFanIsLimit

end Product

section Pi

variable {ι : Type u} (R : ι → CommRingCat.{u})

/--
The categorical product of rings is the cartesian product of rings. This is its `Fan`.
-/
@[simps! pt]
def piFan : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) → R i)) (Pi.evalRingHom _)

/--
The categorical product of rings is the cartesian product of rings.
-/
def piFanIsLimit : IsLimit (piFan R) where
  lift s := Pi.ringHom fun i ↦ s.π.1 ⟨i⟩
  fac s i := by rfl
  uniq s g h := DFunLike.ext _ _ fun x ↦ funext fun i ↦ DFunLike.congr_fun (h ⟨i⟩) x

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
  Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f g).subtype) <| by
      ext ⟨x, e⟩
      simpa using e
set_option linter.uppercaseLean3 false in
#align CommRing.equalizer_fork CommRingCat.equalizerFork

/-- The equalizer in `CommRingCat` is the equalizer as sets. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
  -- Porting note: Lean can't see through `(parallelPair f g).obj zero`
  haveI : SubsemiringClass (Subring A) ((parallelPair f g).obj WalkingParallelPair.zero) :=
    show SubsemiringClass (Subring A) A by infer_instance
  use s.ι.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x : _)
  constructor
  · ext
    rfl
  · intro m hm
    exact RingHom.ext fun x => Subtype.ext <| ConcreteCategory.congr_hom hm x
set_option linter.uppercaseLean3 false in
#align CommRing.equalizer_fork_is_limit CommRingCat.equalizerForkIsLimit

instance : IsLocalRingHom (equalizerFork f g).ι := by
  constructor
  rintro ⟨a, h₁ : _ = _⟩ (⟨⟨x, y, h₃, h₄⟩, rfl : x = _⟩ : IsUnit a)
  have : y ∈ RingHom.eqLocus f g := by
    apply (f.isUnit_map ⟨⟨x, y, h₃, h₄⟩, rfl⟩ : IsUnit (f x)).mul_left_inj.mp
    conv_rhs => rw [h₁]
    rw [← f.map_mul, ← g.map_mul, h₄, f.map_one, g.map_one]
  rw [isUnit_iff_exists_inv]
  exact ⟨⟨y, this⟩, Subtype.eq h₃⟩

instance equalizer_ι_isLocalRingHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalRingHom (limit.π F WalkingParallelPair.zero) := by
  have := limMap_π (diagramIsoParallelPair F).hom WalkingParallelPair.zero
  rw [← IsIso.comp_inv_eq] at this
  rw [← this]
  rw [← limit.isoLimitCone_hom_π
      ⟨_,
        equalizerForkIsLimit (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)⟩
      WalkingParallelPair.zero]
  change IsLocalRingHom ((lim.map _ ≫ _ ≫ (equalizerFork _ _).ι) ≫ _)
  infer_instance
set_option linter.uppercaseLean3 false in
#align CommRing.equalizer_ι_is_local_ring_hom CommRingCat.equalizer_ι_isLocalRingHom

open CategoryTheory.Limits.WalkingParallelPair Opposite

open CategoryTheory.Limits.WalkingParallelPairHom

instance equalizer_ι_is_local_ring_hom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalRingHom (limit.π F (Opposite.op WalkingParallelPair.one)) := by
  have : _ = limit.π F (walkingParallelPairOpEquiv.functor.obj _) :=
    (limit.isoLimitCone_inv_π
        ⟨_, IsLimit.whiskerEquivalence (limit.isLimit F) walkingParallelPairOpEquiv⟩
        WalkingParallelPair.zero : _)
  erw [← this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align CommRing.equalizer_ι_is_local_ring_hom' CommRingCat.equalizer_ι_is_local_ring_hom'

end Equalizer

section Pullback

/-- In the category of `CommRingCat`, the pullback of `f : A ⟶ C` and `g : B ⟶ C` is the `eqLocus`
of the two maps `A × B ⟶ C`. This is the constructed pullback cone.
-/
def pullbackCone {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))).subtype)
    (by
      ext ⟨x, e⟩
      simpa [CommRingCat.ofHom] using e)
set_option linter.uppercaseLean3 false in
#align CommRing.pullback_cone CommRingCat.pullbackCone

/-- The constructed pullback cone is indeed the limit. -/
def pullbackConeIsLimit {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) := by
  fapply PullbackCone.IsLimit.mk
  · intro s
    apply (s.fst.prod s.snd).codRestrict
    intro x
    exact congr_arg (fun f : s.pt →+* C => f x) s.condition
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
    refine RingHom.ext fun (x : s.pt) => Subtype.ext ?_
    change (m x).1 = (_, _)
    have eq1 := (congr_arg (fun f : s.pt →+* A => f x) e₁ : _)
    have eq2 := (congr_arg (fun f : s.pt →+* B => f x) e₂ : _)
    rw [← eq1, ← eq2]
    rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pullback_cone_is_limit CommRingCat.pullbackConeIsLimit

end Pullback

end CommRingCat
