/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.RingTheory.Subring.Basic

#align_import algebra.category.Ring.constructions from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Constructions of (co)limits in `CommRingCat`

In this file we provide the explicit (co)cones for various (co)limits in `CommRingCat`, including
* tensor product is the pushout
* `Z` is the initial object
* `0` is the strict terminal object
* cartesian product is the product
* `RingHom.eqLocus` is the equalizer

-/


universe u u'

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CommRingCat

section Pushout

variable {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B)

/-- The explicit cocone with tensor products as the fibered product in `CommRingCat`. -/
def pushoutCocone : Limits.PushoutCocone f g := by
  letI := RingHom.toAlgebra f
  -- ⊢ PushoutCocone f g
  letI := RingHom.toAlgebra g
  -- ⊢ PushoutCocone f g
  fapply Limits.PushoutCocone.mk
  show CommRingCat; exact CommRingCat.of (A ⊗[R] B)
  show A ⟶ _; exact Algebra.TensorProduct.includeLeftRingHom
  show B ⟶ _; exact Algebra.TensorProduct.includeRight.toRingHom
              -- ⊢ (f ≫
  ext r
  -- ⊢ ↑(f ≫
  trans algebraMap R (A ⊗[R] B) r
  · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    -- 🎉 no goals
  · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone CommRingCat.pushoutCocone

@[simp]
theorem pushoutCocone_inl :
    (pushoutCocone f g).inl = by
      letI := f.toAlgebra
      -- ⊢ A ⟶ (pushoutCocone f g).pt
      letI := g.toAlgebra
      -- ⊢ A ⟶ (pushoutCocone f g).pt
      exact Algebra.TensorProduct.includeLeftRingHom :=
      -- 🎉 no goals
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_inl CommRingCat.pushoutCocone_inl

@[simp]
theorem pushoutCocone_inr :
    (pushoutCocone f g).inr = by
      letI := f.toAlgebra
      -- ⊢ B ⟶ (pushoutCocone f g).pt
      letI := g.toAlgebra
      -- ⊢ B ⟶ (pushoutCocone f g).pt
      exact Algebra.TensorProduct.includeRight.toRingHom :=
      -- 🎉 no goals
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_inr CommRingCat.pushoutCocone_inr

@[simp]
theorem pushoutCocone_pt :
    (pushoutCocone f g).pt = by
      letI := f.toAlgebra
      -- ⊢ CommRingCat
      letI := g.toAlgebra
      -- ⊢ CommRingCat
      exact CommRingCat.of (A ⊗[R] B) :=
      -- 🎉 no goals
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_X CommRingCat.pushoutCocone_pt

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone f g) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra f
    -- ⊢ { l // PushoutCocone.inl (pushoutCocone f g) ≫ l = PushoutCocone.inl s ∧ Pus …
    letI := RingHom.toAlgebra g
    -- ⊢ { l // PushoutCocone.inl (pushoutCocone f g) ≫ l = PushoutCocone.inl s ∧ Pus …
    letI := RingHom.toAlgebra (f ≫ s.inl)
    -- ⊢ { l // PushoutCocone.inl (pushoutCocone f g) ≫ l = PushoutCocone.inl s ∧ Pus …
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
    -- Porting note : Lean has forget why `A ⊗[R] B` makes sense
    letI : Algebra R A := f.toAlgebra
    -- ⊢ { l // PushoutCocone.inl (pushoutCocone f g) ≫ l = PushoutCocone.inl s ∧ Pus …
    letI : Algebra R B := g.toAlgebra
    -- ⊢ { l // PushoutCocone.inl (pushoutCocone f g) ≫ l = PushoutCocone.inl s ∧ Pus …
    letI : Algebra R (pushoutCocone f g).pt := show Algebra R (A ⊗[R] B) by infer_instance
    -- ⊢ { l // PushoutCocone.inl (pushoutCocone f g) ≫ l = PushoutCocone.inl s ∧ Pus …
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
    -- ⊢ PushoutCocone.inl (pushoutCocone f g) ≫ ↑(Algebra.TensorProduct.productMap f …
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    -- ⊢ Algebra.TensorProduct.includeLeftRingHom ≫ ↑(Algebra.TensorProduct.productMa …
    constructor
    · ext x
      -- ⊢ ↑(Algebra.TensorProduct.includeLeftRingHom ≫ ↑(Algebra.TensorProduct.product …
      -- Porting note : Lean can't see through `forget` functor
      letI : Semiring ((forget CommRingCat).obj A) := A.str.toSemiring
      -- ⊢ ↑(Algebra.TensorProduct.includeLeftRingHom ≫ ↑(Algebra.TensorProduct.product …
      letI : Algebra R ((forget CommRingCat).obj A) := show Algebra R A by infer_instance
      -- ⊢ ↑(Algebra.TensorProduct.includeLeftRingHom ≫ ↑(Algebra.TensorProduct.product …
      exact Algebra.TensorProduct.productMap_left_apply _ _ x
      -- 🎉 no goals
    constructor
    · ext x
      -- ⊢ ↑(↑Algebra.TensorProduct.includeRight ≫ ↑(Algebra.TensorProduct.productMap { …
      -- Porting note : Lean can't see through `forget` functor
      letI : Semiring ((forget CommRingCat).obj B) := B.str.toSemiring
      -- ⊢ ↑(↑Algebra.TensorProduct.includeRight ≫ ↑(Algebra.TensorProduct.productMap { …
      letI : Algebra R ((forget CommRingCat).obj B) := show Algebra R B by infer_instance
      -- ⊢ ↑(↑Algebra.TensorProduct.includeRight ≫ ↑(Algebra.TensorProduct.productMap { …
      exact Algebra.TensorProduct.productMap_right_apply _ _ x
      -- 🎉 no goals
    intro h eq1 eq2
    -- ⊢ h = ↑(Algebra.TensorProduct.productMap { toRingHom := { toMonoidHom := ↑(Pus …
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
    -- ⊢ ∀ (a : ↑A) (b : ↑B), ↑h' (a ⊗ₜ[↑R] b) = ↑(Algebra.TensorProduct.productMap f …
    intro a b
    -- ⊢ ↑h' (a ⊗ₜ[↑R] b) = ↑(Algebra.TensorProduct.productMap f' g') (a ⊗ₜ[↑R] b)
    simp only [PushoutCocone.ι_app_left, pushoutCocone_pt, coe_of, RingHom.toMonoidHom_eq_coe,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_coe, ← eq1, AlgHom.toRingHom_eq_coe,
      PushoutCocone.ι_app_right, ← eq2, Algebra.TensorProduct.productMap_apply_tmul]
    change _ = h (a ⊗ₜ 1) * h (1 ⊗ₜ b)
    -- ⊢ ↑h (a ⊗ₜ[↑R] b) = ↑h (a ⊗ₜ[↑R] 1) * ↑h (1 ⊗ₜ[↑R] b)
    rw [←h.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    -- ⊢ ↑h (a ⊗ₜ[↑R] b) = ↑h (a ⊗ₜ[↑R] b)
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_is_colimit CommRingCat.pushoutCoconeIsColimit

end Pushout

section Terminal

/-- The trivial ring is the (strict) terminal object of `CommRingCat`. -/
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) := by
  refine IsTerminal.ofUnique (h := fun X => ⟨⟨⟨⟨1, rfl⟩, fun _ _ => rfl⟩, ?_, ?_⟩, ?_⟩)
  · dsimp
    -- 🎉 no goals
  · intros; dsimp
    -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := 1, map_one' := (_ : OfNat.ofNat 1 1  …
            -- 🎉 no goals
  · intros f; ext; rfl
    -- ⊢ f = default
              -- ⊢ ↑f x✝ = ↑default x✝
                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.punit_is_terminal CommRingCat.punitIsTerminal

instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} := by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  -- ⊢ ∀ (A : CommRingCat) (f : of PUnit ⟶ A), IsIso f
  intro X f
  -- ⊢ IsIso f
  refine ⟨⟨⟨1, rfl, fun _ _ => rfl⟩, by ext; rfl, ?_⟩⟩
  -- ⊢ { toMonoidHom := 1, map_zero' := (_ : OneHom.toFun (↑1) 0 = OneHom.toFun (↑1 …
  ext x
  -- ⊢ ↑({ toMonoidHom := 1, map_zero' := (_ : OneHom.toFun (↑1) 0 = OneHom.toFun ( …
  have e : (0 : X) = 1 := by
    rw [← f.map_one, ← f.map_zero]
    congr
  replace e : 0 * x = 1 * x := congr_arg (· * x) e
  -- ⊢ ↑({ toMonoidHom := 1, map_zero' := (_ : OneHom.toFun (↑1) 0 = OneHom.toFun ( …
  rw [one_mul, zero_mul, ← f.map_zero] at e
  -- ⊢ ↑({ toMonoidHom := 1, map_zero' := (_ : OneHom.toFun (↑1) 0 = OneHom.toFun ( …
  exact e
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.CommRing_has_strict_terminal_objects CommRingCat.commRingCat_hasStrictTerminalObjects

theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)
                                -- 🎉 no goals
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
    -- ⊢ ↑((fun c => RingHom.prod (NatTrans.app c.π { as := WalkingPair.left }) (NatT …
    rcases j with ⟨⟨⟩⟩ <;>
    -- ⊢ ↑((fun c => RingHom.prod (NatTrans.app c.π { as := WalkingPair.left }) (NatT …
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right,
      FunctorToTypes.map_comp_apply, forget_map, coe_of, RingHom.prod_apply] <;>
    rfl
    -- 🎉 no goals
    -- 🎉 no goals
  uniq s m h := by
    ext x
    -- ⊢ ↑m x = ↑((fun c => RingHom.prod (NatTrans.app c.π { as := WalkingPair.left } …
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    -- ⊢ ↑m x = (↑(BinaryFan.fst s) x, ↑(BinaryFan.snd s) x)
    have eq1 := congr_hom (h ⟨WalkingPair.left⟩) x
    -- ⊢ ↑m x = (↑(BinaryFan.fst s) x, ↑(BinaryFan.snd s) x)
    have eq2 := congr_hom (h ⟨WalkingPair.right⟩) x
    -- ⊢ ↑m x = (↑(BinaryFan.fst s) x, ↑(BinaryFan.snd s) x)
    dsimp at eq1 eq2
    -- ⊢ ↑m x = (↑(BinaryFan.fst s) x, ↑(BinaryFan.snd s) x)
    rw [←eq1, ←eq2]
    -- ⊢ ↑m x = (↑(m ≫ BinaryFan.fst (prodFan A B)) x, ↑(m ≫ BinaryFan.snd (prodFan A …
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.prod_fan_is_limit CommRingCat.prodFanIsLimit

end Product

section Equalizer

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

/-- The equalizer in `CommRingCat` is the equalizer as sets. This is the equalizer fork. -/
def equalizerFork : Fork f g :=
  Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f g).subtype) <| by
      ext ⟨x, e⟩
      -- ⊢ ↑(ofHom (Subring.subtype (RingHom.eqLocus f g)) ≫ f) { val := x, property := …
      simpa using e
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.equalizer_fork CommRingCat.equalizerFork

/-- The equalizer in `CommRingCat` is the equalizer as sets. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  -- ⊢ (s : Fork f g) → { l // l ≫ Fork.ι (equalizerFork f g) = Fork.ι s ∧ ∀ {m : ( …
  intro s
  -- ⊢ { l // l ≫ Fork.ι (equalizerFork f g) = Fork.ι s ∧ ∀ {m : ((Functor.const Wa …
  -- Porting note : Lean can't see through `(parallelPair f g).obj zero`
  haveI : SubsemiringClass (Subring A) ((parallelPair f g).obj WalkingParallelPair.zero) :=
    show SubsemiringClass (Subring A) A by infer_instance
  use s.ι.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x : _)
  -- ⊢ RingHom.codRestrict (Fork.ι s) (RingHom.eqLocus f g) (_ : ∀ (x : ↑(((Functor …
  constructor
  -- ⊢ RingHom.codRestrict (Fork.ι s) (RingHom.eqLocus f g) (_ : ∀ (x : ↑(((Functor …
  · ext
    -- ⊢ ↑(RingHom.codRestrict (Fork.ι s) (RingHom.eqLocus f g) (_ : ∀ (x : ↑(((Funct …
    rfl
    -- 🎉 no goals
  · intro m hm
    -- ⊢ m = RingHom.codRestrict (Fork.ι s) (RingHom.eqLocus f g) (_ : ∀ (x : ↑(((Fun …
    exact RingHom.ext fun x => Subtype.ext <| ConcreteCategory.congr_hom hm x
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.equalizer_fork_is_limit CommRingCat.equalizerForkIsLimit

instance : IsLocalRingHom (equalizerFork f g).ι := by
  constructor
  -- ⊢ ∀ (a : ↑(((Functor.const WalkingParallelPair).obj (equalizerFork f g).pt).ob …
  rintro ⟨a, h₁ : _ = _⟩ (⟨⟨x, y, h₃, h₄⟩, rfl : x = _⟩ : IsUnit a)
  -- ⊢ IsUnit { val := x, property := h₁ }
  have : y ∈ RingHom.eqLocus f g := by
    apply (f.isUnit_map ⟨⟨x, y, h₃, h₄⟩, rfl⟩ : IsUnit (f x)).mul_left_inj.mp
    conv_rhs => rw [h₁]
    rw [← f.map_mul, ← g.map_mul, h₄, f.map_one, g.map_one]
  rw [isUnit_iff_exists_inv]
  -- ⊢ ∃ b, { val := x, property := h₁ } * b = 1
  exact ⟨⟨y, this⟩, Subtype.eq h₃⟩
  -- 🎉 no goals

instance equalizer_ι_isLocalRingHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalRingHom (limit.π F WalkingParallelPair.zero) := by
  have := limMap_π (diagramIsoParallelPair F).hom WalkingParallelPair.zero
  -- ⊢ IsLocalRingHom (limit.π F WalkingParallelPair.zero)
  rw [← IsIso.comp_inv_eq] at this
  -- ⊢ IsLocalRingHom (limit.π F WalkingParallelPair.zero)
  rw [← this]
  -- ⊢ IsLocalRingHom ((limMap (diagramIsoParallelPair F).hom ≫ limit.π (parallelPa …
  rw [← limit.isoLimitCone_hom_π
      ⟨_,
        equalizerForkIsLimit (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)⟩
      WalkingParallelPair.zero]
  change IsLocalRingHom ((lim.map _ ≫ _ ≫ (equalizerFork _ _).ι) ≫ _)
  -- ⊢ IsLocalRingHom ((lim.map (diagramIsoParallelPair F).hom ≫ (limit.isoLimitCon …
  infer_instance
  -- 🎉 no goals
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
  -- ⊢ IsLocalRingHom ((limit.isoLimitCone { cone := Cone.whisker walkingParallelPa …
  infer_instance
  -- 🎉 no goals
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
      -- ⊢ ↑(ofHom (RingHom.comp (RingHom.fst ↑A ↑B) (Subring.subtype (RingHom.eqLocus  …
      simpa [CommRingCat.ofHom] using e)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.pullback_cone CommRingCat.pullbackCone

/-- The constructed pullback cone is indeed the limit. -/
def pullbackConeIsLimit {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) := by
  fapply PullbackCone.IsLimit.mk
  · intro s
    -- ⊢ s.pt ⟶ of { x // x ∈ RingHom.eqLocus (RingHom.comp f (RingHom.fst ↑A ↑B)) (R …
    apply (s.fst.prod s.snd).codRestrict
    -- ⊢ ∀ (x : ↑s.pt), ↑(RingHom.prod (PullbackCone.fst s) (PullbackCone.snd s)) x ∈ …
    intro x
    -- ⊢ ↑(RingHom.prod (PullbackCone.fst s) (PullbackCone.snd s)) x ∈ RingHom.eqLocu …
    exact congr_arg (fun f : s.pt →+* C => f x) s.condition
    -- 🎉 no goals
  · intro s
    -- ⊢ RingHom.codRestrict (RingHom.prod (PullbackCone.fst s) (PullbackCone.snd s)) …
    ext x
    -- ⊢ ↑(RingHom.codRestrict (RingHom.prod (PullbackCone.fst s) (PullbackCone.snd s …
    rfl
    -- 🎉 no goals
  · intro s
    -- ⊢ RingHom.codRestrict (RingHom.prod (PullbackCone.fst s) (PullbackCone.snd s)) …
    ext x
    -- ⊢ ↑(RingHom.codRestrict (RingHom.prod (PullbackCone.fst s) (PullbackCone.snd s …
    rfl
    -- 🎉 no goals
  · intro s m e₁ e₂
    -- ⊢ m = RingHom.codRestrict (RingHom.prod (PullbackCone.fst s) (PullbackCone.snd …
    refine RingHom.ext fun (x : s.pt) => Subtype.ext ?_
    -- ⊢ ↑(↑m x) = ↑(↑(RingHom.codRestrict (RingHom.prod (PullbackCone.fst s) (Pullba …
    change (m x).1 = (_, _)
    -- ⊢ ↑(↑m x) = (↑(PullbackCone.fst s) x, ↑(PullbackCone.snd s) x)
    have eq1 := (congr_arg (fun f : s.pt →+* A => f x) e₁ : _)
    -- ⊢ ↑(↑m x) = (↑(PullbackCone.fst s) x, ↑(PullbackCone.snd s) x)
    have eq2 := (congr_arg (fun f : s.pt →+* B => f x) e₂ : _)
    -- ⊢ ↑(↑m x) = (↑(PullbackCone.fst s) x, ↑(PullbackCone.snd s) x)
    rw [←eq1, ←eq2]
    -- ⊢ ↑(↑m x) = (↑(m ≫ ofHom (RingHom.comp (RingHom.fst ↑A ↑B) (Subring.subtype (R …
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommRing.pullback_cone_is_limit CommRingCat.pullbackConeIsLimit

end Pullback

end CommRingCat
