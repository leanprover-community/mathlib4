/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!

# Existence of Flat extension

-/

@[expose] public section

universe w u v

open IsLocalRing CategoryTheory SmallObject

open scoped Polynomial

variable (R : Type u) [CommRing R] [IsLocalRing R] (K : Type v) [Field K]
  [Algebra (ResidueField R) K]

section instances

instance {S : Type*} [Semiring S] [Algebra R S] : IsLocalHom (AlgHom.id R S) := ⟨fun _ h ↦ h⟩

instance {S₁ S₂ S₃ : Type*} [Semiring S₁] [Semiring S₂] [Semiring S₃] [Algebra R S₁] [Algebra R S₂]
    [Algebra R S₃] (f : S₁ →ₐ[R] S₂) (g : S₂ →ₐ[R] S₃) [locf : IsLocalHom f] [locg : IsLocalHom g] :
    IsLocalHom (g.comp f) :=
  ⟨fun a ha ↦ locf.map_nonunit a (locg.map_nonunit (f a) ha)⟩

omit [IsLocalRing R] in
private lemma AlgHom.comp_toRingHom' {S₁ S₂ S₃ : Type*} [Semiring S₁] [Semiring S₂] [Semiring S₃]
    [Algebra R S₁] [Algebra R S₂] [Algebra R S₃] (f : S₁ →ₐ[R] S₂) (g : S₂ →ₐ[R] S₃) :
    (g.comp f) = (RingHomClass.toRingHom g).comp (RingHomClass.toRingHom f) := rfl

instance [Small.{w} R] : IsLocalRing (Shrink R) :=
  let := IsLocalHom.of_surjective (Shrink.ringEquiv R).symm.toRingHom
    (Shrink.ringEquiv R).symm.surjective
  IsLocalRing.of_surjective (Shrink.ringEquiv R).symm.toRingHom (Shrink.ringEquiv R).symm.surjective

end instances

section monogenic

variable (S : Type w) [CommRing S] [IsLocalRing S] [Algebra (ResidueField S) K]

noncomputable abbrev minpolyLift (x : K) (int : IsIntegral (ResidueField S) x) : S[X] :=
  Classical.choose (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (IsLocalRing.residue S) IsLocalRing.residue_surjective
    (minpoly (ResidueField S) x)) (minpoly.monic int))

lemma minpolyLift_spec (x : K) (int : IsIntegral (ResidueField S) x) :
    Polynomial.map (IsLocalRing.residue S) (minpolyLift K S x int) = minpoly (ResidueField S) x ∧
    (minpolyLift K S x int).natDegree = (minpoly (ResidueField S) x).natDegree
    ∧ (minpolyLift K S x int).Monic :=
    Classical.choose_spec (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (IsLocalRing.residue S) IsLocalRing.residue_surjective
    (minpoly (ResidueField S) x)) (minpoly.monic int))

abbrev extensionByAlgebraic (x : K) (int : IsIntegral (ResidueField S) x) : Type w :=
  S[X] ⧸ Ideal.span {minpolyLift K S x int}

instance (x : K) (int : IsIntegral (ResidueField S) x) :
    Module.Finite S (extensionByAlgebraic K S x int) :=
  (minpolyLift_spec K S x int).2.2.finite_quotient

instance (x : K) (int : IsIntegral (ResidueField S) x) :
    Module.Free S (extensionByAlgebraic K S x int) :=
  (minpolyLift_spec K S x int).2.2.free_quotient

set_option backward.isDefEq.respectTransparency false in
lemma extensionByAlgebraic_maximalIdeal_map (x : K) (int : IsIntegral (ResidueField S) x) :
    ((maximalIdeal S).map (algebraMap S (extensionByAlgebraic K S x int))).IsMaximal := by
  let f' := (Ideal.Quotient.mk (Ideal.span {(minpoly (ResidueField S) x)})).comp
    (Polynomial.mapRingHom (IsLocalRing.residue S))
  have eqmap : Ideal.span {(minpoly (ResidueField S) x)} =
    (Ideal.span {minpolyLift K S x int}).map (Polynomial.mapRingHom (IsLocalRing.residue S)) := by
    simp [Ideal.map_span, (minpolyLift_spec K S x int).1]
  have kereq : RingHom.ker f' = Ideal.span {minpolyLift K S x int} ⊔
    (maximalIdeal S).map Polynomial.C := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, eqmap, Ideal.comap_map_of_surjective' _
      (Polynomial.map_surjective _ residue_surjective), Polynomial.ker_mapRingHom, ker_residue]
  let f : (extensionByAlgebraic K S x int) →+* _ :=
    Ideal.Quotient.lift _ f' (fun x hx ↦ (le_of_le_of_eq le_sup_left kereq.symm) hx)
  have surjf : Function.Surjective f := by
    apply Ideal.Quotient.lift_surjective_of_surjective
    exact (Ideal.Quotient.mk_surjective.comp
      (Polynomial.map_surjective _ IsLocalRing.residue_surjective))
  let : Fact _ := ⟨minpoly.irreducible int⟩
  let := Ideal.Quotient.field (Ideal.span {(minpoly (ResidueField S) x)})
  convert RingHom.ker_isMaximal_of_surjective f surjf
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [RingHom.comap_ker, Ideal.Quotient.lift_comp_mk, kereq, IsScalarTower.algebraMap_eq S S[X]]
  simp [← Ideal.map_map]

instance (x : K) (int : IsIntegral (ResidueField S) x) :
    IsLocalRing (extensionByAlgebraic K S x int) := by
  have := extensionByAlgebraic_maximalIdeal_map K S x int
  apply IsLocalRing.of_unique_max_ideal
  use (maximalIdeal S).map (algebraMap S (extensionByAlgebraic K S x int)), this
  intro m hm
  exact (this.eq_of_le hm.ne_top (Ideal.map_le_iff_le_comap.mpr (le_of_eq (eq_maximalIdeal
    m.isMaximal_comap_of_isIntegral_of_isMaximal).symm))).symm

lemma extensionByAlgebraic_maximalIdeal_eq_map (x : K) (int : IsIntegral (ResidueField S) x) :
    maximalIdeal (extensionByAlgebraic K S x int) =
    (maximalIdeal S).map (algebraMap S (extensionByAlgebraic K S x int)) :=
  (eq_maximalIdeal (extensionByAlgebraic_maximalIdeal_map K S x int)).symm

lemma extensionByAlgebraic_algebraMap_isLocalHom (x : K) (int : IsIntegral (ResidueField S) x) :
    IsLocalHom (algebraMap S (extensionByAlgebraic K S x int)) := sorry

def extensionByAlgebraicAlgebraK (x : K) (int : IsIntegral (ResidueField S) x) :
    Algebra (ResidueField (extensionByAlgebraic K S x int)) K := sorry

def extensionByAlgebraicIsScalarTower (x : K) (int : IsIntegral (ResidueField S) x) :
    letI := extensionByAlgebraic_algebraMap_isLocalHom K S x int
    letI := extensionByAlgebraicAlgebraK K S x int
    IsScalarTower (ResidueField S) (ResidueField (extensionByAlgebraic K S x int)) K := sorry

abbrev extensionByTranscendental : Type w :=
  Localization.AtPrime ((maximalIdeal S).map Polynomial.C)

instance : IsLocalHom (algebraMap S (extensionByTranscendental S)) := sorry

def extensionByTranscendentalAlgebraK (x : K) (nint : ¬ IsIntegral (ResidueField S) x) :
    Algebra (ResidueField (extensionByTranscendental S)) K := sorry

def extensionByTranscendentalIsScalarTower (x : K) (nint : ¬ IsIntegral (ResidueField S) x) :
    letI := extensionByTranscendentalAlgebraK K S x nint
    IsScalarTower (ResidueField S) (ResidueField (extensionByTranscendental S)) K := sorry

end monogenic

structure FlatExtension where
  Ring : Type w
  [commRing : CommRing Ring]
  [isLocalRing : IsLocalRing Ring]
  [algebra : Algebra R Ring]
  [isLocalHom : IsLocalHom (algebraMap R Ring)]
  [algebraK : Algebra (ResidueField Ring) K]
  [isScalarTower : IsScalarTower (ResidueField R) (ResidueField Ring) K]
  flat : Module.Flat R Ring
  eqmap : maximalIdeal Ring = (maximalIdeal R).map (algebraMap R Ring)

namespace FlatExtension

attribute [instance] commRing algebra isLocalRing isLocalHom algebraK isScalarTower

noncomputable def trivial [Small.{w} R] : FlatExtension R K := by
  let e : R ≃+* Shrink.{w} R := (Shrink.ringEquiv R).symm
  let : IsLocalHom (algebraMap R (Shrink.{w} R)) :=
    IsLocalHom.of_surjective e.toRingHom e.surjective
  let : Algebra (ResidueField (Shrink.{w, u} R)) K := sorry
  let : IsScalarTower (ResidueField R) (ResidueField (Shrink.{w, u} R)) K := sorry
  refine ⟨Shrink.{w} R, Module.Flat.of_linearEquiv (Shrink.linearEquiv R R), ?_⟩
  apply (IsLocalRing.eq_maximalIdeal _).symm
  exact (Ideal.isMaximal_map_iff_of_bijective _ e.bijective).2 inferInstance

variable {R K} in
structure Hom (S₁ S₂ : FlatExtension.{w} R K) where
  hom : S₁.Ring →ₐ[R] S₂.Ring
  [isLocalHom : IsLocalHom hom]
  comm : (algebraMap (ResidueField S₂.Ring) K).comp (ResidueField.map hom) =
    (algebraMap (ResidueField S₁.Ring) K)

attribute [instance] Hom.isLocalHom

instance : Category.{w} (FlatExtension.{w} R K) where
  Hom S₁ S₂ := FlatExtension.Hom S₁ S₂
  id S := ⟨AlgHom.id R S.Ring, by simp⟩
  comp f g := ⟨g.hom.comp f.hom, by
    simp [← f.comm, ← g.comm, AlgHom.comp_toRingHom', ResidueField.map_comp, ← RingHom.comp_assoc]⟩

noncomputable def SuccStruct [Small.{w} R] : SuccStruct (FlatExtension.{w} R K) where
  X₀ := trivial R K
  succ S := sorry
  toSucc S := sorry

lemma algebraMap_range_lt_of_not_surjective [Small.{w} R] (S : FlatExtension R K)
    (nsurj : ¬ Function.Surjective (algebraMap (ResidueField S.Ring) K)) :
    (algebraMap (ResidueField S.Ring) K).range <
    (algebraMap (ResidueField ((FlatExtension.SuccStruct R K).succ S).Ring) K).range := by
  sorry

variable (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [Small.{w} R]

private instance : Limits.HasIterationOfShape J (FlatExtension R K) := sorry

end FlatExtension

set_option backward.isDefEq.respectTransparency false in
lemma exists_isLocalHom_flat : ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[ResidueField R] (ResidueField R')) := by
  obtain ⟨setK, ⟨e⟩⟩ : ∃ S : Type max u v, Nonempty (S ≃ Set K) := ⟨ULift (Set K), ⟨Equiv.ulift⟩⟩
  let ⟨lin, wf⟩ := exists_wellOrder setK
  let : WellFoundedLT (WithTop setK) := WithTop.instWellFoundedLT
  let : SuccOrder (WithTop setK) := SuccOrder.ofLinearWellFoundedLT _
  let : OrderBot (WithTop setK) := WellFoundedLT.toOrderBot
  obtain ⟨φ⟩ : Nonempty ((FlatExtension.SuccStruct.{max u v} R K).Iteration (⊤ : WithTop setK)) :=
    inferInstance
  let fi : WithTop setK ≃o Set.Iic (⊤ : WithTop setK) := OrderIso.IicTop.symm
  let φobj := fun i ↦ (algebraMap (ResidueField ((φ.F.obj (fi i)).Ring)) K).range
  let φtop := φ.F.obj (fi ⊤)
  suffices h : (algebraMap (ResidueField φtop.Ring) K).range = ⊤ by
    let f := algebraMap (ResidueField φtop.Ring) K
    have : Function.Bijective f := ⟨RingHom.injective f, RingHom.range_eq_top.mp h⟩
    let f := RingEquiv.ofBijective f this
    refine ⟨φtop.Ring, φtop.commRing, φtop.isLocalRing, φtop.algebra, φtop.isLocalHom, φtop.flat,
      φtop.eqmap, ⟨AlgEquiv.ofRingEquiv (f := f.symm) fun x ↦ f.injective ?_⟩⟩
    · simp only [RingEquiv.apply_symm_apply]
      exact IsScalarTower.algebraMap_apply (ResidueField R) (ResidueField φtop.Ring) K x
  have mono : Monotone φobj := fun a b hab ↦ by
    let mapab := φ.F.map (homOfLE (fi.monotone hab))
    rintro _ ⟨x, rfl⟩
    exact ⟨ResidueField.map mapab.hom x, congr($mapab.comm x)⟩
  by_contra hne
  have hlt : ∀ i, i < ⊤ → ∃ u, u ∈ φobj (Order.succ i) ∧ ¬ u ∈ φobj i := by
    rintro i h
    have := FlatExtension.algebraMap_range_lt_of_not_surjective R K (φ.F.obj (fi i)) <|
      fun h' ↦ hne <| eq_top_iff.mpr <| le_trans (le_of_eq (RingHom.range_eq_top.mpr h').symm)
        <| mono le_top
    obtain ⟨x, hx⟩ := Set.exists_of_ssubset this
    have : φ.F.obj (fi (Order.succ i)) = (FlatExtension.SuccStruct R K).succ (φ.F.obj (fi i)) := by
      rw [← φ.obj_succ]
      · rfl
      · exact h
    unfold φobj
    exact ⟨x, this ▸ hx⟩
  let uh := fun i : setK ↦ hlt (fi i) (WithTop.coe_lt_top _)
  let u : setK → K := fun i ↦ Classical.choose (uh i)
  have hu : Function.Injective u := by
    refine Function.Injective.of_lt_imp_ne fun x y hxy heq ↦ ?_
    absurd (Classical.choose_spec (uh x)).1
    change u x ∉ _
    rw [heq]
    refine fun h ↦ (Classical.choose_spec (uh y)).2 ((mono ?_) h)
    exact Order.succ_le_of_lt <| Subtype.mk_lt_mk.mpr (WithTop.coe_lt_coe.mpr hxy)
  absurd (Cardinal.lift_mk_le_lift_mk_of_injective (hu.comp e.symm.injective))
  simpa using Cardinal.cantor (Cardinal.mk K)
