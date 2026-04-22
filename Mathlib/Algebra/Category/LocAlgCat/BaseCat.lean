/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocAlgCat.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.AdicCompletion.Noetherian

import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Category.LocAlgCat.Cotangent

/-!
# The Base Category for Deformation Theory

This file introduces `BaseCat`, the base category used in formal deformation theory
(e.g., for Schlessinger's criteria and Artin's axioms). It is defined as the full subcategory
of `LocAlgCat Λ k` consisting of Artinian local algebras.

## Main Results

* `BaseCat`: The category of Artinian local `Λ`-algebras with a fixed residue field `k`.

* `BaseCat.IsSmallExtension`: The typeclass representing a small extension.
  A morphism `f : A ⟶ B` is a small extension if it is surjective and its kernel is a principal
  ideal annihilated by the maximal ideal of `A`.

* `BaseCat.induction_on_isSmallExtension`: Any surjective morphism in `BaseCat` can
  be factored into a finite composition of small extensions.

-/

@[expose] public section

universe w v u

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]

/-- The base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] : Type _ :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦ IsArtinianRing A

namespace BaseCat

/-- A synonym for `A.obj.carrier`, which we can mark with `@[coe]`. -/
@[reducible]
def carrier (A : BaseCat.{w} Λ k) : Type w := A.obj.carrier

instance : CoeSort (BaseCat.{w} Λ k) (Type w) := ⟨BaseCat.carrier⟩

attribute [coe] carrier

variable {A B C : BaseCat.{w} Λ k} {f : A ⟶ B}

instance (A : BaseCat Λ k) : IsArtinianRing A := A.property

variable (Λ k) in
/-- The object in the base category associated to a type equipped with appropriate typeclasses.
This is a preferred way to construct a term of `BaseCat`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [Algebra X k]
    [IsScalarTower Λ X k] [IsArtinianRing X] (hX : Surjective (algebraMap X k)) :
    BaseCat Λ k := ⟨.of Λ k X hX, inferInstance⟩

/-- The quotient of an object `A` in `BaseCat` by a proper ideal `I`. -/
def ofQuot (A : BaseCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : BaseCat Λ k :=
  ⟨A.obj.ofQuot I, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- Upgrades the canonical quotient map from `A` to `A ⧸ I` to a morphism in `BaseCat`. -/
abbrev toOfQuot (A : BaseCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] :
    A ⟶ A.ofQuot I := ObjectProperty.homMk (A.obj.toOfQuot I)

/-- The morphism between quotient objects in `BaseCat` induced by a morphism `f : A ⟶ B`.
This is the categorical counterpart to `Ideal.quotientMapₐ` in the Artinian setting. -/
abbrev mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B} [Nontrivial (A ⧸ I)]
    [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  ObjectProperty.homMk <| LocAlgCat.mapOfQuot f.hom hf

lemma toOfQuot_comp_mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B}
    [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) :
    A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

/-- The quotient of a local Artinian algebra by the `n`-th power of its maximal ideal,
viewed as an object in `BaseCat`. -/
abbrev infinitesimalNeighborhood (n : ℕ) [NeZero n] (A : BaseCat.{w} Λ k) : BaseCat Λ k :=
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood in `BaseCat`. -/
abbrev toInfinitesimalNeighborhood (n : ℕ) [NeZero n] (A : BaseCat.{w} Λ k) :
    A ⟶ A.infinitesimalNeighborhood n := toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `BaseCat`. -/
abbrev mapInfinitesimalNeighborhood (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimalNeighborhood m ⟶ B.infinitesimalNeighborhood n :=
  ObjectProperty.homMk (LocAlgCat.mapInfinitesimalNeighborhood m n hmn f.hom)

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `BaseCat`. -/
abbrev specialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : BaseCat.{w} Λ k) :
    BaseCat.{w} Λ k :=
  ⟨A.obj.specialFiber, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- The canonical morphism from `A` to its special fiber in `BaseCat`. -/
abbrev toSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : BaseCat.{w} Λ k) :
    A ⟶ A.specialFiber :=
  ObjectProperty.homMk A.obj.toSpecialFiber

/-- The morphism between special fibers induced by a morphism in `BaseCat`. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (f : A ⟶ B) :
    A.specialFiber ⟶ B.specialFiber :=
  ObjectProperty.homMk (LocAlgCat.mapSpecialFiber f.hom)

/-- A morphism `f : A ⟶ B` in `BaseCat` is a small extension if it is a surjective map
whose kernel is a principal ideal annihilated by the maximal ideal of `A`. -/
@[stacks 06GD]
class IsSmallExtension (f : A ⟶ B) : Prop where
  private mk ::
  surjective (f) : Function.Surjective f.hom.toAlgHom
  isPrincipal_ker (f) : (RingHom.ker f.hom.toAlgHom).IsPrincipal
  le_annihilator_ker (f) : maximalIdeal A ≤ (RingHom.ker f.hom.toAlgHom).annihilator

theorem isSmallExtenstion_iff : IsSmallExtension f ↔ Function.Surjective f.hom.toAlgHom ∧
    ∃ x : A, Ideal.span {x} = RingHom.ker f.hom.toAlgHom ∧
      ∀ y ∈ maximalIdeal A, x * y = 0 := by
  refine ⟨fun ⟨_, ⟨x, hx⟩, h⟩ ↦ ⟨IsSmallExtension.surjective f, x, ?_, fun y y_in ↦ ?_⟩,
    fun ⟨h, x, x_span, hx⟩ ↦ ⟨h, ⟨x, ?_⟩, ?_⟩⟩
  · simp [hx]
  · rw [mul_comm, ← smul_eq_mul, ← Submodule.mem_annihilator_span_singleton, ← hx]
    exact h y_in
  · simp [← x_span]
  · intro y y_in
    rw [← x_span, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
    exact hx y y_in

theorem isSmallExtension_of_bijective (h : Bijective f.hom.toAlgHom) : IsSmallExtension f :=
  (isSmallExtenstion_iff).mpr ⟨h.surjective, 0, by
    have := h.injective
    rw [RingHom.injective_iff_ker_eq_bot] at this
    simp [this]⟩

instance IsSmallExtension.hom_iso (e : A ≅ B) : IsSmallExtension e.hom := by
  apply isSmallExtension_of_bijective
  rw [bijective_iff_has_inverse]
  use e.inv.hom.toAlgHom
  simp [leftInverse_iff_comp, rightInverse_iff_comp, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]

theorem IsSmallExtension.toOfQuot_span_singleton (A : BaseCat.{w} Λ k) (x : A)
    [Nontrivial (A ⧸ (Ideal.span {x}))] (h : ∀ y ∈ maximalIdeal A, x * y = 0) :
    IsSmallExtension (A.toOfQuot (Ideal.span {x})) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, h⟩
  change _ = RingHom.ker (A.obj.toOfQuot (Ideal.span {x})).toAlgHom
  rw [LocAlgCat.ker_toAlgHom_toOfQuot]

open Submodule in
@[elab_as_elim, stacks 06GE]
theorem induction_on_isSmallExtension (hf : Surjective f.hom.toAlgHom)
    {P : ∀ {A B : BaseCat.{w} Λ k} (f : A ⟶ B), Surjective f.hom.toAlgHom → Prop}
    (small_ext : ∀ {X Y : BaseCat.{w} Λ k} (f : X ⟶ Y) [IsSmallExtension f],
      P f (IsSmallExtension.surjective f))
    (comp : ∀ {A B C : BaseCat.{w} Λ k} (f : A ⟶ B) (g : B ⟶ C) [IsSmallExtension f]
      (hg : Surjective g.hom.toAlgHom), P g hg →
    P (f ≫ g) (hg.comp (IsSmallExtension.surjective f))) : P f hf := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Module.length A A :=
    ENat.ne_top_iff_exists.mp Module.length_ne_top
  symm at hn; revert A
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A f hf hlen
    have hn : n ≠ 0 := by
      intro hn; revert hlen
      have : Nontrivial A := inferInstance
      simpa [hn, Module.length_eq_zero_iff, ← not_nontrivial_iff_subsingleton]
    let I := RingHom.ker f.hom.toAlgHom
    by_cases hI : I = ⊥
    · rw [← RingHom.injective_iff_ker_eq_bot] at hI
      have : IsSmallExtension f := isSmallExtension_of_bijective ⟨hI, hf⟩
      exact small_ext f
    obtain ⟨x, hx, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Ideal.annihilator_inf_ne_bot
      ((isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance) hI)
    have x_in : x ∈ I := (mem_inf.mp hx).right
    replace hx : ∀ y ∈ maximalIdeal A, x * y = 0 := mem_annihilator.mp (mem_inf.mp hx).left
    have span_ne_top : Ideal.span {x} ≠ ⊤ := by
      refine Ideal.span_singleton_ne_top (le_maximalIdeal ?_ x_in)
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, le_maximalIdeal
        (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have : Nontrivial (A ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr span_ne_top
    have : IsLocalRing (A ⧸ Ideal.span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have aux : ∀ a ∈ Ideal.span {x}, (LocAlgCat.Hom.toAlgHom f.hom) a = 0 := by
      intro _ h; rw [Ideal.mem_span_singleton'] at h
      rcases h with ⟨_, rfl⟩; rw [← RingHom.mem_ker]
      exact Ideal.mul_mem_left _ _ x_in
    let C := A.ofQuot (Ideal.span {x})
    let g : A ⟶ C := A.toOfQuot (Ideal.span {x})
    have hg : IsSmallExtension g := IsSmallExtension.toOfQuot_span_singleton A x hx
    let u : C →ₐ[Λ] B := Ideal.Quotient.liftₐ (Ideal.span {x}) f.hom.toAlgHom aux
    have u_surj : Surjective u :=
      Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) aux hf
    let f' : C ⟶ B := ObjectProperty.homMk (LocAlgCat.ofHom u (eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ ‹_›)) (AlgHom.ext fun t ↦ by
        induction t using Quotient.induction_on with
        | H t =>
          simp [← AlgHom.comp_apply, f.hom.residue_comp, u]
          simpa [LocAlgCat.residue, ← Ideal.Quotient.algebraMap_eq] using
            IsScalarTower.algebraMap_apply ..))
    obtain ⟨m, hm⟩ : ∃ n : ℕ, n = Module.length C C :=
      ENat.ne_top_iff_exists.mp Module.length_ne_top
    symm at hm; suffices h : m < n by
      change P (g ≫ f') _; apply comp
      · apply ih m h; exact hm
      · exact u_surj
    change Module.length (A ⧸ Ideal.span {x}) (A ⧸ Ideal.span {x}) = m at hm
    have := Submodule.length_le_length_restrictScalars (R := (A ⧸ Ideal.span {x}))
      (M := (A ⧸ Ideal.span {x})) A ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, ← hlen, ← hm]
    exact lt_of_le_of_lt this (length_quotient_lt (Ideal.span {x}) (by simpa))

/-- A morphism `f : A ⟶ B` in the base category is called essentially surjective if its
underlying algebra homomorphism is surjective, and it satisfies the following minimality
condition: for any object `C` and morphism `g : C ⟶ A` in `BaseCat`, if the composition
`g ≫ f` is surjective, then `g` itself must be surjective. -/
@[stacks 06GF, mk_iff]
class IsEssSurj (f : A ⟶ B) : Prop where
  surjective (f) : Surjective f.hom.toAlgHom
  surjective_of_comp_left (f) {C : BaseCat.{w} Λ k} (g : C ⟶ A) :
    Surjective (g ≫ f).hom.toAlgHom → Surjective g.hom.toAlgHom

instance IsEssSurj.hom_iso (e : A ≅ B) : IsEssSurj e.hom := by
  constructor
  · rw [surjective_iff_hasRightInverse]
    use e.inv.hom.toAlgHom
    simp [rightInverse_iff_comp, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]
  · intro C g hg
    rw [ObjectProperty.FullSubcategory.comp_hom, LocAlgCat.toAlgHom_comp, AlgHom.coe_comp] at hg
    apply Surjective.of_comp_left hg
    rw [injective_iff_hasLeftInverse]
    use e.inv.hom.toAlgHom
    simp [leftInverse_iff_comp, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]

instance IsEssSurj.comp (f : A ⟶ B) (g : B ⟶ C) [IsEssSurj f] [IsEssSurj g] :
    IsEssSurj (f ≫ g) :=
  ⟨by simpa using .comp (IsEssSurj.surjective g) (IsEssSurj.surjective f), fun _ h ↦
    IsEssSurj.surjective_of_comp_left f _ (IsEssSurj.surjective_of_comp_left g _ h)⟩

theorem isEssSurj_toOfQuot_of_le {I : Ideal A} [Nontrivial (A ⧸ I)]
    (h : I ≤ maximalIdeal A ^ 2) : IsEssSurj (A.toOfQuot I) := by
  rw [← LocAlgCat.bijective_mapCotangent_toOfQuot_iff] at h
  refine ⟨Ideal.Quotient.mk_surjective, fun {C} g hg ↦ ?_⟩
  apply LocAlgCat.surjective_of_surjective_mapCotangent
  apply Surjective.of_comp_left (f := LocAlgCat.mapCotangent (A.obj.toOfQuot I))
  · rw [← LinearMap.coe_comp, ← LocAlgCat.mapCotangent_comp]
    exact LocAlgCat.surjective_mapCotangent_of_surjective hg
  · exact h.injective

section IsLocalRing

variable [IsLocalRing Λ] [Module.Finite Λ k]

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `BaseCat` where `g.hom.toAlgHom` is surjective,
`ofPullback` is the object in `BaseCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
@[stacks 06GH "(1)"]
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) : BaseCat.{w} Λ k :=
  ⟨.ofPullback f.hom g.hom hg, LocAlgCat.isArtinianRing_ofPullback ..⟩

/-- Upgrades the first projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ A := ObjectProperty.homMk (LocAlgCat.pullbackFst f.hom g.hom hg)

/-- Upgrades the second projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ B := ObjectProperty.homMk (LocAlgCat.pullbackSnd f.hom g.hom hg)

lemma pullback_comm_sq (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g := by
  ext
  simpa using LocAlgCat.pullback_comm_sq f.hom g.hom hg

@[stacks 06GH "(2)"]
instance pullbackFst_isSmallExtension (f : A ⟶ C) (g : B ⟶ C) [IsSmallExtension g] :
    IsSmallExtension (pullbackFst f g (IsSmallExtension.surjective g)) := by
  obtain ⟨x, x_span, hx⟩ := ((isSmallExtenstion_iff (f := g)).mp ‹_›).right
  rw [isSmallExtenstion_iff]; constructor
  · exact f.hom.toAlgHom.surjective_pullbackFst_of_surjective g.hom.toAlgHom
      (IsSmallExtension.surjective g)
  · have : (0, x) ∈ f.hom.toAlgHom.pullback g.hom.toAlgHom := by
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        map_zero, AlgHom.snd_apply]
      rw [eq_comm, ← RingHom.mem_ker, ← x_span]
      exact Ideal.mem_span_singleton_self x
    refine ⟨⟨(0, x), this⟩, ?_, fun ⟨⟨a, b⟩, hab⟩ h ↦ ?_⟩
    · change (Ideal.span {⟨(0, x), this⟩} : Ideal (f.hom.toAlgHom.pullback g.hom.toAlgHom)) =
        RingHom.ker (AlgHom.pullbackFst ..)
      ext ⟨⟨u, v⟩, h⟩
      simp only [Ideal.mem_span_singleton', eq_comm, Subtype.exists,
        MulMemClass.mk_mul_mk, Subtype.mk.injEq, AlgHom.mem_equalizer, AlgHom.coe_comp,
        Function.comp_apply, AlgHom.fst_apply, AlgHom.snd_apply, exists_prop, Prod.exists,
        Prod.mk_mul_mk, mul_zero, Prod.mk.injEq, and_left_comm, exists_and_left, RingHom.mem_ker,
        Subalgebra.coe_val, and_iff_left_iff_imp]
      intro u_eq
      simp only [u_eq, AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply,
        AlgHom.fst_apply, map_zero, AlgHom.snd_apply] at h
      rw [eq_comm, ← RingHom.mem_ker, ← x_span, Ideal.mem_span_singleton'] at h
      rcases h with ⟨w, hw⟩
      rcases LocAlgCat.exists_mem_maximalIdeal_toAlgHom_apply_add_eq g.hom f.hom
        w (IsSmallExtension.surjective g) with ⟨z, m, m_in, hm⟩
      exact ⟨z, w + m, hm.symm, by rw [add_mul, hw, mul_comm, hx m m_in, add_zero]⟩
    · rw [mem_maximalIdeal, mem_nonunits_iff] at h
      change ¬ IsUnit (⟨(a, b), hab⟩ : f.hom.toAlgHom.pullback g.hom.toAlgHom) at h
      rw [AlgHom.isUnit_pullback_mk_iff, not_and] at h
      change (⟨(0, x), this⟩ * ⟨(a, b), hab⟩ : f.hom.toAlgHom.pullback g.hom.toAlgHom) = 0
      suffices ¬ IsUnit b by simpa [← Subtype.val_inj] using hx b this
      intro hb
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        AlgHom.snd_apply] at hab
      have : IsUnit ((LocAlgCat.Hom.toAlgHom f.hom) a) := hab ▸ IsUnit.map g.hom.toAlgHom hb
      apply f.hom.isLocalHom_toAlgHom.map_nonunit at this
      exact (iff_false_intro (h this)).mp hb

/-- When `Λ` is a local ring and `k / ResidueField Λ` is
a finite separable field extension, `ofPullbackOfIsSeparable` is the object in `BaseCat`
obtained from the pullback of the underlying algebra homomorphisms of two morphisms. -/
def ofPullbackOfIsSeparable [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    BaseCat Λ k :=
  haveI : IsLocalRing ↥(f.hom.toAlgHom.pullback g.hom.toAlgHom) :=
    isLocalRing_algHomPullback _ _ g.hom.isLocalHom_toAlgHom
  ⟨.of Λ k (f.hom.toAlgHom.pullback g.hom.toAlgHom)
    (LocAlgCat.surjective_residue_comp_pullbackFst_of_isSeparable f.hom g.hom), inferInstance⟩

@[stacks 06S5]
theorem isEssSurj_iff_isEssSurj_mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B}
    [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hI : I ≤ maximalIdeal A ^ 2)
    (hJ : J ≤ maximalIdeal B ^ 2) (hf : I ≤ J.comap f.hom.toAlgHom) :
    IsEssSurj f ↔ IsEssSurj (mapOfQuot f hf) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · apply Surjective.of_comp (g := (A.toOfQuot I).hom.toAlgHom)
    simp only [ObjectProperty.homMk_hom, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]
    simp only [ofQuot, LocAlgCat.toOfQuot_comp_mapOfQuot, LocAlgCat.toAlgHom_comp]
    exact fun r ↦ Surjective.comp (B.obj.surjective_toAlgHom_toOfQuot (I := J)) h.surjective r
  · intro C g hg
    let C' := ofPullback g (A.toOfQuot I) Ideal.Quotient.mk_surjective
    let p : C' ⟶ C := pullbackFst g (A.toOfQuot I) Ideal.Quotient.mk_surjective
    have p_surj : Surjective p.hom.toAlgHom :=
      AlgHom.surjective_pullbackFst_of_surjective _ _ Ideal.Quotient.mk_surjective
    apply Surjective.of_comp (g := p.hom.toAlgHom)
    rw [← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      pullback_comm_sq, ObjectProperty.FullSubcategory.comp_hom,
      LocAlgCat.toAlgHom_comp, AlgHom.coe_comp]
    refine Surjective.comp Ideal.Quotient.mk_surjective ?_
    apply isEssSurj_toOfQuot_of_le at hJ
    apply IsEssSurj.surjective_of_comp_left (f ≫ B.toOfQuot J)
    rw [← toOfQuot_comp_mapOfQuot (I := I) f hf, Category.assoc',
      ← pullback_comm_sq, Category.assoc,
      ObjectProperty.FullSubcategory.comp_hom, LocAlgCat.toAlgHom_comp, AlgHom.coe_comp]
    exact hg.comp p_surj
  · apply LocAlgCat.surjective_of_surjective_mapCotangent
    apply Surjective.of_comp_left (f := LocAlgCat.mapCotangent (B.toOfQuot J).hom)
    · rw [← LinearMap.coe_comp, ← LocAlgCat.mapCotangent_comp,
        ← ObjectProperty.FullSubcategory.comp_hom, ← toOfQuot_comp_mapOfQuot (I := I) f hf,
        ObjectProperty.FullSubcategory.comp_hom, LocAlgCat.mapCotangent_comp, LinearMap.coe_comp]
      refine Surjective.comp (LocAlgCat.surjective_mapCotangent_of_surjective h.surjective) ?_
      exact LocAlgCat.surjective_mapCotangent_of_surjective Ideal.Quotient.mk_surjective
    · exact ((LocAlgCat.bijective_mapCotangent_toOfQuot_iff J).mpr hJ).injective
  · intro C g hg
    apply isEssSurj_toOfQuot_of_le at hI
    apply IsEssSurj.surjective_of_comp_left (A.toOfQuot I ≫ (mapOfQuot f hf))
    rw [toOfQuot_comp_mapOfQuot, Category.assoc', ObjectProperty.FullSubcategory.comp_hom,
      LocAlgCat.toAlgHom_comp, AlgHom.coe_comp]
    exact Ideal.Quotient.mk_surjective.comp hg

end IsLocalRing

end BaseCat
