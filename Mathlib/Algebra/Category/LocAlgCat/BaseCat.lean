/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocAlgCat.Basic
public import Mathlib.RingTheory.Length

import Mathlib.RingTheory.HopkinsLevitzki

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
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦ IsArtinianRing A

namespace BaseCat

variable {A B : BaseCat.{w} Λ k} {f : A ⟶ B}

instance (A : BaseCat Λ k) : IsArtinianRing A.obj := A.property

variable (Λ k) in
/-- The object in the base category associated to a type equipped with appropriate typeclasses.
This is a preferred way to construct a term of `BaseCat`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [Algebra X k]
    [IsScalarTower Λ X k] [IsArtinianRing X] (hX : Surjective (algebraMap X k)) :
    BaseCat Λ k := ⟨.of Λ k X hX, inferInstance⟩

/-- The quotient of an object `A` in `BaseCat` by a proper ideal `I`. -/
def ofQuot (A : BaseCat.{w} Λ k) (I : Ideal A.obj) [Nontrivial (A.obj ⧸ I)] : BaseCat Λ k :=
  ⟨A.obj.ofQuot I, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- Upgrades the canonical quotient map from `A` to `A ⧸ I` to a morphism in `BaseCat`. -/
def toOfQuot (A : BaseCat.{w} Λ k) (I : Ideal A.obj) [Nontrivial (A.obj ⧸ I)] :
    A ⟶ A.ofQuot I := ObjectProperty.homMk (A.obj.toOfQuot I)

/-- A morphism `f : A ⟶ B` in `BaseCat` is a small extension if it is a surjective map
whose kernel is a principal ideal annihilated by the maximal ideal of `A`. -/
@[stacks 06GD]
class IsSmallExtension (f : A ⟶ B) : Prop where
  private mk ::
  surjective (f) : Function.Surjective f.hom.toAlgHom
  isPrincipal_ker (f) : (RingHom.ker f.hom.toAlgHom).IsPrincipal
  le_annihilator_ker (f) : maximalIdeal A.obj ≤ (RingHom.ker f.hom.toAlgHom).annihilator

theorem isSmallExtenstion_iff : IsSmallExtension f ↔ Function.Surjective f.hom.toAlgHom ∧
    ∃ x : A.obj, Ideal.span {x} = RingHom.ker f.hom.toAlgHom ∧
      ∀ y ∈ maximalIdeal A.obj, x * y = 0 := by
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

theorem IsSmallExtension.toOfQuot_span_singleton (A : BaseCat.{w} Λ k) (x : A.obj)
    [Nontrivial (A.obj ⧸ (Ideal.span {x}))] (h : ∀ y ∈ maximalIdeal A.obj, x * y = 0) :
    IsSmallExtension (A.toOfQuot (Ideal.span {x})) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, h⟩
  ext; rw [← Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

open Submodule in
@[elab_as_elim, stacks 06GE]
theorem induction_on_isSmallExtension (hf : Surjective f.hom.toAlgHom)
    {P : ∀ {A B : BaseCat.{w} Λ k} (f : A ⟶ B), Surjective f.hom.toAlgHom → Prop}
    (small_ext : ∀ {X Y : BaseCat.{w} Λ k} (f : X ⟶ Y) [IsSmallExtension f],
      P f (IsSmallExtension.surjective f))
    (comp : ∀ {A B C : BaseCat.{w} Λ k} (f : A ⟶ B) (g : B ⟶ C) [IsSmallExtension f]
      (hg : Surjective g.hom.toAlgHom), P g hg →
    P (f ≫ g) (hg.comp (IsSmallExtension.surjective f))) : P f hf := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Module.length A.obj A.obj :=
    ENat.ne_top_iff_exists.mp Module.length_ne_top
  symm at hn; revert A
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A f hf hlen
    have hn : n ≠ 0 := by
      intro hn; revert hlen
      have : Nontrivial A.obj := inferInstance
      simpa [hn, Module.length_eq_zero_iff, ← not_nontrivial_iff_subsingleton]
    let I := RingHom.ker f.hom.toAlgHom
    by_cases hI : I = ⊥
    · rw [← RingHom.injective_iff_ker_eq_bot] at hI
      have : IsSmallExtension f := isSmallExtension_of_bijective ⟨hI, hf⟩
      exact small_ext f
    obtain ⟨x, hx, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Ideal.annihilator_inf_ne_bot
      ((isArtinianRing_iff_isNilpotent_maximalIdeal A.obj).mp inferInstance) hI)
    have x_in : x ∈ I := (mem_inf.mp hx).right
    replace hx : ∀ y ∈ maximalIdeal A.obj, x * y = 0 := mem_annihilator.mp (mem_inf.mp hx).left
    have span_ne_top : Ideal.span {x} ≠ ⊤ := by
      refine Ideal.span_singleton_ne_top (le_maximalIdeal ?_ x_in)
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨maximalIdeal A.obj, maximalIdeal.isMaximal A.obj, le_maximalIdeal
        (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have : Nontrivial (A.obj ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr span_ne_top
    have : IsLocalRing (A.obj ⧸ Ideal.span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have aux : ∀ a ∈ Ideal.span {x}, (LocAlgCat.Hom.toAlgHom f.hom) a = 0 := by
      intro _ h; rw [Ideal.mem_span_singleton'] at h
      rcases h with ⟨_, rfl⟩; rw [← RingHom.mem_ker]
      exact Ideal.mul_mem_left _ _ x_in
    let C := A.ofQuot (Ideal.span {x})
    let g : A ⟶ C := A.toOfQuot (Ideal.span {x})
    have hg : IsSmallExtension g := IsSmallExtension.toOfQuot_span_singleton A x hx
    let u : C.obj →ₐ[Λ] B.obj := Ideal.Quotient.liftₐ (Ideal.span {x}) f.hom.toAlgHom aux
    have u_surj : Surjective u :=
      Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) aux hf
    let f' : C ⟶ B := ObjectProperty.homMk (LocAlgCat.ofHom u (eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ ‹_›)) (AlgHom.ext fun t ↦ by
        induction t using Quotient.induction_on with
        | H t =>
          simp [← AlgHom.comp_apply, f.hom.residue_comp, u]
          simpa [LocAlgCat.residue, ← Ideal.Quotient.algebraMap_eq] using
            IsScalarTower.algebraMap_apply ..))
    obtain ⟨m, hm⟩ : ∃ n : ℕ, n = Module.length C.obj C.obj :=
      ENat.ne_top_iff_exists.mp Module.length_ne_top
    symm at hm; suffices h : m < n by
      change P (g ≫ f') _; apply comp
      · apply ih m h; exact hm
      · exact u_surj
    change Module.length (A.obj ⧸ Ideal.span {x}) (A.obj ⧸ Ideal.span {x}) = m at hm
    have := Submodule.length_le_length_restrictScalars (R := (A.obj ⧸ Ideal.span {x}))
      (M := (A.obj ⧸ Ideal.span {x})) A.obj ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, ← hlen, ← hm]
    exact lt_of_le_of_lt this (length_quotient_lt (Ideal.span {x}) (by simpa))

end BaseCat
