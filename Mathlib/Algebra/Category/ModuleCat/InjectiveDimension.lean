/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Baer
public import Mathlib.Algebra.Category.ModuleCat.Ext.Ulift
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!

# Injective Dimension in ModuleCat

-/

@[expose] public section

universe u u' v v'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

private instance small_of_quotient [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

namespace CategoryTheory

section

lemma hasInjectiveDimensionLT_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}
    (e' : M ≃ₗ[R] N) (n : ℕ) [HasInjectiveDimensionLT M n] :
    HasInjectiveDimensionLT N n := by
  apply (hasInjectiveDimensionLT_iff.{v'} _ n).mpr (fun i hi L x ↦ ?_)
  apply @Subsingleton.eq_zero _ _ ?_ x
  apply ext_subsingleton_of_quotients N i (fun I ↦ ?_)
  let e'' : (ModuleCat.of R (Shrink.{v} (R ⧸ I))) ≃ₗ[R] (ModuleCat.of R (Shrink.{v'} (R ⧸ I))) :=
    (Shrink.linearEquiv.{v} R (R ⧸ I)).trans (Shrink.linearEquiv.{v'} R (R ⧸ I)).symm
  rw [← (ModuleCat.extLinearEquivOfLinearEquiv e'' e' i).subsingleton_congr]
  exact HasInjectiveDimensionLT.subsingleton.{v} M n i hi _

lemma injectiveDimension_eq_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R} (e : M ≃ₗ[R] N) :
    injectiveDimension M = injectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [injectiveDimension_le_iff]
      refine ⟨fun h ↦ hasInjectiveDimensionLT_of_linearEquiv e (n + 1),
        fun h ↦ hasInjectiveDimensionLT_of_linearEquiv e.symm (n + 1)⟩

end

section

variable {R' : Type u'} [CommRing R'] (e : R ≃+* R')

attribute [local instance] RingHomInvPair.of_ringEquiv

lemma hasInjectiveDimensionLT_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}
    (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) (n : ℕ) [HasInjectiveDimensionLT M n] :
    HasInjectiveDimensionLT N n := by
  apply (hasInjectiveDimensionLT_iff.{v'} _ n).mpr (fun i hi L x ↦ ?_)
  apply @Subsingleton.eq_zero _ _ ?_ x
  apply ext_subsingleton_of_quotients N i (fun I ↦ ?_)
  let e''' : (R ⧸ (I.comap e)) ≃ₛₗ[RingHomClass.toRingHom e] (R' ⧸ I) := {
    __ := Ideal.quotientEquiv (I.comap e) I e (I.map_comap_eq_self_of_equiv e).symm
    map_smul' r x := by
      rcases Ideal.Quotient.mk_surjective x with ⟨y, hy⟩
      simp [Ideal.quotientMap, ← hy, Algebra.smul_def] }
  let e'' : (ModuleCat.of R (Shrink.{v} (R ⧸ (I.comap e)))) ≃ₛₗ[RingHomClass.toRingHom e]
    (ModuleCat.of R' (Shrink.{v', u'} (R' ⧸ I))) :=
    ((Shrink.linearEquiv.{v} R _).trans e''').trans (Shrink.linearEquiv.{v'} R' _).symm
  rw [(ModuleCat.extSemiLinearEquivOfSemiLinearEquiv e e'' e' i).subsingleton_congr]
  exact HasInjectiveDimensionLT.subsingleton.{v} M n i hi _

lemma injectiveDimension_eq_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}
    (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) :
    injectiveDimension M = injectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e'.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [injectiveDimension_le_iff]
      refine ⟨fun h ↦ hasInjectiveDimensionLT_of_semiLinearEquiv e e' (n + 1),
        fun h ↦ hasInjectiveDimensionLT_of_semiLinearEquiv e.symm e'.symm (n + 1)⟩

end

end CategoryTheory
