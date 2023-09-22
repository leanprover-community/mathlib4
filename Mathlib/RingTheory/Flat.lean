/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.CategoryTheory.ShortExactSequence
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Character
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Homology.Homology

#align_import ring_theory.flat from "leanprover-community/mathlib"@"62c0a4ef1441edb463095ea02a06e87f3dfe135c"

/-!
# Flat modules

A module `M` over a commutative ring `R` is *flat*
if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.

This is equivalent to the claim that for all injective `R`-linear maps `f : M₁ → M₂`
the induced map `M₁ ⊗ M → M₂ ⊗ M` is injective.
See <https://stacks.math.columbia.edu/tag/00HD>.
This result is not yet formalised.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## TODO

* Show that tensoring with a flat module preserves injective morphisms.
  Show that this is equivalent to be flat.
  See <https://stacks.math.columbia.edu/tag/00HD>.
  To do this, it is probably a good idea to think about a suitable
  categorical induction principle that should be applied to the category of `R`-modules,
  and that will take care of the administrative side of the proof.
* Define flat `R`-algebras
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
* Show that flatness is stable under base change (aka extension of scalars)
  For base change, it will be very useful to have a "characteristic predicate"
  instead of relying on the construction `A ⊗ B`.
  Indeed, such a predicate should allow us to treat both
  `A[X]` and `A ⊗ R[X]` as the base change of `R[X]` to `A`.
  (Similar examples exist with `Fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.

-/

universe u v

namespace Module

open CategoryTheory Functor MonoidalCategory Limits

open LinearMap (lsmul)

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

open TensorProduct

def Flat.preserves_ses : Prop :=
  (tensorRight <| ModuleCat.of R M).PreservesSESs

def Flat.preserves_exactness : Prop :=
∀ ⦃N1 N2 N3 : ModuleCat.{u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (_ : Exact l12 l23),
  Exact ((tensorRight <| ModuleCat.of R M).map l12)
    ((tensorRight <| ModuleCat.of R M).map l23)

def Flat.injective : Prop :=
∀ ⦃N N' : ModuleCat.{u} R⦄ (L : N ⟶ N'),
  Function.Injective L → Function.Injective ((tensorRight (ModuleCat.of R M)).map L)

def Flat.ideal : Prop :=
  ∀ (I : Ideal R), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

def Flat.fg_ideal : Prop :=
  ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
class Flat  : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG),
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
#align module.flat Module.Flat

namespace Flat

open TensorProduct LinearMap Submodule BigOperators

instance self (R : Type u) [CommRing R] : Flat R R := ⟨by
  intro I _
  rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
  convert Subtype.coe_injective using 1
  ext x
  simp⟩
#align module.flat.self Module.Flat.self

lemma fg_ideal_of_ideal (H : Flat.ideal R M) : Flat.fg_ideal R M := fun I _ => H I

namespace injective_of_ideal

lemma baer_iff_surjective :
    Module.Baer.{u, u} R M ↔
    ∀ (I : Ideal R), Function.Surjective <| LinearMap.domRestrict' (M₂ := M) I := by
fconstructor
· intro H I g
  obtain ⟨L, H⟩:= H I g
  refine ⟨L, LinearMap.ext fun x => H x.1 x.2⟩
· intro H I g
  obtain ⟨L, H⟩ := H I g
  refine ⟨L, fun x hx => by convert FunLike.congr_fun H ⟨x, hx⟩⟩

lemma lambek [h : CategoryTheory.Injective (ModuleCat.of R <| CharacterModule M)] :
    Flat.injective R M := by
  intros A B L hL
  have m1 : Mono L
  · rwa [ConcreteCategory.mono_iff_injective_of_preservesPullback]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro z (hz : _ = 0)
  simp only [tensorRight_obj, tensorRight_map] at hz
  show z = 0
  by_contra rid
  obtain ⟨g, hg⟩ := exists_character_apply_ne_zero_of_ne_zero _ rid
  let f : A →ₗ[R] (CharacterModule M) :=
  { toFun := fun a =>
    { toFun := fun m => g (a ⊗ₜ m)
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  pick_goal 2
  · intros
    simp only [tensorRight_obj, tmul_add]
    rw [g.map_add]
  pick_goal 2
  · intros
    simp only [tensorRight_obj, tmul_smul, eq_intCast, Int.cast_id]
    rw [g.map_smul]
  pick_goal 2
  · intros
    refine LinearMap.ext fun _ => ?_
    simp only [tensorRight_obj, LinearMap.coe_mk, AddHom.coe_mk]
    rw [LinearMap.add_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [add_tmul, g.map_add]
  pick_goal 2
  · intros
    refine LinearMap.ext fun _ => ?_
    simp only [tensorRight_obj, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    rw [LinearMap.bimodule_smul_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, tmul_smul]
    rw [smul_tmul']
  obtain ⟨f', hf'⟩ := h.factors (f : A ⟶ ModuleCat.of R (CharacterModule M)) L
  obtain ⟨ι, a, m, s, rfl⟩ := TensorProduct.exists_rep _ z
  let g' : (CharacterModule <| B ⊗[R] M) := CharacterModule.homEquiv _ _ _ f'
  have EQ : g' (∑ i in s, L (a i) ⊗ₜ m i) = 0
  · rw [LinearMap.map_sum] at hz
    change ∑ i in s, (L (a i) ⊗ₜ m i) = 0 at hz
    rw [hz, g'.map_zero]
  refine hg ?_
  rw [g.map_sum]
  rw [g'.map_sum] at EQ
  simp_rw [CharacterModule.homEquiv_apply, CharacterModule.uncurry_apply,
    toAddCommGroup'_apply_tmul] at EQ
  replace hf' : ∀ x, f' (L x) = f x := FunLike.congr_fun hf'
  replace EQ : ∑ i in s, f (a i) (m i) = 0
  · rw [← EQ]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [hf']
  convert EQ

lemma injective_of_baer (h : Module.Baer.{u, u} R <| CharacterModule M) :
    Flat.injective R M :=
  lambek (h := (Module.injective_iff_injective_object _ _).mp <| Module.Baer.injective h)

lemma injective_of_surjective
    (h : ∀ (I : Ideal R), Function.Surjective <|
      LinearMap.domRestrict' (M₂ := CharacterModule M) I) :
    Flat.injective R M :=
  injective_of_baer _ _ <| (baer_iff_surjective _ _).mpr h

lemma characterfy_surj_of_inj (I : Ideal R)
    (inj : Function.Injective <| (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Function.Surjective <|
      (LinearMap.characterfy (R := R) (M := I ⊗[R] M) (N := M)
        (TensorProduct.lift ((lsmul R M).comp I.subtype))) := by
  apply LinearMap.charaterfy_surjective_of_injective
  assumption

lemma baer_characterModule_of_injective
    (inj : ∀ (I : Ideal R), Function.Injective <|
      (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Module.Baer.{u, u} R (CharacterModule M) := by
  rw [baer_iff_surjective]
  intro I L
  obtain ⟨F, hF⟩ := characterfy_surj_of_inj R _ I (inj I) <| CharacterModule.uncurry R _ _ L
  refine ⟨CharacterModule.curry _ _ _ <|
    (CharacterModule.cong R (R ⊗[R] M) M (TensorProduct.lid _ _)).symm F,
    FunLike.ext _ _ fun i => FunLike.ext _ _ fun m => ?_⟩
  simp only [CharacterModule.cong_symm_apply, characterfy_apply, domRestrict'_apply]
  rw [CharacterModule.curry_apply_apply, LinearMap.comp_apply]
  simp only [AddMonoidHom.coe_toIntLinearMap, toAddMonoidHom_coe, LinearEquiv.coe_coe, lid_tmul]
  have EQ := FunLike.congr_fun hF (i ⊗ₜ m)
  simp only [characterfy_apply] at EQ
  rw [LinearMap.comp_apply] at EQ
  simp only [AddMonoidHom.coe_toIntLinearMap, toAddMonoidHom_coe, lift.tmul, LinearMap.coe_comp,
    coeSubtype, Function.comp_apply, lsmul_apply] at EQ
  exact EQ

lemma main (ideal : Flat.ideal R M) : Flat.injective R M := by
  apply injective_of_baer
  apply baer_characterModule_of_injective
  exact ideal

end injective_of_ideal

lemma injective_of_ideal (ideal : Flat.ideal R M) : Flat.injective R M :=
  injective_of_ideal.main R M ideal

namespace ideal_of_fg_ideal

end ideal_of_fg_ideal

lemma tfae : List.TFAE
    [ Flat.injective R M,
      Flat.ideal R M,
      Flat.fg_ideal R M ] := by
  tfae_have 2 → 1
  · apply injective_of_ideal
  tfae_have 1 → 2
  · intro H I
    specialize H (ModuleCat.ofHom (R := R) (X := I) (Y := R) <| Submodule.subtype _)
      (Submodule.injective_subtype _)
    intro x y h
    apply H
    simp only [tensorRight_obj, tensorRight_map]
    change TensorProduct.map _ LinearMap.id _ =
      TensorProduct.map _ LinearMap.id _
    apply_fun TensorProduct.lid R M using LinearEquiv.injective _
    change ((TensorProduct.lid _ _).toLinearMap ∘ₗ _) x =
      ((TensorProduct.lid _ _).toLinearMap ∘ₗ _) _
    convert h <;>
    · refine TensorProduct.ext ?_
      ext i m : 2
      simp only [compr₂_apply, mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, lift.tmul, coeSubtype, lsmul_apply]
      rfl
  tfae_have 2 → 3
  · intro H I _
    exact H I
  tfae_have 3 → 2
  · sorry
  tfae_finish

end Flat

end Module
