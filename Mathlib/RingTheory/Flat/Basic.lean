/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness

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

## Main theorems

* `Module.Flat.of_retract`: retracts of flat modules are flat
* `Module.Flat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
* `Module.Flat.directSum`: arbitrary direct sums of flat modules are flat
* `Module.Flat.of_free`: free modules are flat
* `Module.Flat.of_projective`: projective modules are flat

## TODO

* Show that tensoring with a flat module preserves injective morphisms.
  Show that this is equivalent to be flat.
  See <https://stacks.math.columbia.edu/tag/00HD>.
  To do this, it is probably a good idea to think about a suitable
  categorical induction principle that should be applied to the category of `R`-modules,
  and that will take care of the administrative side of the proof.
* Show that flatness is stable under base change (aka extension of scalars)
  For base change, it will be very useful to have a "characteristic predicate"
  instead of relying on the construction `A ⊗ B`.
  Indeed, such a predicate should allow us to treat both
  `A[X]` and `A ⊗ R[X]` as the base change of `R[X]` to `A`.
  (Similar examples exist with `Fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.
-/


universe u v w

namespace Module

open Function (Surjective)

open LinearMap Submodule TensorProduct

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
class Flat : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
#align module.flat Module.Flat

/-- An `R`-module is flat if for all injectives `R`-linear maps `L : N → N'`, `L ⊗ 𝟙 M` is also
  injective. -/
def Flat.rTensor_preserves_injectiveness
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M)
namespace Flat

instance self : Flat R R :=
  ⟨by
    intro I _
    rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
    convert Subtype.coe_injective using 1
    ext x
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, rid_symm_apply, comp_apply, mul_one,
      lift.tmul, Submodule.subtype_apply, Algebra.id.smul_eq_mul, lsmul_apply]⟩
#align module.flat.self Module.Flat.self

/-- An `R`-module `M` is flat iff for all finitely generated ideals `I` of `R`, the
tensor product of the inclusion `I → R` and the identity `M → M` is injective. See
`iff_rTensor_injective'` to extend to all ideals `I`. --/
lemma iff_rTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (rTensor M I.subtype) := by
  have aux : ∀ I : Ideal R, (TensorProduct.lid R M).comp (rTensor M I.subtype) =
      TensorProduct.lift ((lsmul R M).comp I.subtype) := by
    intro I; apply TensorProduct.ext'; intro x y; simp
  constructor
  · intro F I hI
    erw [← Equiv.comp_injective _ (TensorProduct.lid R M).toEquiv]
    have h₁ := F.out hI
    rw [← aux] at h₁
    exact h₁
  · intro h₁
    constructor
    intro I hI
    rw [← aux]
    simp [h₁ hI]

/-- An `R`-module `M` is flat iff for all ideals `I` of `R`, the tensor product of the
inclusion `I → R` and the identity `M → M` is injective. See `iff_rTensor_injective` to
restrict to finitely generated ideals `I`. --/
theorem iff_rTensor_injective' :
    Flat R M ↔ ∀ I : Ideal R, Function.Injective (rTensor M I.subtype) := by
  rewrite [Flat.iff_rTensor_injective]
  refine ⟨fun h I => ?_, fun h I _ => h I⟩
  rewrite [injective_iff_map_eq_zero]
  intro x hx₀
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rewrite [← rTensor_comp_apply] at hx₀
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx₀, LinearMap.map_zero]

/-- Given a linear map `f : N → P`, `f ⊗ M` is injective if and only if `M ⊗ f` is injective. -/
lemma lTensor_inj_iff_rTensor_inj {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N]
    [Module R P] (f : N →ₗ[R] P) :
    Function.Injective (lTensor M f) ↔ Function.Injective (rTensor M f) := by
  haveI h1 : rTensor M f ∘ₗ TensorProduct.comm R M N =
    TensorProduct.comm R M P ∘ₗ lTensor M f := ext rfl
  haveI h2 : ⇑(TensorProduct.comm R M P) ∘ ⇑(lTensor M f) =
    (TensorProduct.comm R M P) ∘ₗ (lTensor M f) := rfl
  simp only [← EquivLike.injective_comp (TensorProduct.comm R M N),
    ← EquivLike.comp_injective _ (TensorProduct.comm R M P), h2, ← h1]
  trivial

/-- The `lTensor`-variant of `iff_rTensor_injective`. .-/
theorem iff_lTensor_injective :
    Module.Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (lTensor M I.subtype) := by
  simp only [lTensor_inj_iff_rTensor_inj]
  exact Module.Flat.iff_rTensor_injective R M

/-- The `lTensor`-variant of `iff_rTensor_injective'`. .-/
theorem iff_lTensor_injective' :
    Module.Flat R M ↔ ∀ (I : Ideal R), Function.Injective (lTensor M I.subtype) := by
  simp only [lTensor_inj_iff_rTensor_inj]
  exact Module.Flat.iff_rTensor_injective' R M

variable (N : Type w) [AddCommGroup N] [Module R N]

/-- A retract of a flat `R`-module is flat. -/
lemma of_retract [f : Flat R M] (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r.comp i = LinearMap.id) :
    Flat R N := by
  rw [iff_rTensor_injective] at *
  intro I hI
  have h₁ : Function.Injective (lTensor R i) := by
    apply Function.RightInverse.injective (g := (lTensor R r))
    intro x
    rw [← LinearMap.comp_apply, ← lTensor_comp, h]
    simp
  rw [← Function.Injective.of_comp_iff h₁ (rTensor N I.subtype), ← LinearMap.coe_comp]
  rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  rw [LinearMap.coe_comp, Function.Injective.of_comp_iff (f hI)]
  apply Function.RightInverse.injective (g := lTensor _ r)
  intro x
  rw [← LinearMap.comp_apply, ← lTensor_comp, h]
  simp

/-- A `R`-module linearly equivalent to a flat `R`-module is flat. -/
lemma of_linearEquiv [f : Flat R M] (e : N ≃ₗ[R] M) : Flat R N := by
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by simp
  exact of_retract _ _ _ e.toLinearMap e.symm.toLinearMap h

open DirectSum

/-- A direct sum of flat `R`-modules is flat. -/
instance directSum (ι : Type v) (M : ι → Type w) [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module R (M i)] [F : (i : ι) → (Flat R (M i))] : Flat R (⨁ i, M i) := by
  haveI := Classical.decEq ι
  rw [iff_rTensor_injective]
  intro I hI
  -- This instance was added during PR #10828,
  -- see https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2310828.20-.20generalizing.20CommRing.20to.20CommSemiring.20etc.2E/near/422684923
  letI : ∀ i, AddCommGroup (I ⊗[R] M i) := inferInstance
  rw [← Equiv.comp_injective _ (TensorProduct.lid R (⨁ i, M i)).toEquiv]
  set η₁ := TensorProduct.lid R (⨁ i, M i)
  set η := (fun i ↦ TensorProduct.lid R (M i))
  set φ := (fun i ↦ rTensor (M i) I.subtype)
  set π := (fun i ↦ component R ι (fun j ↦ M j) i)
  set ψ := (TensorProduct.directSumRight R {x // x ∈ I} (fun i ↦ M i)).symm.toLinearMap with psi_def
  set ρ := rTensor (⨁ i, M i) I.subtype
  set τ := (fun i ↦ component R ι (fun j ↦ ({x // x ∈ I} ⊗[R] (M j))) i)
  rw [← Equiv.injective_comp (TensorProduct.directSumRight _ _ _).symm.toEquiv]
  rw [LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  rw [LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  rw [← psi_def, injective_iff_map_eq_zero ((η₁.comp ρ).comp ψ)]
  have h₁ : ∀ (i : ι), (π i).comp ((η₁.comp ρ).comp ψ) = (η i).comp ((φ i).comp (τ i)) := by
    intro i
    apply DirectSum.linearMap_ext
    intro j
    apply TensorProduct.ext'
    intro a m
    simp only [ρ, ψ, φ, η, η₁, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      directSumRight_symm_lof_tmul, rTensor_tmul, Submodule.coeSubtype, lid_tmul, map_smul]
    rw [DirectSum.component.of, DirectSum.component.of]
    by_cases h₂ : j = i
    · subst j; simp
    · simp [h₂]
  intro a ha; rw [DirectSum.ext_iff R]; intro i
  have f := LinearMap.congr_arg (f := (π i)) ha
  erw [LinearMap.congr_fun (h₁ i) a] at f
  rw [(map_zero (π i) : (π i) 0 = (0 : M i))] at f
  have h₂ := (F i)
  rw [iff_rTensor_injective] at h₂
  have h₃ := h₂ hI
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, AddEquivClass.map_eq_zero_iff,
    h₃, LinearMap.map_eq_zero_iff] at f
  simp [f]

/-- Free `R`-modules over discrete types are flat. -/
instance finsupp (ι : Type v) : Flat R (ι →₀ R) :=
  haveI := Classical.decEq ι
  of_linearEquiv R _ _ (finsuppLEquivDirectSum R R ι)

instance of_free [Free R M] : Flat R M := of_linearEquiv R _ _ (Free.repr R M)

/-- A projective module with a discrete type of generator is flat -/
lemma of_projective_surjective (ι : Type w) [Projective R M] (p : (ι →₀ R) →ₗ[R] M)
    (hp : Surjective p) : Flat R M := by
  have h := Module.projective_lifting_property p (LinearMap.id) hp
  cases h with
    | _ e he => exact of_retract R _ _ _ _ he

instance of_projective [h : Projective R M] : Flat R M := by
  rw [Module.projective_def'] at h
  cases h with
    | _ e he => exact of_retract R _ _ _ _ he

open BigOperators in
lemma rTensor_preserves_injectiveness_of_injective_characterModule
    (h : Module.Injective R <| CharacterModule M) :
    Flat.rTensor_preserves_injectiveness R M := by
  intros A B _ _ _ _ L hL
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro z (hz : _ = 0)
  show z = 0
  by_contra rid
  obtain ⟨g, hg⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero (a := z) rid

  let f : A →ₗ[R] (CharacterModule M) :=
  { toFun := fun a =>
    { toFun := fun m => g (a ⊗ₜ m)
      map_add' := fun _ _ => by simp only [tmul_add, map_add]
      map_zero' := by simp }
    map_add' := fun _ _ => AddMonoidHom.ext fun _ => by
      change g _ = g _ + g _
      rw [add_tmul, map_add]
    map_smul' := fun _ _ => AddMonoidHom.ext fun _ => by
      change g _ = g _
      aesop }
  obtain ⟨f', hf'⟩ := h.out L hL f
  have mem : z ∈ (⊤ : Submodule R _) := ⟨⟩
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
  obtain ⟨c, hc, (eq1 : ∑ i in c.support, _ • _ = z)⟩ := mem
  choose a m H using hc
  replace eq1 : ∑ i in c.support.attach, (c i • a i.2) ⊗ₜ (m i.2) = z := by
    conv_rhs => rw [← eq1, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← smul_tmul']
    exact congr(c i • $(H i.2))
  subst eq1
  let g' : (CharacterModule <| B ⊗[R] M) :=
    CharacterModule.homEquiv f'
  have EQ : g' (∑ i in c.support.attach, L (c i • a i.2) ⊗ₜ m i.2) = 0 := by
    simp only [map_sum, rTensor_tmul] at hz
    rw [hz, map_zero]
  refine hg ?_
  rw [map_sum] at EQ ⊢
  convert EQ using 1
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp [CharacterModule.homEquiv]
  erw [liftAddHom_tmul, L.map_smul, f'.map_smul, hf', CharacterModule.smul_apply, smul_tmul]
  rfl

lemma _root_.Module.Baer.characterModule_of_ideal
    (inj : ∀ (I : Ideal R), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Module.Baer R (CharacterModule M) := by
  letI : Module.Injective ℤ (AddCircle (1 : ℚ)) := by
    erw [Module.injective_iff_injective_object, AddCommGroupCat.injective_as_module_iff]
    have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
    apply AddCommGroupCat.injective_of_divisible _
  rintro I (L : _ →ₗ[_] _)
  letI :  AddCommGroup (I ⊗[R] M) := inferInstance
  obtain ⟨F, hF⟩ := CharacterModule.dual_surjective_of_injective _ (inj I) <|
      TensorProduct.liftAddHom
        { toFun := fun i => L i
          map_zero' := by aesop
          map_add' := by aesop } <| by aesop
  refine ⟨CharacterModule.curry (CharacterModule.congr (TensorProduct.lid R M).symm F), ?_⟩
  intros x hx
  ext m
  exact congr($hF (⟨x, hx⟩ ⊗ₜ m))

lemma rTensor_preserves_injectiveness_of_ideal
    (inj : ∀ (I : Ideal R), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Flat.rTensor_preserves_injectiveness R M := by
  apply rTensor_preserves_injectiveness_of_injective_characterModule
  apply Module.Baer.injective
  apply Module.Baer.characterModule_of_ideal
  assumption

lemma of_rTensor_preserves_injectiveness [UnivLE.{u, v}]
    (h : rTensor_preserves_injectiveness R M) :
    Flat R M := by
  rw [Flat.iff_rTensor_injective']
  intro I x y eq1
  let e : I ⊗[R] M ≃ₗ[R] (Shrink I) ⊗[R] M := LinearEquiv.ofLinear
    ((Shrink.linearEquiv I R).symm.toLinearMap.rTensor M)
    ((Shrink.linearEquiv I R).toLinearMap.rTensor M)
    (LinearMap.ext fun z ↦ z.induction_on (by aesop)
      (fun i m ↦ by
        simp only [coe_comp, Function.comp_apply, rTensor_tmul, LinearEquiv.coe_coe,
          Shrink.linearEquiv_apply, Shrink.linearEquiv_symm_apply, id_coe, id_eq]
        erw [Equiv.symm_apply_apply]) (by aesop))
    (LinearMap.ext fun z ↦ z.induction_on (by aesop)
      (fun i m ↦ by
        simp only [coe_comp, Function.comp_apply, rTensor_tmul, LinearEquiv.coe_coe,
          Shrink.linearEquiv_apply, Shrink.linearEquiv_symm_apply, id_coe, id_eq]
        erw [Equiv.symm_apply_apply]) (by aesop))
  apply_fun e using e.injective
  have H := @h (Shrink I) (Shrink R) _ _ _ _
    ((Shrink.linearEquiv R R).symm.toLinearMap ∘ₗ I.subtype ∘ₗ (Shrink.linearEquiv I R).toLinearMap)
    ((Shrink.linearEquiv R R).symm.injective.comp
      (Subtype.val_injective.comp (Shrink.linearEquiv I R).injective))
  refine @H (e x) (e y) ?_
  set L : Shrink I ⊗[R] M →ₗ[R] Shrink R ⊗[R] M := _
  convert_to L (e x) = L (e y)
  suffices eq2 : L ∘ₗ e.toLinearMap =
    (rTensor M (Shrink.linearEquiv R R).symm.toLinearMap) ∘ₗ rTensor M (Submodule.subtype I) by
    erw [congr($eq2 x), congr($eq2 y), LinearMap.comp_apply, eq1, LinearMap.comp_apply]
  refine TensorProduct.ext <| LinearMap.ext fun i ↦ LinearMap.ext fun m ↦ ?_
  simp only [compr₂_apply, mk_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.ofLinear_apply, rTensor_tmul, Shrink.linearEquiv_symm_apply, Submodule.coeSubtype,
    Shrink.linearEquiv_apply]
  congr
  erw [Equiv.symm_symm_apply, Equiv.symm_apply_apply]

lemma iff_rTensor_preserves_injectiveness [UnivLE.{u, v}] :
    Flat R M ↔ Flat.rTensor_preserves_injectiveness R M where
  mp h := by
    apply rTensor_preserves_injectiveness_of_ideal
    rw [Flat.iff_rTensor_injective'] at h
    intro I x y eq1
    specialize h I
    apply h
    suffices (TensorProduct.lid _ _).symm.toLinearMap ∘ₗ
      (lift (lsmul R M ∘ₗ Submodule.subtype I)) = rTensor M (Submodule.subtype I) by
      rw [← this, LinearMap.comp_apply, LinearMap.comp_apply, eq1]
    refine TensorProduct.ext <| LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
    simp only [compr₂_apply, mk_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      lift.tmul, Submodule.coeSubtype, lsmul_apply, map_smul, lid_symm_apply, rTensor_tmul]
    rw [smul_tmul', smul_eq_mul, mul_one]
  mpr := of_rTensor_preserves_injectiveness R M


end Flat


end Module
