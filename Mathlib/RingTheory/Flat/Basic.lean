/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Projective

#align_import ring_theory.flat from "leanprover-community/mathlib"@"62c0a4ef1441edb463095ea02a06e87f3dfe135c"

/-!
# Flat modules

A module `M` over a commutative ring `R` is *flat*
if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.

This is equivalent to the claim that for all injective `R`-linear maps `f : M₁ → M₂`
the induced map `M₁ ⊗ M → M₂ ⊗ M` is injective.
See <https://stacks.math.columbia.edu/tag/00HD>.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## Main theorems

* `Module.Flat.of_retract`: retracts of flat modules are flat
* `Module.Flat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
* `Module.Flat.directSum`: arbitrary direct sums of flat modules are flat
* `Module.Flat.of_free`: free modules are flat
* `Module.Flat.of_projective`: projective modules are flat
* `Module.Flat.iff_rTensor_preserves_injectiveness`: a module is flat iff tensoring preserves
  injectiveness.

## TODO

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
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG),
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
#align module.flat Module.Flat

namespace Flat

instance self (R : Type u) [CommRing R] : Flat R R :=
  ⟨by
    intro I _
    rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
    convert Subtype.coe_injective using 1
    ext x
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, rid_symm_apply, comp_apply, mul_one,
      lift.tmul, Submodule.subtype_apply, Algebra.id.smul_eq_mul, lsmul_apply]⟩
#align module.flat.self Module.Flat.self

variable (M : Type v) [AddCommGroup M] [Module R M]

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
  letI : AddCommGroup (I ⊗[R] M) := inferInstance -- Type class reminder
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

end Flat

namespace Flat

open DirectSum LinearMap Submodule

variable (R : Type u) [CommRing R]

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

open Classical in
/-- Free `R`-modules over discrete types are flat. -/
instance finsupp (ι : Type v) : Flat R (ι →₀ R) :=
  of_linearEquiv R _ _ (finsuppLEquivDirectSum R R ι)

variable (M : Type v) [AddCommGroup M] [Module R M]

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
/--
Define character module of `M` to be `M → ℚ ⧸ ℤ`
If the character module of `M` is an injective module then `L ⊗ 𝟙 M` is injective for any linear map
`L`.
-/
lemma rTensor_preserves_injective_linearMap_of_injective_characterModule
    (h : Module.Injective R <| CharacterModule M) :
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M) := by
  intros A B _ _ _ _ L hL
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro z (hz : _ = 0)
  -- Consider an injective linear map `L : A → B`, we want to prove that `(L ⊗ 𝟙 M) z = 0`
  -- implies `z = 0`
  show z = 0
  by_contra rid
  -- Let's prove by contradication
  -- If `z ≠ 0`, then there would be some character `g ∈ (A ⊗ M)⋆` such that `g z ≠ 0`
  obtain ⟨g, hg⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero (a := z) rid

  -- Then we can define a linear map `f : A → M⋆` by `f a m = g (a ⊗ m)`.
  let f : A →ₗ[R] (CharacterModule M) := CharacterModule.homEquiv.symm g
  -- Since `M⋆` is an injective module, we can factor `f` to `f' ∘ L` where `f' : B → M⋆`.
  obtain ⟨f', hf'⟩ := h.out L hL f
  -- Since `B → M⋆`  is naturally isomorphic to `(B ⊗ M)⋆`, we get a character `g' : (B ⊗ M)⋆`
  let g' : (CharacterModule <| B ⊗[R] M) :=
    CharacterModule.homEquiv f'

  have mem : z ∈ (⊤ : Submodule R _) := ⟨⟩
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
  obtain ⟨c, hc, (eq1 : ∑ i in c.support, _ • _ = z)⟩ := mem
  choose a m H using hc
  -- Let's write `z ∈ A ⊗ M` as `∑ aᵢ ⊗ mᵢ`
  replace eq1 : ∑ i in c.support.attach, (c i • a i.2) ⊗ₜ (m i.2) = z := by
    conv_rhs => rw [← eq1, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← smul_tmul']
    exact congr(c i • $(H i.2))
  subst eq1
  -- Then `g'(∑ L aᵢ ⊗ mᵢ)` is zero because `(L ⊗ 𝟙 M) z = 0 = ∑ L aᵢ ⊗ mᵢ`
  have EQ : g' (∑ i in c.support.attach, L (c i • a i.2) ⊗ₜ m i.2) = 0 := by
    simp only [map_sum, rTensor_tmul] at hz
    rw [hz, map_zero]
  -- Now, we aim to show that `g z = 0` and obtain the desired contradiction.
  refine hg ?_
  rw [map_sum] at EQ ⊢
  -- Since `∑ g'(L aᵢ ⊗ mᵢ) = 0` and `g'` is obtained by `f' : B → M⋆`,
  -- we now know `∑ f'(L aᵢ)(mᵢ) = 0` so that `∑ f(aᵢ)(mᵢ) = 0`
  -- But by definition of `f`, this is saying `∑ g (aᵢ ⊗ mᵢ) = 0`, i.e. `g z = 0`
  convert EQ using 1
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp [CharacterModule.homEquiv]
  erw [liftAddHom_tmul, L.map_smul, f'.map_smul, hf', CharacterModule.smul_apply, smul_tmul]
  rfl

-- We have established a connection between preserving injectiveness of linear map and character
-- module being an injective module. We use Baer's criterion to investigate this connection further.

/--
`M⋆` is Baer, if `I ⊗ M → M` is injective for every ideal `I`
-/
lemma CharacterModule.baer_of_ideal
    (inj : ∀ (I : Ideal R), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Module.Baer R (CharacterModule M) := by
  -- Let `I` be an ideal and `L : I → M⋆`, we want to extend `L` to the entire ring
  rintro I (L : _ →ₗ[_] _)
  letI :  AddCommGroup (I ⊗[R] M) := inferInstance
  -- We know that every linear map `f : A → B` induces `f⋆ : B⋆ → A⋆` and if `f` is injective then
  -- `f⋆` is surjective.
  -- Under our assumption `ι : I ⊗ M → M` is injective, so `ι⋆ : M⋆ → (I ⊗ M)⋆` is surjective, so
  -- there is a character `F : M⋆` such that `ι⋆F (i ⊗ m) = L i m`
  obtain ⟨F, hF⟩ := CharacterModule.dual_surjective_of_injective _ (inj I) <|
      TensorProduct.liftAddHom
        { toFun := fun i => L i
          map_zero' := by aesop
          map_add' := by aesop } <| by aesop
  -- Since `R ⊗ M ≃ M`, `M⋆ ≃ (R ⊗ M)⋆ ≃ Hom(R, M⋆)`, under this equivalence, we can reinterpret
  -- `F` as `F' : R → M⋆`. Indeed `F' i = L i m` by definition
  refine ⟨CharacterModule.curry (CharacterModule.congr (TensorProduct.lid R M).symm F), ?_⟩
  intros x hx
  ext m
  exact congr($hF (⟨x, hx⟩ ⊗ₜ m))

/--
If `I ⊗ M → M` is injective for every ideal `I`, then `f ⊗ 𝟙 M` is injective for every injective
linear map `f`.
-/
lemma rTensor_preserves_injective_linearMap_of_ideal
    (inj : ∀ (I : Ideal R), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'](L : N →ₗ[R] N'),
      Function.Injective L → Function.Injective (L.rTensor M) := by
  apply rTensor_preserves_injective_linearMap_of_injective_characterModule
  apply Module.Baer.injective
  apply CharacterModule.baer_of_ideal
  assumption

/--
If `f ⊗ 𝟙 M` is injective for every injective linear map `f`, then `M` is flat.
-/
lemma of_rTensor_preserves_injective_linearMap [UnivLE.{u, v}]
    (h : ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M)) :
    Flat R M := by
  rw [Flat.iff_rTensor_injective']
  intro I x y eq1
  let e := TensorProduct.congr (Shrink.linearEquiv I R).symm (LinearEquiv.refl R M)
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
  simp only [compr₂_apply, mk_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, congr_tmul,
    Shrink.linearEquiv_symm_apply, LinearEquiv.refl_apply, rTensor_tmul, Submodule.coeSubtype,
    Shrink.linearEquiv_apply]
  congr 1
  erw [Equiv.symm_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm_apply]

/--
M is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective lienar map.
-/
lemma iff_rTensor_preserves_injective_linearMap [UnivLE.{u, v}] :
    Flat R M ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M) := by
  constructor
  · intro h
    apply rTensor_preserves_injective_linearMap_of_ideal
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
  · exact of_rTensor_preserves_injective_linearMap R M


end Flat

end Module
