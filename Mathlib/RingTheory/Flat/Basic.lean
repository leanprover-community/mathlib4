/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang, Yongle Hu
-/
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.TensorProduct

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
* `Module.Flat.preserves_injective_linearMap`: If `M` is a flat module then tensoring with `M`
  preserves injectivity of linear maps. This lemma is fully universally polymorphic in all
  arguments, i.e. `R`, `M` and linear maps `N → N'` can all have different universe levels.
* `Module.Flat.iff_rTensor_preserves_injective_linearMap`: a module is flat iff tensoring modules
  in the higher universe preserves injectivity .
* `Module.Flat.lTensor_exact`: If `M` is a flat module then tensoring with `M` is an exact
  functor. This lemma is fully universally polymorphic in all arguments, i.e.
  `R`, `M` and linear maps `N → N' → N''` can all have different universe levels.
* `Module.Flat.iff_lTensor_exact`: a module is flat iff tensoring modules
  in the higher universe is an exact functor.

## TODO

* Generalize flatness to noncommutative rings.

-/


universe v' u v w

open TensorProduct

namespace Module

open Function (Surjective)

open LinearMap Submodule DirectSum

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
@[mk_iff] class Flat : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG),
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

namespace Flat

variable {R} in
instance instSubalgebraToSubmodule {S : Type v} [Ring S] [Algebra R S]
    (A : Subalgebra R S) [Flat R A] : Flat R (Subalgebra.toSubmodule A) := ‹Flat R A›

instance self (R : Type u) [CommRing R] : Flat R R :=
  ⟨by
    intro I _
    rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
    convert Subtype.coe_injective using 1
    ext x
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, rid_symm_apply, comp_apply, mul_one,
      lift.tmul, Submodule.subtype_apply, Algebra.id.smul_eq_mul, lsmul_apply]⟩

/-- An `R`-module `M` is flat iff for all finitely generated ideals `I` of `R`, the
tensor product of the inclusion `I → R` and the identity `M → M` is injective. See
`iff_rTensor_injective'` to extend to all ideals `I`. --/
lemma iff_rTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (rTensor M I.subtype) := by
  simp [flat_iff, ← lid_comp_rTensor]

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

@[deprecated (since := "2024-03-29")]
alias lTensor_inj_iff_rTensor_inj := LinearMap.lTensor_inj_iff_rTensor_inj

/-- The `lTensor`-variant of `iff_rTensor_injective`. . -/
theorem iff_lTensor_injective :
    Module.Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using Module.Flat.iff_rTensor_injective R M

/-- The `lTensor`-variant of `iff_rTensor_injective'`. . -/
theorem iff_lTensor_injective' :
    Module.Flat R M ↔ ∀ (I : Ideal R), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using Module.Flat.iff_rTensor_injective' R M

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

/-- If an `R`-module `M` is linearly equivalent to another `R`-module `N`, then `M` is flat
  if and only if `N` is flat. -/
lemma equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ => of_linearEquiv R M N e.symm, fun _ => of_linearEquiv R N M e⟩

instance ulift [Module.Flat R M] : Module.Flat R (ULift.{v'} M) :=
  of_linearEquiv R M (ULift.{v'} M) ULift.moduleEquiv

-- Making this an instance causes an infinite sequence `M → ULift M → ULift (ULift M) → ...`.
lemma of_ulift [Module.Flat R (ULift.{v'} M)] : Module.Flat R M :=
  of_linearEquiv R (ULift.{v'} M) M ULift.moduleEquiv.symm

instance shrink [Small.{v'} M] [Module.Flat R M] : Module.Flat R (Shrink.{v'} M) :=
  of_linearEquiv R M (Shrink.{v'} M) (Shrink.linearEquiv M R)

-- Making this an instance causes an infinite sequence `M → Shrink M → Shrink (Shrink M) → ...`.
lemma of_shrink [Small.{v'} M] [Module.Flat R (Shrink.{v'} M)] :
    Module.Flat R M :=
  of_linearEquiv R (Shrink.{v'} M) M (Shrink.linearEquiv M R).symm

/-- A direct sum of flat `R`-modules is flat. -/
instance directSum (ι : Type v) (M : ι → Type w) [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module R (M i)] [F : (i : ι) → (Flat R (M i))] : Flat R (⨁ i, M i) := by
  haveI := Classical.decEq ι
  rw [iff_rTensor_injective]
  intro I hI
  -- This instance was added during PR https://github.com/leanprover-community/mathlib4/pull/10828,
  -- see https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2310828.20-.20generalizing.20CommRing.20to.20CommSemiring.20etc.2E/near/422684923
  letI : ∀ i, AddCommGroup (I ⊗[R] M i) := inferInstance
  rw [← Equiv.comp_injective _ (TensorProduct.lid R (⨁ i, M i)).toEquiv]
  set η₁ := TensorProduct.lid R (⨁ i, M i)
  set η := fun i ↦ TensorProduct.lid R (M i)
  set φ := fun i ↦ rTensor (M i) I.subtype
  set π := fun i ↦ component R ι (fun j ↦ M j) i
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
      directSumRight_symm_lof_tmul, rTensor_tmul, Submodule.coe_subtype, lid_tmul, map_smul]
    rw [DirectSum.component.of, DirectSum.component.of]
    by_cases h₂ : j = i
    · subst j; simp
    · simp [h₂]
  intro a ha; rw [DirectSum.ext_iff R]; intro i
  have f := LinearMap.congr_arg (f := (π i)) ha
  erw [LinearMap.congr_fun (h₁ i) a] at f
  rw [(map_zero (π i) : (π i) 0 = (0 : M i))] at f
  have h₂ := F i
  rw [iff_rTensor_injective] at h₂
  have h₃ := h₂ hI
  simp +zetaDelta only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    EmbeddingLike.map_eq_zero_iff, h₃, LinearMap.map_eq_zero_iff] at f
  simp [f]

open scoped Classical in
/-- Free `R`-modules over discrete types are flat. -/
instance finsupp (ι : Type v) : Flat R (ι →₀ R) :=
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

/--
Define the character module of `M` to be `M →+ ℚ ⧸ ℤ`.
The character module of `M` is an injective module if and only if
 `L ⊗ 𝟙 M` is injective for any linear map `L` in the same universe as `M`.
-/
lemma injective_characterModule_iff_rTensor_preserves_injective_linearMap :
    Module.Injective R (CharacterModule M) ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M) := by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl

variable {R M N}

/-- `CharacterModule M` is Baer iff `M` is flat. -/
theorem iff_characterModule_baer : Flat R M ↔ Module.Baer R (CharacterModule M) := by
  simp_rw [iff_rTensor_injective', Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall]; rfl

/-- `CharacterModule M` is an injective module iff `M` is flat. -/
theorem iff_characterModule_injective [Small.{v} R] :
    Flat R M ↔ Module.Injective R (CharacterModule M) :=
  iff_characterModule_baer.trans Module.Baer.iff_injective

/--
If `M` is a flat module, then `f ⊗ 𝟙 M` is injective for all injective linear maps `f`.
-/
theorem rTensor_preserves_injective_linearMap {N' : Type*} [AddCommGroup N'] [Module R N']
    [h : Flat R M] (L : N →ₗ[R] N') (hL : Function.Injective L) :
    Function.Injective (L.rTensor M) :=
  rTensor_injective_iff_lcomp_surjective.2 ((iff_characterModule_baer.1 h).extension_property _ hL)

@[deprecated (since := "2024-03-29")]
alias preserves_injective_linearMap := rTensor_preserves_injective_linearMap

instance {S} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Flat S M] [Flat R N] :
    Flat S (M ⊗[R] N) :=
  (iff_rTensor_injective' _ _).mpr fun I ↦ by
    simpa [AlgebraTensorModule.rTensor_tensor] using
      rTensor_preserves_injective_linearMap (.restrictScalars R <| rTensor M I.subtype)
      (rTensor_preserves_injective_linearMap _ I.injective_subtype)

example [Flat R M] [Flat R N] : Flat R (M ⊗[R] N) := inferInstance

/--
If `M` is a flat module, then `𝟙 M ⊗ f` is injective for all injective linear maps `f`.
-/
theorem lTensor_preserves_injective_linearMap {N' : Type*} [AddCommGroup N'] [Module R N']
    [Flat R M] (L : N →ₗ[R] N') (hL : Function.Injective L) :
    Function.Injective (L.lTensor M) :=
  (L.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap L hL)

variable (R M) in
/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap` to specialize the universe of
  `N, N', N''` to `Type (max u v)`. -/
lemma iff_rTensor_preserves_injective_linearMap' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) :=
  (Module.Flat.equiv_iff R M (Shrink.{v'} M) (Shrink.linearEquiv M R).symm).trans <|
    iff_characterModule_injective.trans <|
      (injective_characterModule_iff_rTensor_preserves_injective_linearMap R (Shrink.{v'} M)).trans
        <| forall₅_congr <| fun N N' _ _ _ => forall₃_congr <| fun _ f _ =>
  let frmu := f.rTensor (Shrink.{v'} M)
  let frm := f.rTensor M
  let emn := TensorProduct.congr (LinearEquiv.refl R N) (Shrink.linearEquiv M R)
  let emn' := TensorProduct.congr (LinearEquiv.refl R N') (Shrink.linearEquiv M R)
  have h : emn'.toLinearMap.comp frmu = frm.comp emn.toLinearMap := TensorProduct.ext rfl
  (EquivLike.comp_injective frmu emn').symm.trans <|
    (congrArg Function.Injective (congrArg DFunLike.coe h)).to_iff.trans <|
      EquivLike.injective_comp emn frm

variable (R M) in
/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
lemma iff_rTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) :=
  iff_rTensor_preserves_injective_linearMap'.{max u v} R M

variable (R M) in
/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap` to specialize the universe of
  `N, N', N''` to `Type (max u v)`. -/
lemma iff_lTensor_preserves_injective_linearMap' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

variable (R M) in
/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
lemma iff_lTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.lTensor M) :=
  iff_lTensor_preserves_injective_linearMap'.{max u v} R M

variable (M) in
/-- If `M` is flat then `M ⊗ -` is an exact functor. -/
lemma lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.lTensor M) (π.lTensor M) by
    rw [show g = ι.comp π from rfl, lTensor_comp]
    exact exact1.comp_injective _ (lTensor_preserves_injective_linearMap ι <| by
      simpa [ι, - Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.lTensor_exact _ (fun x => by simp [π]) Quotient.mk''_surjective

variable (M) in
/-- If `M` is flat then `- ⊗ M` is an exact functor. -/
lemma rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.rTensor M) (π.rTensor M) by
    rw [show g = ι.comp π from rfl, rTensor_comp]
    exact exact1.comp_injective _ (rTensor_preserves_injective_linearMap ι <| by
      simpa [ι, - Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.rTensor_exact M (fun x => by simp [π]) Quotient.mk''_surjective

/-- `M` is flat if and only if `M ⊗ -` is an exact functor. See
  `Module.Flat.iff_lTensor_exact` to specialize the universe of `N, N', N''` to `Type (max u v)`. -/
theorem iff_lTensor_exact' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) := by
  refine ⟨fun _ => lTensor_exact M, fun H => iff_lTensor_preserves_injective_linearMap' R M |>.mpr
    fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp  hx

/-- `M` is flat if and only if `M ⊗ -` is an exact functor.
  See `Module.Flat.iff_lTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
theorem iff_lTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) :=
  iff_lTensor_exact'.{max u v}

/-- `M` is flat if and only if `- ⊗ M` is an exact functor. See
  `Module.Flat.iff_rTensor_exact` to specialize the universe of `N, N', N''` to `Type (max u v)`. -/
theorem iff_rTensor_exact' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) := by
  refine ⟨fun _ => rTensor_exact M, fun H => iff_rTensor_preserves_injective_linearMap' R M |>.mpr
    fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp hx

/-- `M` is flat if and only if `- ⊗ M` is an exact functor.
  See `Module.Flat.iff_rTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
theorem iff_rTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) :=
  iff_rTensor_exact'.{max u v}

variable (p : Submodule R M) (q : Submodule R N)

/-- If p and q are submodules of M and N respectively, and M and q are flat,
then `p ⊗ q → M ⊗ N` is injective. -/
theorem tensorProduct_mapIncl_injective_of_right
    [Flat R M] [Flat R q] : Function.Injective (mapIncl p q) := by
  rw [mapIncl, ← lTensor_comp_rTensor]
  exact (lTensor_preserves_injective_linearMap _ q.injective_subtype).comp
    (rTensor_preserves_injective_linearMap _ p.injective_subtype)

/-- If p and q are submodules of M and N respectively, and N and p are flat,
then `p ⊗ q → M ⊗ N` is injective. -/
theorem tensorProduct_mapIncl_injective_of_left
    [Flat R p] [Flat R N] : Function.Injective (mapIncl p q) := by
  rw [mapIncl, ← rTensor_comp_lTensor]
  exact (rTensor_preserves_injective_linearMap _ p.injective_subtype).comp
    (lTensor_preserves_injective_linearMap _ q.injective_subtype)

end Flat

end Module

section Injective

variable {R S A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [CommSemiring S] [Algebra S A] [SMulCommClass R S A]

namespace Algebra.TensorProduct

theorem includeLeft_injective [Module.Flat R A] (hb : Function.Injective (algebraMap R B)) :
    Function.Injective (includeLeft : A →ₐ[S] A ⊗[R] B) := by
  convert Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R B) hb
    |>.comp (_root_.TensorProduct.rid R A).symm.injective
  ext; simp

theorem includeRight_injective [Module.Flat R B] (ha : Function.Injective (algebraMap R A)) :
    Function.Injective (includeRight : B →ₐ[R] A ⊗[R] B) := by
  convert Module.Flat.rTensor_preserves_injective_linearMap (M := B) (Algebra.linearMap R A) ha
    |>.comp (_root_.TensorProduct.lid R B).symm.injective
  ext; simp

end Algebra.TensorProduct

end Injective

section Nontrivial

variable (R : Type*) [CommRing R]

namespace TensorProduct

variable (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` to `N`,
and `M` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial. -/
theorem nontrivial_of_linearMap_injective_of_flat_left (f : R →ₗ[R] N) (h : Function.Injective f)
    [Module.Flat R M] [Nontrivial M] : Nontrivial (M ⊗[R] N) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := M) f h |>.comp
    (TensorProduct.rid R M).symm.injective |>.nontrivial

/-- If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` to `M`,
and `N` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial. -/
theorem nontrivial_of_linearMap_injective_of_flat_right (f : R →ₗ[R] M) (h : Function.Injective f)
    [Module.Flat R N] [Nontrivial N] : Nontrivial (M ⊗[R] N) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := N) f h |>.comp
    (TensorProduct.lid R N).symm.injective |>.nontrivial

end TensorProduct

namespace Algebra.TensorProduct

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- If `A`, `B` are `R`-algebras, `R` injects into `B`,
and `A` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial. -/
theorem nontrivial_of_algebraMap_injective_of_flat_left (h : Function.Injective (algebraMap R B))
    [Module.Flat R A] [Nontrivial A] : Nontrivial (A ⊗[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_left R A B (Algebra.linearMap R B) h

/-- If `A`, `B` are `R`-algebras, `R` injects into `A`,
and `B` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial. -/
theorem nontrivial_of_algebraMap_injective_of_flat_right (h : Function.Injective (algebraMap R A))
    [Module.Flat R B] [Nontrivial B] : Nontrivial (A ⊗[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right R A B (Algebra.linearMap R A) h

end Algebra.TensorProduct

end Nontrivial
