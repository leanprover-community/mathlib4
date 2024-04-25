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
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

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
* `Module.Flat.preserves_injective_linearMap`: If `M` is a flat module then tensoring with `M`
  preserves injectivity of linear maps. This lemma is fully universally polymorphic in all
  arguments, i.e. `R`, `M` and linear maps `N → N'` can all have different universe levels.
* `Module.Flat.iff_rTensor_preserves_injective_linearMap`: a module is flat iff tensoring preserves
  injectivity in the ring's universe (or higher).

## Implementation notes
In `Module.Flat.iff_rTensor_preserves_injective_linearMap`, we require that the universe level of
the ring is lower than or equal to that of the module. This requirement is to make sure ideals of
the ring can be lifted to the universe of the module. It is unclear if this lemma also holds
when the module lives in a lower universe.

## TODO

* Show that flatness is stable under base change (aka extension of scalars)
  Using the `IsBaseChange` predicate should allow us to treat both
  `A[X]` and `A ⊗ R[X]` as the base change of `R[X]` to `A`.
  (Similar examples exist with `Fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.

-/


universe u v w

namespace Module

open Function (Surjective)

open LinearMap Submodule TensorProduct DirectSum

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
@[mk_iff] class Flat : Prop where
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

@[deprecated]
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
      directSumRight_symm_lof_tmul, rTensor_tmul, Submodule.coeSubtype, lid_tmul, map_smul]
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
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, AddEquivClass.map_eq_zero_iff,
    h₃, LinearMap.map_eq_zero_iff] at f
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

@[deprecated]
alias preserves_injective_linearMap := rTensor_preserves_injective_linearMap

/--
If `M` is a flat module, then `𝟙 M ⊗ f` is injective for all injective linear maps `f`.
-/
theorem lTensor_preserves_injective_linearMap {N' : Type*} [AddCommGroup N'] [Module R N']
    [Flat R M] (L : N →ₗ[R] N') (hL : Function.Injective L) :
    Function.Injective (L.lTensor M) :=
  (L.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap L hL)

variable (R M) in
/--
M is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
-/
lemma iff_rTensor_preserves_injective_linearMap [Small.{v} R] :
    Flat R M ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M) := by
  rw [iff_characterModule_injective,
    injective_characterModule_iff_rTensor_preserves_injective_linearMap]

variable (R M) in
/--
M is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
-/
lemma iff_lTensor_preserves_injective_linearMap [Small.{v} R] :
    Flat R M ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap, LinearMap.lTensor_inj_iff_rTensor_inj]

variable (R M) in
lemma lTensor_exact [Small.{v} R] [flat : Flat R M] ⦃N N' N'' : Type v⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
    [Module R N] [Module R N'] [Module R N'']
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'')
    (exact : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f :=
  { toFun := Submodule.Quotient.mk
    map_add' := by simp
    map_smul' := by simp }
  have exact0 : Function.Exact f π := by
    intro x; simp [π]
  have surj0 : Function.Surjective π := Quotient.surjective_Quotient_mk''

  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (Function.LinearMap.exact_iff.mp exact).symm
  have inj0 : Function.Injective ι := by
    simpa [ι] using Subtype.val_injective
  have eq0 : g = ι.comp π := by aesop

  suffices exact1 : Function.Exact (f.lTensor M) (π.lTensor M) by
    rw [eq0, lTensor_comp]
    apply Function.Exact.comp_injective (exact := exact1)
      (inj := iff_lTensor_preserves_injective_linearMap R M |>.mp flat _ inj0)
      (h0 := map_zero _)

  exact _root_.lTensor_exact _ exact0 surj0

variable (R M) in
lemma rTensor_exact [Small.{v} R] [flat : Flat R M] ⦃N N' N'' : Type v⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
    [Module R N] [Module R N'] [Module R N'']
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'')
    (exact : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f :=
  { toFun := Submodule.Quotient.mk
    map_add' := by simp
    map_smul' := by simp }
  have exact0 : Function.Exact f π := by
    intro x; simp [π]
  have surj0 : Function.Surjective π := Quotient.surjective_Quotient_mk''

  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (Function.LinearMap.exact_iff.mp exact).symm
  have inj0 : Function.Injective ι := by
    simpa [ι] using Subtype.val_injective
  have eq0 : g = ι.comp π := by aesop

  suffices exact1 : Function.Exact (f.rTensor M) (π.rTensor M) by
    rw [eq0, rTensor_comp]
    apply Function.Exact.comp_injective (exact := exact1)
      (inj := iff_rTensor_preserves_injective_linearMap R M |>.mp flat _ inj0)
      (h0 := map_zero _)

  exact _root_.rTensor_exact _ exact0 surj0

variable (R M) in
lemma iff_lTensor_exact [Small.{v} R] :
    Flat R M ↔
    ∀ ⦃N N' N'' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N'']
      (f : N →ₗ[R] N') (g : N' →ₗ[R] N''), Function.Exact f g →
      Function.Exact (f.lTensor M) (g.lTensor M) := by
  refine ⟨fun _ => lTensor_exact R M, fun H => iff_lTensor_preserves_injective_linearMap R M |>.mpr
    fun N' N'' _ _ _ _ L hL => ?_⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro x (hx : _ = 0)
  simpa [Eq.comm] using
    @H PUnit N' N'' _ _ _ _ _ _ 0 L (by intro x; simpa [hL] using Eq.comm) x |>.mp hx

variable (R M) in
lemma iff_rTensor_exact [Small.{v} R] :
    Flat R M ↔
    ∀ ⦃N N' N'' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N'']
      (f : N →ₗ[R] N') (g : N' →ₗ[R] N''), Function.Exact f g →
      Function.Exact (f.rTensor M) (g.rTensor M) := by
  refine ⟨fun _ => rTensor_exact R M, fun H => iff_rTensor_preserves_injective_linearMap R M |>.mpr
    fun N' N'' _ _ _ _ L hL => ?_⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro x (hx : _ = 0)
  simpa [Eq.comm] using
    @H PUnit N' N'' _ _ _ _ _ _ 0 L (by intro x; simpa [hL] using Eq.comm) x |>.mp hx

noncomputable section categorical_characterisations

open CategoryTheory MonoidalCategory ModuleCat

variable (M : ModuleCat.{u} R)

open scoped MonoidalCategory in
set_option maxHeartbeats 400000 in
-- In two goals, we need to use `simpa` in one; and `simp` in the other.
set_option linter.unnecessarySimpa false in
instance [flat : Flat R M] {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    Limits.PreservesLimit (Limits.parallelPair f 0) (tensorLeft M) where
  preserves {c} hc := by
    let ι : c.pt ⟶ X := c.π.app .zero
    have mono0 : Mono ι := by
      constructor
      intro Z g h H
      let c' : Limits.Cone (Limits.parallelPair f 0) :=
        ⟨Z, ⟨fun x => match x with
        | .zero => h ≫ ι
        | .one => 0,
        fun _ _ l => match l with
          | .left => by simp [ι]
          | .right => by simp [ι]
          | .id x => by simp⟩⟩
      rw [hc.uniq c' g fun x => match x with
        | .zero => by simpa [ι] using H
        | .one => by simp, hc.uniq c' h fun x => match x with
        | .zero => by simp [ι]
        | .one => by simp]
    have exact0 : Exact ι f := by
      refine Abelian.exact_of_is_kernel (w := by simp [ι]) (h := ?_)
      refine Limits.IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _
        ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ hc
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp [ι]
      · exact 𝟙 c.pt
      · rintro (⟨⟩|⟨⟩) <;> simp [ι]
      · rfl
      · rfl

    let f' := M ◁ f; let ι' := M ◁ ι

    have exact1 : Exact ι' f' := by
      rw [exact_iff, Eq.comm, ← Function.LinearMap.exact_iff] at exact0 ⊢
      exact lTensor_exact R M ι f exact0
    have mono1 : Mono ι' := by
      rw [ModuleCat.mono_iff_injective] at mono0 ⊢
      letI : Flat R (of R M) := inferInstanceAs <| Flat R M
      exact lTensor_preserves_injective_linearMap _ mono0
    letI ic1 := Abelian.isLimitOfExactOfMono ι' f' exact1

    refine Limits.IsLimit.equivOfNatIsoOfIso ⟨⟨fun x => match x with
      | .zero => 𝟙 _
      | .one => 𝟙 _, ?_⟩, ⟨fun x => match x with
      | .zero => 𝟙 _
      | .one => 𝟙 _, ?_⟩, ?_, ?_⟩ _ _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ ic1
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · rintro _ _ (⟨⟩ | ⟨⟩ | ⟨_⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · ext (⟨⟩|⟨⟩) <;> simp
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simpa [ι', ι, f', Eq.comm] using exact1.w
    · exact 𝟙 _
    · rintro (⟨⟩ | ⟨⟩) <;> simpa [ι', ι, f', Eq.comm] using exact1.w
    · ext (⟨⟩ | ⟨⟩); simp [ι', ι, f']
    · ext (⟨⟩ | ⟨⟩); simp [ι', ι, f']

instance tensorLeft_preservesFiniteLimits [Flat R M] :
    Limits.PreservesFiniteLimits (tensorLeft M) :=
  (tensorLeft M).preservesFiniteLimitsOfPreservesKernels

open scoped MonoidalCategory in
instance tensorRight_preservesFiniteLimits [Flat R M] :
    Limits.PreservesFiniteLimits (tensorRight M) where
  preservesFiniteLimits J _ _ :=
  { preservesLimit := fun {K} => by
      letI : Limits.PreservesLimit K (tensorLeft M) := inferInstance
      apply Limits.preservesLimitOfNatIso (F := tensorLeft M)
      exact ⟨⟨fun X => β_ _ _ |>.hom, by aesop_cat⟩, ⟨fun X => β_ _ _ |>.inv, by aesop_cat⟩,
        by aesop_cat, by aesop_cat⟩ }

lemma iff_tensorLeft_preservesFiniteLimits :
    Flat R M ↔
    Nonempty (Limits.PreservesFiniteLimits (tensorLeft M)) := by
  refine ⟨fun _ => ⟨inferInstance⟩, ?_⟩
  rintro ⟨_⟩
  rw [iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ L hL
  haveI : Mono (ofHom L) := by rwa [ModuleCat.mono_iff_injective]
  have inj : Mono <| (tensorLeft M).map (ofHom L) :=
    preserves_mono_of_preservesLimit (tensorLeft M) (ofHom L)
  rwa [ModuleCat.mono_iff_injective] at inj

lemma iff_tensorRight_preservesFiniteLimits :
    Flat R M ↔
    Nonempty (Limits.PreservesFiniteLimits (tensorRight M)) := by
  refine ⟨fun _ => ⟨inferInstance⟩, ?_⟩
  rintro ⟨_⟩
  rw [iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ L hL
  haveI : Mono (ofHom L) := by rwa [ModuleCat.mono_iff_injective]
  have inj : Mono <| (tensorRight M).map (ofHom L) :=
    preserves_mono_of_preservesLimit (tensorRight M) (ofHom L)
  rwa [ModuleCat.mono_iff_injective] at inj

namespace tor_related_constructions

open Classical
open ShortComplex HomologicalComplex

variable (M) in
/-- For any `R`-module `M`, we associated with a free module `⨁ (_ : M), R` -/
private def _root_.ModuleCat.free : ModuleCat.{u} R := of R <| ⨁ (_ : M), R

instance : Free R M.free := Module.Free.dfinsupp _ _

instance [Module.Free R M] : Projective R M :=
  Module.Projective.of_free

instance [Module.Free R M] : CategoryTheory.Projective M where
  factors {E X} f e _ :=
    projective_lifting_property e f (by rwa [← ModuleCat.epi_iff_surjective])

/-- `⨁ (m : M), R ⟶ M` defined by `(_ · m)` at `m`-th coordinate -/
private def _root_.ModuleCat.fromFree : M.free ⟶ M :=
DirectSum.toModule _ _ _ fun i => LinearMap.lsmul R M |>.flip i

lemma surjective_fromFree : Surjective M.fromFree := by
  intro x
  use DirectSum.of _ x 1
  erw [toModule_lof, LinearMap.lsmul_apply, one_smul]

instance : Epi M.fromFree := by
  rw [ModuleCat.epi_iff_surjective]; apply surjective_fromFree

variable (R) in
structure ARROW :=
  prev : ModuleCat.{u} R
  next : ModuleCat.{u} R
  free_prev : Free R prev
  free_next : Free R next
  hom : next ⟶ prev

attribute [instance] ARROW.free_prev ARROW.free_next

open Limits
def complexAux :
    ℕ → ARROW R :=
  Nat.rec
    ⟨M.free, kernel M.fromFree |>.free,
      inferInstance, inferInstance,
      ModuleCat.fromFree _ ≫ kernel.ι _⟩
    fun _ P =>
      ⟨P.next, kernel P.hom |>.free,
        inferInstance, inferInstance,
        ModuleCat.fromFree _ ≫ kernel.ι _⟩


lemma complexAux_exact (n : ℕ) : Exact (complexAux M (n + 1)).hom (complexAux M n).hom := by
  change Exact (_ ≫ _) _
  apply exact_epi_comp (hgh := exact_kernel_ι)

def complex : ChainComplex (ModuleCat.{u} R) ℕ where
  X n := complexAux M n |>.prev
  d i j :=
    if h : j + 1 = i
    then eqToHom (by subst (h : j.succ = i); simp [complexAux]) ≫ (complexAux M _).hom
    else 0
  d_comp_d' := by rintro _ _ i ⟨rfl⟩ ⟨rfl⟩; simp [complexAux]

instance (n : ℕ) : Free R <| (complex M).X n := by
  dsimp [complex]
  infer_instance

instance (n : ℕ) : HomologicalComplex.HasHomology (complex M) n := by
  dsimp [complex]
  infer_instance

lemma complex_exact (n : ℕ) : Exact ((complex M).d (n + 2) (n + 1)) ((complex M).d (n + 1) n) := by
  simpa [complex] using complexAux_exact M n

abbrev π : complex M ⟶ (ChainComplex.single₀ _).obj M :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨M.fromFree, by simp [complex, complexAux]⟩

instance : QuasiIsoAt (π M) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros'] <;> try rfl
  simpa only [complex, complexAux, shortComplexFunctor'_obj_X₁, Nat.rec_add_one, Nat.rec_zero,
    shortComplexFunctor'_obj_X₂, ChainComplex.single₀_obj_zero, shortComplexFunctor'_obj_f,
    zero_add, ↓reduceDite, eqToHom_refl, Category.id_comp, shortComplexFunctor'_map_τ₂,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero] using
    ⟨exact_iff_shortComplex_exact _ |>.mp <| CategoryTheory.exact_epi_comp
      (hgh := exact_kernel_ι), inferInstance⟩

open scoped ZeroObject in
instance (n : ℕ) : QuasiIsoAt (π M) (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have z1 : IsZero <| ((ChainComplex.single₀ (ModuleCat R)).obj M).homology (n + 1) := by
    apply isZero_single_obj_homology
    simp

  have z2 : IsZero <| HomologicalComplex.homology (complex M) (n + 1) := by
    suffices e : HomologicalComplex.homology (complex M) (n + 1) ≅ 0 from
      e.isZero_iff.mpr (isZero_zero _)

    refine exact_iff_homology_iso_zero _ |>.mp ?_ |>.some
    rw [← exact_iff_shortComplex_exact]
    simp only [complex, shortComplexFunctor_obj_X₁, shortComplexFunctor_obj_X₂,
      shortComplexFunctor_obj_X₃, shortComplexFunctor_obj_f, ChainComplex.prev, ↓reduceDite,
      shortComplexFunctor_obj_g, ChainComplex.next_nat_succ, exact_iso_comp]
    set g := _; change Exact _ g
    suffices g = (complexAux M n).hom ≫ eqToHom (by simp [complex]) by
      rw [this, exact_comp_iso]
      apply complexAux_exact M n
    simp [g]


  suffices HomologicalComplex.homologyMap (π M) (n + 1) = (z2.iso z1).hom by
    rw [this]
    exact IsIso.of_iso _
  exact IsZero.eq_of_tgt z1 _ _

instance : _root_.QuasiIso (π M) where
  quasiIsoAt n := by
    cases n <;> infer_instance

def _root_.ModuleCat.freeResolution : ProjectiveResolution M where
  complex := complex M
  π := π M

instance : HasProjectiveResolutions (ModuleCat.{u} R) where
  out M := ⟨⟨M.freeResolution⟩⟩


def _root_.Ideal.shortComplex (I : Ideal R) : ShortComplex (ModuleCat.{u} R) where
  X₁ := of R I
  X₂ := of R R
  X₃ := of R (R ⧸ I)
  f := ofHom I.subtype
  g := ofHom <| Algebra.linearMap _ _
  zero := by
    ext x
    simp only [ModuleCat.coe_comp, Function.comp_apply, ofHom_apply, Submodule.coeSubtype,
      Algebra.linearMap_apply, Ideal.Quotient.algebraMap_eq]
    change Ideal.Quotient.mk I x.1 = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact x.2


end tor_related_constructions

open scoped ZeroObject

open tor_related_constructions in
def higherTorIsoZero [flat : Flat R M] (n : ℕ) (N : ModuleCat.{u} R) :
    ((Tor' _ (n + 1)).obj N).obj M ≅ 0 := by
  dsimp [Tor', Functor.flip]
  refine' N.freeResolution.isoLeftDerivedObj (tensorRight M) (n + 1) ≪≫ ?_
  refine Limits.IsZero.isoZero ?_
  dsimp only [HomologicalComplex.homologyFunctor_obj]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  dsimp [HomologicalComplex.ExactAt]
  rw [← exact_iff_shortComplex_exact]
  dsimp
  rw [ModuleCat.exact_iff, Eq.comm, ← Function.LinearMap.exact_iff]
  rw [iff_rTensor_exact] at flat
  refine flat _ _ ?_
  rw [Function.LinearMap.exact_iff, Eq.comm, ← ModuleCat.exact_iff]
  simp [ModuleCat.freeResolution]
  convert complex_exact N n using 1
  · congr! 1; simp only [ChainComplex.prev]; rfl
  · congr! 1; simp
  · congr! 1; simp only [ChainComplex.prev]; rfl
  · congr! 1; simp

def firstTorIsoZero [Flat R M] (N : ModuleCat.{u} R) :
    ((Tor' _ 1).obj N).obj M ≅ 0 :=
  higherTorIsoZero M 0 N

def firstTorOfIdealIsoZero [Flat R M] (I : Ideal R) :
    ((Tor' _ 1).obj (ModuleCat.of R I)).obj M ≅ 0 :=
  firstTorIsoZero M (ModuleCat.of R I)

end categorical_characterisations

end Flat

end Module
