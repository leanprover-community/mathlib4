/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.Perfectoid.Untilt
import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Fontaine's θ map
In this file, we define Fontaine's `θ` map, which is a ring
homomorphism from the Witt vector `𝕎(A^♭)` of the tilt of a perfectoid ring `O`
to `O` itself. Our definition of `θ` does not require that `O` is perfectoid in the first place.
We only need `O` to be `p`-adically complete.

## Main definitions
* `fontaineTheta` : Fontaine's θ map, which is a ring homomorphism from `𝕎(O^♭)` to `O`.
* `BDeRhamPlus` : The period ring `B_{dR}^+`.

## Main theorems
* `fontaineTheta_surjective` : Fontaine's θ map is surjective.

## Tags
Fontaine's theta map, period rings, perfectoid theory, p-adic Hodge theory

## TODO
Currently, the period ring `B_{dR}^+` takes the ring of integers `O` as the input.
After the perfectoid theory is developed, we should modify it to
take a perfectoid field as the input.
-/

universe u

open Ideal Quotient PreTilt WittVector

-- an one term proof used in the later statement `quotEquivOfEq_ghostComponentModPPow`.
private lemma Ideal.span_pow_zero_add_one {R : Type*} [CommRing R]
    {I : Ideal R} : I ^ (0 + 1) = I := by
  simp

noncomputable section

variable {O : Type u} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)]

local notation A "^♭" => PreTilt A p
local notation "𝕎" => WittVector p

namespace WittVector

/-!
## θ as a ring homomorphism
In this section, we first define the ring homomorphism
`fontaineThetaModPPow : 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ (n + 1)`.
Then we show they are compatible with each other and lift to a
ring homomorphism `fontaineTheta : 𝕎 (O^♭) →+* O`.

To prove this, we define `fontaineThetaModPPow`
as a composition of the following ring homomorphisms.
`𝕎(O^♭) --𝕎(Frob^-n)->  𝕎(O^♭) --𝕎(coeff 0)-> 𝕎(O/p) --gh_n-> O/p^(n+1)`

Here, the ring map `gh_n` fits in the following diagram.

```
𝕎(A)  --ghost_n->   A
|                   |
v                   v
𝕎(A/p) --gh_n-> A/p^(n+1)
```
-/

theorem ker_map_le_ker_mk_comp_ghostComponent (n : ℕ) :
    RingHom.ker (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)}) ≤
    RingHom.ker (((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp
    (WittVector.ghostComponent (p := p) n)) := by
  intro x
  simp only [RingHom.mem_ker, map_eq_zero_iff, RingHom.comp_apply]
  intro h
  simp only [ghostComponent]
  apply_fun Ideal.quotEquivOfEq (Ideal.span_singleton_pow (p : O) (n + 1))
  simp only [RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply, ghostMap_apply,
    quotEquivOfEq_mk, map_zero]
  simp only [eq_zero_iff_dvd] at h ⊢
  exact pow_dvd_ghostComponent_of_dvd_coeff (fun _ _ ↦ h _)

/--
The lift ring map `gh_n : 𝕎(A/p) →+* A/p^(n+1)` of the `n`-th ghost component
`𝕎(A) →+* A` along the surjective ring map `𝕎(A) →+* 𝕎(A/p)`.
-/
def ghostComponentModPPow (n : ℕ): 𝕎 (O ⧸ span {(p : O)}) →+* O ⧸ span {(p : O)}^(n + 1) :=
  RingHom.liftOfSurjective (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)})
    (map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp
    (WittVector.ghostComponent (p := p) n), ker_map_le_ker_mk_comp_ghostComponent n⟩

@[simp]
theorem quotEquivOfEq_ghostComponentModPPow (x : 𝕎 (O ⧸ span {(p : O)})) :
    quotEquivOfEq (Ideal.span_pow_zero_add_one) (ghostComponentModPPow 0 x) =
    ghostComponent 0 x := by
  simp only [Nat.reduceAdd, ghostComponentModPPow, RingHom.liftOfSurjective]
  have surj : Function.Surjective (WittVector.map (p := p) (Ideal.Quotient.mk (span {(p : O)}))) :=
    map_surjective _ Ideal.Quotient.mk_surjective
  choose y hy using surj x
  have := RingHom.liftOfSurjective_comp_apply
      (WittVector.map (p := p) (Ideal.Quotient.mk (span {(p : O)})))
      surj ⟨((Ideal.Quotient.mk <| span {(p : O)} ^ (0 + 1))).comp
      (WittVector.ghostComponent (p := p) 0), ker_map_le_ker_mk_comp_ghostComponent 0⟩ y
  rw [hy] at this
  rw [this]
  simp [← hy, ghostComponent_apply]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

@[simp]
theorem ghostComponentModPPow_teichmuller_coeff (n : ℕ) (x : O^♭) :
    ghostComponentModPPow n (teichmuller p (Perfection.coeff (ModP O p) _ n x)) =
    Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) x.untilt := by
  simpa [ghostComponentModPPow] using RingHom.liftOfSurjective_comp_apply
      (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)})
      (map_surjective _ Ideal.Quotient.mk_surjective)
      ⟨((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp
      (WittVector.ghostComponent (p := p) n), ker_map_le_ker_mk_comp_ghostComponent n⟩
      (teichmuller p ((((_root_.frobeniusEquiv _ p).symm ^ n) x).untilt))

variable (O p) in
/--
The Fontaine's theta map modulo `p ^ n`.
It is the composition of the following ring homomorphisms.
`𝕎(O^♭) --𝕎(Frob^-n)->  𝕎(O^♭) --𝕎(coeff 0)-> 𝕎(O/p) --gh_n-> O/p^(n+1)`
-/
def fontaineThetaModPPow (n : ℕ): 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ (n + 1) :=
  (ghostComponentModPPow n).comp
      (((WittVector.map (Perfection.coeff _ p 0))).comp
          (WittVector.map ((_root_.frobeniusEquiv (O^♭) p).symm ^ n : O^♭ →+* O^♭)))

@[simp]
theorem fontaineThetaModPPow_teichmuller (n : ℕ) (x : O^♭) :
    fontaineThetaModPPow O p n (teichmuller p x) = Ideal.Quotient.mk _ x.untilt := by
  simp [fontaineThetaModPPow, PreTilt]

theorem factorPowSucc_comp_fontaineThetaModPPow (n : ℕ) :
    (factorPowSucc _ (n + 1)).comp (fontaineThetaModPPow O p (n + 1)) =
    fontaineThetaModPPow O p n:= by
  apply eq_of_apply_teichmuller_eq
      ((factorPowSucc _ (n + 1)).comp (fontaineThetaModPPow O p (n + 1)))
      (fontaineThetaModPPow O p n)
  · use n + 1
    have : (p : (O ⧸ span {(p : O)} ^ (n + 1))) =
        Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) (p : O) := by
      simp only [map_natCast]
    rw [this, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (mem_span_singleton_self _) _
  intro (x : Ring.Perfection (ModP O p) p)
  simp [PreTilt, fontaineThetaModPPow]

theorem factorPowSucc_fontaineThetaModPPow_eq (n : ℕ) (x : 𝕎 (O^♭)) :
    (factorPowSucc _ (n + 1)) ((fontaineThetaModPPow O p (n + 1)) x) =
    fontaineThetaModPPow O p n x:= by
  simp [← factorPowSucc_comp_fontaineThetaModPPow n]

/--
The Fontaine's θ map from `𝕎(O^♭)` to `O`.
It is the limit of the ring maps `fontaineThetaModPPow n` from `𝕎(O^♭)` `O/p^(n+1)`.
-/
def fontaineTheta : 𝕎 (O^♭) →+* O :=
  IsAdicComplete.limRingHom Order.succ_strictMono (factorPowSucc_fontaineThetaModPPow_eq _ _).symm

theorem mk_pow_fontaineTheta (n : ℕ) (x : 𝕎 (O^♭)) :
    Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) (fontaineTheta x) = fontaineThetaModPPow O p n x :=
  IsAdicComplete.mk_limRingHom Order.succ_strictMono
      (factorPowSucc_fontaineThetaModPPow_eq _ _).symm n x

theorem mk_fontaineTheta (x : 𝕎 (O^♭)) :
    Ideal.Quotient.mk (span {(p : O)}) (fontaineTheta x) =
    Perfection.coeff (ModP O p) _ 0 (x.coeff 0) := by
  have := mk_pow_fontaineTheta 0 x
  simp only [Nat.reduceAdd] at this
  apply_fun Ideal.quotEquivOfEq (pow_one (p : O) ▸ Ideal.span_singleton_pow (p : O) 1) at this
  simp only [quotEquivOfEq_mk] at this
  rw [this]
  simp only [fontaineThetaModPPow, Nat.reduceAdd, pow_zero, RingHom.one_def, WittVector.map_id,
    RingHomCompTriple.comp_eq, RingHom.coe_comp, Function.comp_apply,
    quotEquivOfEq_ghostComponentModPPow, ghostComponent_apply, wittPolynomial_zero,
    MvPolynomial.aeval_X]
  -- Note to reviewers : This line was designed to be
  -- `simp [fontaineThetaModPPow, ghostComponent_apply, RingHom.one_def]`
  -- However, `WittVector.map_coeff` should, but does not work here.
  rfl

@[simp]
theorem fontaineTheta_teichmuller (x : O^♭) : fontaineTheta (teichmuller p x) = x.untilt := by
  rw [IsHausdorff.eq_iff_smodEq' (I := span {(p : O)})]
  intro n
  cases n
  · simp
  · simp [SModEq, mk_pow_fontaineTheta]

end WittVector


-- theorem fontaineTheta_p : fontaineTheta (p : 𝕎 (O^♭)) = p := by simp

-- AdicComplete
theorem IsAdicComplete.surjective_of_surjective_mkQ_comp {R M N: Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] (I : Ideal R) [IsAdicComplete I M] [IsHausdorff I N] (f : M →ₗ[R] N)
    (hf : Function.Surjective ((Submodule.mkQ (I • ⊤ : Submodule R N)).comp f)) :
    Function.Surjective f := sorry

-- this is a lemma from #20431 by Andrew Yang
section

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M]

lemma SModEq.of_toAddSubgroup_le {U : Submodule R M} {V : Submodule S M}
    (h : U.toAddSubgroup ≤ V.toAddSubgroup) {x y : M} (hxy : x ≡ y [SMOD U]) : x ≡ y [SMOD V] := by
  simp only [SModEq, Submodule.Quotient.eq] at hxy ⊢
  exact h hxy

-- `Mathlib.Algebra.Module.Submodule.Basic` after `Submodule.toAddSubgroup_mono`
@[simp]
theorem Submodule.toAddSubgroup_toAddSubmonoid {R : Type*}  {M : Type*}  [Ring R]
    [AddCommGroup M] {module_M : Module R M}
    (p : Submodule R M) : p.toAddSubgroup.toAddSubmonoid = p.toAddSubmonoid := by
  ext
  simp

-- -- `Mathlib.Algebra.Group.Submonoid.Pointwise` after `AddSubmonoid.smul_iSup`
-- theorem foo {R S A: Type} [AddMonoid A] [CommSemiring R] [Semiring S] [DistribSMul R A]
-- [DistribSMul S A] [Algebra R S] [IsScalarTower R S A] (hIJ : I.map f ≤ J)
-- (p : AddSubmonoid M) :
-- I.toAddSubmonoid • p ≤ J • p := sorry

-- Note: after #20431 this lemma should be moved to the file `RingTheory.AdicCompletion.Mono`,
-- after `IsHausdorff.mono`
variable [Algebra R S]  [IsScalarTower R S M] (hIJ : I.map (algebraMap R S) ≤ J)

include hIJ in
lemma IsHausdorff.map [IsHausdorff J M] : IsHausdorff I M := by
  refine ⟨fun x h ↦ IsHausdorff.haus ‹_› x fun n ↦ ?_⟩ -- fun n ↦ ((h n).of_toAddSubgroup_le ?_)
  apply SModEq.of_toAddSubgroup_le
      (U := (I ^ n • ⊤ : Submodule R M)) (V := (J ^ n • ⊤ : Submodule S M))
  · -- show (I ^ n • ⊤ : Submodule R M).toAddSubmonoid ≤ (J ^ n • ⊤ : Submodule S M).toAddSubmonoid
    rw [← AddSubgroup.toAddSubmonoid_le]
    simp only [Submodule.toAddSubgroup_toAddSubmonoid, Submodule.smul_toAddSubmonoid,
      Submodule.top_toAddSubmonoid]
    rw [AddSubmonoid.smul_le]
    intro r hr m _
    rw [← algebraMap_smul S r m]
    apply AddSubmonoid.smul_mem_smul
    · have := Ideal.mem_map_of_mem (algebraMap R S) hr
      simp only [Ideal.map_pow] at this
      apply Ideal.pow_right_mono (I :=  I.map (algebraMap R S)) hIJ n this
    · trivial
  · exact h n
end

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem surjective_fontaineTheta : Function.Surjective (fontaineTheta : 𝕎 (O^♭) → O) := by
  let I := span {(p : 𝕎 (O^♭))}
  haveI : IsAdicComplete I (𝕎 (O^♭)) := inferInstance
  letI : Algebra (𝕎 (O^♭)) O := RingHom.toAlgebra fontaineTheta
  haveI : IsHausdorff I O := sorry
  let f : 𝕎 (O^♭) →ₐ[𝕎 (O^♭)] O := Algebra.ofId _ _
  have : ⇑f.toLinearMap = ⇑fontaineTheta := rfl
  -- have : (I • ⊤).mkQ ∘ₗ f.toLinearMap = (I • ⊤).mkQ
  rw [← this]
  apply IsAdicComplete.surjective_of_surjective_mkQ_comp I f.toLinearMap
  intro x
  simp [f, Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]
  sorry




-- lemmas about frobenius and untilt another PR
-- Fontaine's theta and Bdr PR
-- surjective to another PR
