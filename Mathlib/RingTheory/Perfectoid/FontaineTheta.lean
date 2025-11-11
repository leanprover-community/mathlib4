/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.RingHom
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

## Main Theorems
* `fontaineTheta_teichmuller` : `θ([x])` is the untilt of `x`.
* `fontaineTheta_surjective` : Fontaine's θ map is surjective.

## Tags
Fontaine's theta map, perfectoid theory, p-adic Hodge theory
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
def ghostComponentModPPow (n : ℕ) : 𝕎 (O ⧸ span {(p : O)}) →+* O ⧸ span {(p : O)}^(n + 1) :=
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
The Fontaine's theta map modulo `p^(n+1)`.
It is the composition of the following ring homomorphisms.
`𝕎(O^♭) --𝕎(Frob^-n)->  𝕎(O^♭) --𝕎(coeff 0)-> 𝕎(O/p) --gh_n-> O/p^(n+1)`
-/
def fontaineThetaModPPow (n : ℕ) : 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ (n + 1) :=
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

open IsAdicComplete

variable (O p) in
/--
The Fontaine's θ map from `𝕎(O^♭)` to `O`.
It is the limit of the ring maps `fontaineThetaModPPow n` from `𝕎(O^♭)` `O/p^(n+1)`.
-/
def fontaineTheta : 𝕎 (O^♭) →+* O :=
  Order.succ_strictMono.liftRingHom (span {(p : O)}) _ (factorPowSucc_comp_fontaineThetaModPPow _)

theorem mk_pow_fontaineTheta (n : ℕ) (x : 𝕎 (O^♭)) :
    Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) (fontaineTheta O p x) =
    fontaineThetaModPPow O p n x :=
  Order.succ_strictMono.mk_liftRingHom (span {(p : O)}) _
      (factorPowSucc_comp_fontaineThetaModPPow _) x

theorem mk_fontaineTheta (x : 𝕎 (O^♭)) :
    Ideal.Quotient.mk (span {(p : O)}) (fontaineTheta O p x) =
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
theorem fontaineTheta_teichmuller (x : O^♭) : fontaineTheta O p (teichmuller p x) = x.untilt := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : O)})]
  simp only [smul_eq_mul, mul_top]
  intro n
  cases n
  · simp
  · simp [SModEq, mk_pow_fontaineTheta]

end WittVector

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem surjective_fontaineTheta (hF : Function.Surjective (frobenius (ModP O p) p)) :
    Function.Surjective (fontaineTheta O p) := by
  have : Ideal.map (fontaineTheta O p) (span {(p : 𝕎 (O^♭))}) = span {(p : O)} := by
    simp [map_span]
  have _ : IsHausdorff ((span {(p : 𝕎 (O^♭))}).map (fontaineTheta O p)) O := by
    rw [this]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (fontaineTheta O p) (I := span {(p : 𝕎 (O^♭))})
  simp only [RingHom.coe_comp]
  suffices h : Function.Surjective (Ideal.Quotient.mk (span {(p : O)}) ∘
      (fontaineTheta O p)) by
    convert h
  have : (Ideal.Quotient.mk (span {(p : O)})) ∘ (fontaineTheta O p) = (fun x ↦
      Perfection.coeff (ModP O p) _ 0 x) ∘ fun (x : 𝕎 (O^♭)) ↦ (x.coeff 0) := by
    ext
    simp [mk_fontaineTheta]
  rw [this]
  apply Function.Surjective.comp
  · exact Perfection.coeff_surjective hF 0
  · exact WittVector.coeff_surjective 0
