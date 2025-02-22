/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.Perfectoid.Untilt
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Fontaine's θ map
In this file, we define Fontaine's `θ` map, which is a ring
homomorphism from the Witt vector `𝕎(A^♭)` of the tilt of a perfectoid ring `A`
to `A` itself. Our definition of `θ` does not require that `A` is perfectoid in the first place.

## Main definitions
* `fontaineTheta` : Fontaine's θ map, which is a ring homomorphism from `𝕎(A^♭)` to `A`.
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
noncomputable section

variable {O : Type u} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

local notation A "^♭" => PreTilt A p
-- local notation "♯" x => PreTilt.untilt x
local notation "𝕎" => WittVector p

-- /-!
-- ## the underlying function of θ
-- In this section, we define the underlying function of `θ`.

-- * `fontaineThetaAux n` is the sum of the first `n`-terms of the summation used in `θ`.
-- * `fontaineThetaFun` is the p-adic limit of the sequence `fontaineThetaAux`.
-- -/
-- section Function

-- def fontaineThetaAux (x : 𝕎 (O^♭)) (n : ℕ) : O :=
--   ∑ (i ≤ n), p^i * ♯ ((frobeniusEquiv _ p).symm^[n] (x.coeff n))

-- lemma pow_dvd_fontaineThetaAux_sub (x : 𝕎 (O^♭)) {m n : ℕ} (h : m ≤ n) :
--   (p : O) ^ m ∣ fontaineThetaAux x m - fontaineThetaAux x n := by
--   sorry

-- lemma exists_pow_dvd_fontaineThetaAux_sub (x : 𝕎 (O^♭)) :
--     ∃ L, ∀ (n : ℕ), (p : O) ^ n ∣ fontaineThetaAux x n - L :=
--   IsPrecomplete.exists_pow_dvd inferInstance (pow_dvd_fontaineThetaAux_sub x)

-- def fontaineThetaFun (x : 𝕎 (O^♭)) : O :=
--   Classical.choose <| exists_pow_dvd_fontaineThetaAux_sub x

-- lemma pow_dvd_fontaineThetaAux_sub_fontaineThetaFun (x : 𝕎 (O^♭)) (n : ℕ) :
--   (p : O) ^ n ∣ fontaineThetaAux x n - fontaineThetaFun x :=
--   (Classical.choose_spec <| exists_pow_dvd_fontaineThetaAux_sub x) n

-- end Function

/-!
## θ is a ring homomorphism
In this section, we show that `fontaineThetaFun` is actually a
ring homomorphism, and define the ring homomorphism `fontaineTheta`.

To prove this, we prove that `fontaineThetaFun` mod `p^n` is a ring homomorphism by
decompose it as a composition of several ring homomorphisms as below.
`𝕎(O^♭) --𝕎(Frob^-n)->  𝕎(O^♭) --𝕎(coeff 0)-> 𝕎(O/p) --gh_n-> O/p^(n+1)`
Here, the ring map `gh_n` fits in the following diagram.

```
𝕎(A)  --ghost_n->   A
|                   |
v                   v
𝕎(A/p) --gh_n-> A/p^(n+1)
```

-/
section RingHom
#check WittVector.ghostComponent
#check WittVector.map_surjective

namespace WittVector

-- New file Mathlib.RingTheory.WittVector.TeichmullerExpansion
-- import Mathlib.RingTheory.WittVector.Teichmuller
-- import Mathlib.RingTheory.WittVector.Complete


def teichmullerSeries {R : Type*} [CommRing R] [ExpChar R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) : R :=
  ((iterateFrobeniusEquiv R p n).symm (x.coeff n))

theorem teichmullerSeries_def {R : Type*} [CommRing R] [ExpChar R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) :
    teichmullerSeries x n =  ((iterateFrobeniusEquiv R p n).symm  (x.coeff n)) := by
  sorry

/--
The Teichmüller expansion.
-/
theorem dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
    {R : Type*} [CommRing R] [ExpChar R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ (i ≤ n), p ^ i * teichmuller p
        ((iterateFrobeniusEquiv R p n).symm (x.coeff i)) := by
  sorry

theorem eq_of_apply_teichmuller_eq {R S : Type*} [CommRing R] [CommRing S] [ExpChar R p]
    [PerfectRing R p] (f g : 𝕎 R →+* S) (hp : IsNilpotent (p : S))
    (h : ∀ (x : R), f (teichmuller p x) = g (teichmuller p x)) : f = g := by
  obtain ⟨n, hn⟩ := hp
  ext x
  calc
    f x = f (x - ∑ (i ≤ n), p ^ i * teichmuller p ((iterateFrobeniusEquiv R p n).symm (x.coeff i))) +
        f (∑ (i ≤ n), p ^ i * teichmuller p ((iterateFrobeniusEquiv R p n).symm (x.coeff i))) := by
      sorry
    _ = ∑ (i ≤ n), p ^ i * f (teichmuller p ((iterateFrobeniusEquiv R p n).symm  (x.coeff i))) := by sorry
    _ = ∑ (i ≤ n), p ^ i * g (teichmuller p ((iterateFrobeniusEquiv R p n).symm  (x.coeff i))) := by sorry
    _ = g (x - ∑ (i ≤ n), p ^ i * teichmuller p ((iterateFrobeniusEquiv R p n).symm  (x.coeff i))) + g (∑ (i ≤ n), p ^ i * teichmuller p ((iterateFrobeniusEquiv R p n).symm  (x.coeff i))) := by sorry
    _ = g x := by sorry



variable (O p) in
def mkCompGhostComponent (n : ℕ) : 𝕎 O →+* O ⧸ span {(p : O)} ^ (n + 1) :=
  ((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp (WittVector.ghostComponent n)

variable (n : ℕ)
#check mkCompGhostComponent O p n
theorem ker_map_le_ker_mkCompGhostComponent (n : ℕ) :
    RingHom.ker (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)}) ≤
        RingHom.ker (mkCompGhostComponent O p n) := sorry


def ghostComponentModPPow (n : ℕ): 𝕎 (O ⧸ span {(p : O)}) →+* O ⧸ span {(p : O)}^(n + 1) :=
  RingHom.liftOfSurjective (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)})
    (map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨mkCompGhostComponent O p n, ker_map_le_ker_mkCompGhostComponent n⟩

#check PreTilt.mk_untilt_eq_coeff_zero
#check RingHom.liftOfRightInverse_comp_apply
@[simp]
theorem ghostComponentModPPow_teichmuller_coeff (n : ℕ) (x : O^♭) :
    ghostComponentModPPow n (teichmuller p (Perfection.coeff (ModP O p) _ n x)) =
    Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) x.untilt := sorry


-- Quotient.lift
#check RingHom.liftOfSurjective
#check WittVector.map

end WittVector

variable (O p) in
def fontaineThetaModPPow (n : ℕ): 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ (n + 1) :=
  (ghostComponentModPPow n).comp
      (((WittVector.map (Perfection.coeff _ p 0))).comp
          (WittVector.map ((frobeniusEquiv (O^♭) p).symm ^ n : O^♭ →+* O^♭)))

-- theorem fontaineThetaModP_eq_fontainThetaFun_mod_p (x : 𝕎 (O^♭)) (n : ℕ) :
--   fontaineThetaModPPow O p n x =
--   Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) (fontaineThetaAux x n) := sorry

-- variable (R S : Type*) [CommRing R] [CommRing S] [Unique S]
-- #check R ⧸ (⊤ : Ideal R)
-- #synth Unique (R ⧸ (⊤ : Ideal R))
-- #synth Inhabited (R → S)
-- #synth Subsingleton S
-- #synth Unique (R → S)
-- #synth Unique (R →+ S)
-- #synth Subsingleton (R →+ S)

-- -- Where to put this?
-- instance (I : Ideal R) : Subsingleton (R ⧸ I ^ 0) :=
--   Ideal.Quotient.subsingleton_iff.mpr (Ideal.one_eq_top (R := R) ▸ pow_zero I)

-- def RingHom.zero (R S : Type*) [CommRing R] [CommRing S] [Subsingleton S] :
--   R →+* S where
--     toFun _ := 0
--     map_one' := Subsingleton.allEq _ _
--     map_mul' _ _ := Subsingleton.allEq _ _
--     map_zero' := Subsingleton.allEq _ _
--     map_add' _ _ := Subsingleton.allEq _ _

-- #check Ideal.Quotient.factorPowSucc
-- instance
-- variable (R : Type*) [CommRing R] (I : Ideal R)
-- #synth Subsingleton (R ⧸ I ^ 0)

-- private def fontaineThetaModPPow' (n : ℕ): 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ n :=
--   if h : n = 0
--   then h ▸ RingHom.zero _ _
--   else Nat.sub_add_cancel (sorry  : 1 ≤ n) ▸ fontaineThetaModPPow O p (n - 1)

--
#check  eq_of_apply_teichmuller_eq
#check WittVector.map_teichmuller
#check WittVector.ghostComponent_teichmuller

-- `Mathlib.FieldTheory.Perfect` after `iterateFrobeniusEquiv_symm`

/--
The `(frobeniusEquiv R p).symm` version of `MonoidHom.map_frobenius`
-/
theorem MonoidHom.map_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    (f : R →* S) (p : ℕ) [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := sorry

theorem RingHom.map_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    (f : R →+* S) (p : ℕ) [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := sorry

theorem MonoidHom.map_frobeniusEquiv_symm_pow {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S]
    (f : R →* S) (p : ℕ) [ExpChar R p]
    [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm ^[n]) x) = ((frobeniusEquiv S p).symm ^[n]) (f x) := sorry

theorem RingHom.map_frobeniusEquiv_symm_pow {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S]
    (f : R →+* S) (p : ℕ) [ExpChar R p]
    [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm ^[n]) x) = ((frobeniusEquiv S p).symm ^[n]) (f x) := sorry

-- `Mathlib.RingTheory.Perfection` after `Perfection.coeff_iterate_frobenius'`
@[simp]
theorem Perfection.coeff_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {p : ℕ}
    [hp : Fact (Nat.Prime p)] [CharP R p] (f : Ring.Perfection R p) (n : ℕ) :
    (Perfection.coeff R p n) ((frobeniusEquiv (Ring.Perfection R p) p).symm f) =
    (Perfection.coeff R p (n + 1)) f := by sorry

@[simp]
theorem Perfection.coeff_iterate_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {p : ℕ}
    [hp : Fact (Nat.Prime p)] [CharP R p] (f : Ring.Perfection R p) (n m : ℕ) :
    (Perfection.coeff _ p n) ((frobeniusEquiv _ p).symm ^[m] f) =
    (Perfection.coeff _ p (n + m)) f := by sorry

theorem factorPowSucc_comp_fontaineThetaModPPow (n : ℕ) :
    (factorPowSucc _ (n + 1)).comp (fontaineThetaModPPow O p (n + 1)) =
    fontaineThetaModPPow O p n:= by
  apply eq_of_apply_teichmuller_eq
      ((factorPowSucc _ (n + 1)).comp (fontaineThetaModPPow O p (n + 1)))
      (fontaineThetaModPPow O p n)
  · use n + 1
    have : (p : (O ⧸ span {(p : O)} ^ (n + 1))) = mk (span {(p : O)} ^ (n + 1)) (p : O) := by
      simp only [map_natCast]
    rw [this, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (mem_span_singleton_self _) _
  intro (x : Ring.Perfection (ModP O p) p)
  simp only [PreTilt, fontaineThetaModPPow, RingHom.coe_comp, Function.comp_apply, map_teichmuller,
    RingHom.coe_pow, RingHom.coe_coe, Function.iterate_succ]
  erw [Perfection.coeff_iterate_frobeniusEquiv_symm, Perfection.coeff_iterate_frobeniusEquiv_symm]
  -- note to reviewers: I don't know why `simp` or `rw` doesn't work here.
  simp

theorem factorPowSucc_fontaineThetaModPPow_eq (n : ℕ) (x : 𝕎 (O^♭)) :
    (factorPowSucc _ (n + 1)).comp (fontaineThetaModPPow O p (n + 1)) x =
    fontaineThetaModPPow O p n x:= by
  rw [← factorPowSucc_comp_fontaineThetaModPPow n]

#check IsAdicComplete.limRingHom
#synth IsAdicComplete (span {(p : 𝕎 (O^♭))}) (𝕎 (O^♭))

#check fontaineThetaModPPow

def fontaineTheta : 𝕎 (O^♭) →+* O := by
  apply IsAdicComplete.limRingHom (a := fun n ↦ n + 1) (S := 𝕎 (O^♭)) (R := O) (I := span {(p : O)})
  · exact (factorPowSucc_fontaineThetaModPPow_eq _ _).symm
  · exact Order.succ_strictMono
  -- · exact fun n ↦ fontaineThetaModPPow O p n
    -- (fun x => (factorPowSucc_fontaineThetaModPPow_eq x).symm)

-- theorem fontaineTheta :
end RingHom

-- theorem modPPow

-- Teichmuller lifts

theorem fontaineTheta_teichmuller (x : O^♭) : fontaineTheta (teichmuller p x) = x.untilt := sorry

theorem surjective_fontaineTheta : Function.Surjective (fontaineTheta : 𝕎 (O^♭) → O) := sorry


section PeriodRing

def BDeRhamPlus : Type u := AdicCompletion (RingHom.ker fontaineTheta) (𝕎 (O^♭)) -- WRONG need invert p

def BDeRham (O : Type*) [CommRing O] [Fact (Nat.Prime p)]
  [Fact ¬IsUnit (p : O)] : Type* := sorry -- FractionRing (BDeRhamPlus O p)
notation "𝔹_dR^+(" O ")" => BDeRhamPlus O

end PeriodRing

end
