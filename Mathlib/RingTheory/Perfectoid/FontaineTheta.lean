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
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra


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
noncomputable section

variable {O : Type u} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

local notation A "^♭" => PreTilt A p
local notation "𝕎" => WittVector p

/-!
## θ as a ring homomorphism
In this section, we first define the ring homomorphism
`fontaineThetaModPPow : 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ (n + 1)`.
Then we show they are compatible with each other and lift to a
ring homomorphism `fontaineTheta : 𝕎 (O^♭) →+* O`.

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


-- def teichmullerSeries {R : Type*} [CommRing R]
-- [ExpChar R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) : R :=
--   (((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n))

-- theorem teichmullerSeries_def {R : Type*} [CommRing R]
-- [ExpChar R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) :
--     teichmullerSeries x n =  (((_root_.frobeniusEquiv R p).symm ^ n)  (x.coeff n)) := by
--   sorry
#check WittVector.coeff_add_of_disjoint

#check Finset.sum_insert_of_eq_zero_if_not_mem
#check Finset.sum_insert
-- local lemma
theorem coeff_sum_of_disjoint {R : Type*} [CommRing R]
    {α : Type*} {S : Finset α} (x : α → 𝕎 R)
    (h : ∀ (n : ℕ), Subsingleton {r | r ∈ S ∧ (x r).coeff n ≠ 0}) (n : ℕ) :
    (∑ s ∈ S, x s).coeff n = ∑ (s ∈ S), (x s).coeff n := by
  classical
  revert n
  induction' S using Finset.induction with a S' ha hind
  · simp
  · intro n
    have : (∀ (n : ℕ), Subsingleton {r | r ∈ S' ∧ (x r).coeff n ≠ 0 }) := by
      refine fun n ↦ ⟨fun b c ↦ ?_⟩
      ext
      exact congrArg (fun x ↦ x.1) <|
          (h n).allEq ⟨b.1, S'.subset_insert a b.2.1, b.2.2⟩ ⟨c.1, S'.subset_insert a c.2.1, c.2.2⟩
    replace hind := hind this
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    have : ∀ (n : ℕ), (x a).coeff n = 0 ∨ (∑ s ∈ S', x s).coeff n = 0 := by
      simp only [hind]
      by_contra! h
      obtain ⟨m, hma, hmS'⟩ := h
      have := Finset.sum_eq_zero.mt hmS'
      push_neg at this
      choose b hb hb' using this
      have : a = b :=
        congrArg (fun x ↦ x.1) <|
          (h m).allEq ⟨a, S'.mem_insert_self a, hma⟩ ⟨b, S'.mem_insert_of_mem hb, hb'⟩
      exact ha (this ▸ hb)
    rw [coeff_add_of_disjoint n _ _ this, hind n]


#check WittVector.mul_pow_charP_coeff_succ
#check WittVector.mul_pow_charP_coeff_zero
-- -- local lemma
@[simp]
theorem teichmuller_mul_pow_coeff {R : Type*} [CommRing R] [CharP R p] (n : ℕ) (x : R) :
    (teichmuller p x * p ^ n).coeff n = x ^ p ^ n := by
  simpa using WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (m := 0)

theorem teichmuller_mul_pow_coeff_of_ne {R : Type*} [CommRing R] [CharP R p] (x : R)
    {m n : ℕ} (h : m ≠ n) : (teichmuller p x * p ^ n).coeff m = 0 := by
  cases Nat.lt_or_lt_of_ne h with
  | inl h =>
     exact WittVector.mul_pow_charP_coeff_zero (teichmuller p x) h
  | inr h =>
    have : m = (m - n) + n := by rw [Nat.sub_add_cancel h.le]
    rw [this, WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (n := n),
        WittVector.teichmuller_coeff_pos p x (m - n) (Nat.zero_lt_sub_of_lt h), zero_pow]
    simp [Prime.ne_zero <| Nat.Prime.prime Fact.out]

-- `Mathlib.Algebra.Ring.Aut` after `toPerm`
theorem RingAut.one_eq_refl (R : Type*) [Mul R] [Add R] : (1 : R ≃+* R) = RingEquiv.refl R := rfl

@[simp]
theorem RingAut.one_apply (R : Type*) [Mul R] [Add R] (x : R) : (1 : R ≃+* R) x = x := rfl

@[simp]
theorem RingAut.coe_one (R : Type*) [Mul R] [Add R] : ⇑(1 : R ≃+* R) = id := rfl

@[simp]
theorem RingAut.mul_apply (R : Type*) [Mul R] [Add R]
    (f g : R ≃+* R) (x : R) : (f * g) x = f (g x) := rfl

@[simp]
theorem RingAut.inv_apply (R : Type*) [Mul R] [Add R]
    (f : R ≃+* R) (x : R) : f⁻¹ x = f.symm x := rfl

@[simp]
theorem RingAut.coe_pow {R : Type*} [CommSemiring R] (f : R ≃+* R) (n : ℕ) : ⇑(f ^ n) = f^[n] := by
  induction' n with n ih
  · simp
  · ext
    simp [pow_succ, ih]

-- `Mathlib.FieldTheory.Perfect` after `frobeniusEquiv_symm_pow_p`
@[simp]
theorem frobeniusEquiv_symm_pow_pow_p_pow (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (x : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p).symm ^[n]) x ^ (p ^ n) = x := by
  revert x
  induction' n with n ih
  · simp
  · intro x
    simp [pow_succ, pow_mul, ih]

/--
The Teichmüller expansion.
-/
theorem dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
    {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ (i ≤ n), (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by
  rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero,
      ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  intro i hi
  rw [WittVector.coeff_sum_of_disjoint]
  · rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi))]
    let g := fun x : ℕ ↦ (0 : R)
    rw [Finset.sum_congr rfl (g := fun x : ℕ ↦ (0 : R))]
    · simp
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_singleton] at hb
      exact teichmuller_mul_pow_coeff_of_ne _ (Ne.intro hb.2).symm
  · refine fun n ↦ ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ ↦ ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_setOf_eq]
    have := of_not_not ((teichmuller_mul_pow_coeff_of_ne _).mt ha)
    rw [← this]
    have := of_not_not ((teichmuller_mul_pow_coeff_of_ne _).mt hb)
    exact this

theorem eq_of_apply_teichmuller_eq {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [PerfectRing R p] (f g : 𝕎 R →+* S) (hp : IsNilpotent (p : S))
    (h : ∀ (x : R), f (teichmuller p x) = g (teichmuller p x)) : f = g := by
  obtain ⟨n, hn⟩ := hp
  ext x
  obtain ⟨c, hc⟩ := (dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n)
  calc
    f x = f (x - ∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + f (∑ (i ≤ n), teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by simp
    _ = ∑ (i ≤ n), f (teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i))) * p ^ i := by rw [hc]; simp [pow_succ, hn]
    _ = ∑ (i ≤ n), g (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i))) * p ^ i := by simp [h]
    _ = g (x - ∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + g (∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) := by rw [hc]; simp [pow_succ, hn]
    _ = g x := by simp


-- this file

-- variable (O p) in
-- def mkCompGhostComponent (n : ℕ) : 𝕎 O →+* O ⧸ span {(p : O)} ^ (n + 1) :=
--   ((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp (WittVector.ghostComponent n)

-- `Mathlib.RingTheory.WittVector.Basic` after `WittVector.map_coeff`
theorem map_eq_zero_iff {p : ℕ} {R S : Type*} [CommRing R] [CommRing S] [Fact (Nat.Prime p)]
    (f : R →+* S) {x : WittVector p R} :
    ((map f) x) = 0 ↔ ∀ n, f (x.coeff n) = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · apply_fun (fun x ↦ x.coeff n) at h
    simpa using h
  · ext n
    simpa using h n

-- `Mathlib.RingTheory.WittVector.Basic` after `WittVector.ghostComponent_apply` or a local lemma
theorem pow_dvd_ghostComponent_of_dvd_coeff {R : Type*} [CommRing R] {x : 𝕎 R} {n : ℕ}
    (hx : ∀ i ≤ n, (p : R) ∣ x.coeff i) : (p : R) ^ (n + 1) ∣ ghostComponent n x := by
  rw [WittVector.ghostComponent_apply, wittPolynomial, MvPolynomial.aeval_sum]
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  have : (MvPolynomial.aeval x.coeff) ((MvPolynomial.monomial (R := ℤ)
      (Finsupp.single i (p ^ (n - i)))) (p ^ i)) = ((p : R) ^ i) * (x.coeff i) ^ (p ^ (n - i)) := by
    simp [MvPolynomial.aeval_monomial, map_pow]
  rw [this]
  have : n + 1 = (n - i) + 1 + i := by omega
  nth_rw 1 [this]
  rw [pow_add, mul_comm]
  apply mul_dvd_mul_left
  refine (pow_dvd_pow_of_dvd ?_ _).trans (b := (x.coeff i) ^ (n - i + 1)) (pow_dvd_pow _ ?_)
  · exact hx i (Nat.le_of_lt_succ hi)
  · exact ((n - i).lt_two_pow_self).succ_le.trans
        (pow_left_mono (n - i) (Nat.Prime.two_le Fact.out))

variable (n : ℕ)

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] in
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

def ghostComponentModPPow (n : ℕ): 𝕎 (O ⧸ span {(p : O)}) →+* O ⧸ span {(p : O)}^(n + 1) :=
  RingHom.liftOfSurjective (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)})
    (map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp
    (WittVector.ghostComponent (p := p) n), ker_map_le_ker_mk_comp_ghostComponent n⟩

#check PreTilt.mk_untilt_eq_coeff_zero
end WittVector

-- Mathlib.FieldTheory.Perfect

-- `Mathlib.FieldTheory.Perfect` after `iterateFrobeniusEquiv_symm`

@[simp]
theorem coe_frobenius_comp_coe_frobeniusEquiv {p : ℕ} {R : Type*}
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] :
    (⇑(frobenius R p) ∘ ⇑(frobeniusEquiv R p).symm) = id := by
  ext
  simp

/--
The `(frobeniusEquiv R p).symm` version of `MonoidHom.map_frobenius`
-/
theorem MonoidHom.map_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    (f : R →* S) (p : ℕ) [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply_fun (frobeniusEquiv S p)
  simp [← MonoidHom.map_frobenius]

theorem RingHom.map_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    (f : R →+* S) (p : ℕ) [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply_fun (frobeniusEquiv S p)
  simp [← RingHom.map_frobenius]

theorem MonoidHom.map_iterate_frobeniusEquiv_symm {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S]
    (f : R →* S) (p : ℕ) [ExpChar R p]
    [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm ^[n]) x) = ((frobeniusEquiv S p).symm ^[n]) (f x) := by
  apply_fun (frobeniusEquiv S p)^[n]
  · simp only [coe_frobeniusEquiv, ← map_iterate_frobenius]
    · rw [← Function.comp_apply (f := (⇑(_root_.frobenius R p))^[n]),
          ← Function.comp_apply (f := (⇑(_root_.frobenius S p))^[n]),
          ← Function.Commute.comp_iterate, ← Function.Commute.comp_iterate]
      · simp
      all_goals rw [← coe_frobeniusEquiv]; simp [Function.Commute, Function.Semiconj]
  apply Function.Injective.iterate
  simp

theorem RingHom.map_iterate_frobeniusEquiv_symm {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S]
    (f : R →+* S) (p : ℕ) [ExpChar R p]
    [PerfectRing R p] [ExpChar S p] [PerfectRing S p] (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm ^[n]) x) = ((frobeniusEquiv S p).symm ^[n]) (f x) :=
  MonoidHom.map_iterate_frobeniusEquiv_symm (f.toMonoidHom) p n x

-- `Mathlib.RingTheory.Perfection` after `Perfection.coeff_iterate_frobenius'`
@[simp]
theorem Perfection.coeff_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {p : ℕ}
    [hp : Fact (Nat.Prime p)] [CharP R p] (f : Ring.Perfection R p) (n : ℕ) :
    (Perfection.coeff R p n) ((_root_.frobeniusEquiv (Ring.Perfection R p) p).symm f) =
    (Perfection.coeff R p (n + 1)) f := by
  nth_rw 2 [← frobenius_apply_frobeniusEquiv_symm _ p f]
  rw [coeff_frobenius]

@[simp]
theorem Perfection.coeff_iterate_frobeniusEquiv_symm {R : Type*} [CommSemiring R] {p : ℕ}
    [hp : Fact (Nat.Prime p)] [CharP R p] (f : Ring.Perfection R p) (n m : ℕ) :
    (Perfection.coeff _ p n) ((_root_.frobeniusEquiv _ p).symm ^[m] f) =
    (Perfection.coeff _ p (n + m)) f := by
  revert f n
  induction' m with m ih
  · simp
  · intro f n
    simp [ih, ← add_assoc]

section
-- PreTilt
omit [IsAdicComplete (span {(p : O)}) O]

@[simp]
theorem PreTilt.coeff_frobenius (n : ℕ) (x : PreTilt O p) :
    ((Perfection.coeff (ModP O p) p (n + 1)) (((_root_.frobenius (PreTilt O p) p)) x)) =
    ((Perfection.coeff (ModP O p) p n) x):= by
  simp [PreTilt]

@[simp]
theorem PreTilt.coeff_frobenius_pow (m n : ℕ) (x : PreTilt O p) :
    ((Perfection.coeff (ModP O p) p (m + n)) (((_root_.frobenius (PreTilt O p) p) ^[n]) x)) =
    ((Perfection.coeff (ModP O p) p m) x):= by
  simp [PreTilt]

@[simp]
theorem PreTilt.coeff_frobeniusEquiv_symm (n : ℕ) (x : PreTilt O p) :
    ((Perfection.coeff (ModP O p) p n) (((_root_.frobeniusEquiv (PreTilt O p) p).symm) x)) =
    ((Perfection.coeff (ModP O p) p (n + 1)) x):= by
  simp [PreTilt]

@[simp]
theorem PreTilt.coeff_iterate_frobeniusEquiv_symm (m n : ℕ) (x : PreTilt O p) :
    ((Perfection.coeff (ModP O p) p m) (((_root_.frobeniusEquiv (PreTilt O p) p).symm ^[n]) x)) =
    ((Perfection.coeff (ModP O p) p (m + n)) x):= by
  simp [PreTilt]

end

-- `Untilt`, after `mk_comp_untilt_eq_coeff_zero`
namespace WittVector
@[simp]
theorem map_mk_teichmuller_frobeniusEquiv_symm_pow_untilt (n : ℕ) (x : O^♭) :
    WittVector.map (Ideal.Quotient.mk (span {(p : O)}))
    (teichmuller p ((((_root_.frobeniusEquiv _ p).symm ^ n) x).untilt)) =
    (teichmuller p (Perfection.coeff (ModP O p) _ n x)) := by
  simp only [RingAut.coe_pow, map_teichmuller, mk_untilt_eq_coeff_zero,
    coeff_iterate_frobeniusEquiv_symm, zero_add]

@[simp]
theorem PreTilt.untilt_frobeniusEquiv_symm_pow_pow (x : O^♭) (n : ℕ) :
    untilt (((_root_.frobeniusEquiv (O^♭) p).symm ^[n]) x) ^ p ^ n = x.untilt := by
  simp only [← map_pow]
  congr
  simp

-- already simp
-- @[simp]
-- theorem ghostComponent_teichmuller_frobeniusEquiv_symm_pow_untilt (n : ℕ) (x : O^♭) :
--     ghostComponent n (teichmuller p ((((_root_.frobeniusEquiv _ p).symm ^ n) x).untilt)) =
--     x.untilt := by
--   simp

#check RingHom.liftOfRightInverse_comp_apply

-- `Mathlib.RingTheory.Ideal.Maps` after `RingHom.eq_liftOfRightInverse`
open RingHom
theorem RingHom.liftOfSurjective_comp_apply {A B C : Type*} [Ring A] [Ring B] [Ring C]
    (f : A →+* B) (hf : Function.Surjective f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    ((f.liftOfSurjective hf) g) (f x) = (g : A →+* C) x :=
  RingHom.liftOfRightInverse_comp_apply f _ _ g x

theorem RingHom.liftOfSurjective_comp {A B C : Type*} [Ring A] [Ring B] [Ring C]
    (f : A →+* B) (hf : Function.Surjective f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) :
    ((f.liftOfSurjective hf) g).comp f = (g : A →+* C) :=
  RingHom.liftOfRightInverse_comp f _ _ g

theorem RingHom.eq_liftOfSurjective {A B C : Type*} [Ring A] [Ring B] [Ring C]
    (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g)
    (h : B →+* C) (hh : h.comp f = g) : h = (f.liftOfSurjective hf) ⟨g, hg⟩ :=
  RingHom.eq_liftOfRightInverse f _ _ g _ _ hh

--

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

-- Quotient.lift
#check RingHom.liftOfSurjective
#check WittVector.map

end WittVector

variable (O p) in
def fontaineThetaModPPow (n : ℕ): 𝕎 (O^♭) →+* O ⧸ span {(p : O)} ^ (n + 1) :=
  (ghostComponentModPPow n).comp
      (((WittVector.map (Perfection.coeff _ p 0))).comp
          (WittVector.map ((frobeniusEquiv (O^♭) p).symm ^ n : O^♭ →+* O^♭)))

@[simp]
theorem fontaineThetaModPPow_teichmuller (n : ℕ) (x : O^♭) :
    fontaineThetaModPPow O p n (teichmuller p x) = Ideal.Quotient.mk _ x.untilt := by
  simp [fontaineThetaModPPow, PreTilt]
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
  simp [PreTilt, fontaineThetaModPPow]

theorem factorPowSucc_fontaineThetaModPPow_eq (n : ℕ) (x : 𝕎 (O^♭)) :
    (factorPowSucc _ (n + 1)).comp (fontaineThetaModPPow O p (n + 1)) x =
    fontaineThetaModPPow O p n x:= by
  rw [← factorPowSucc_comp_fontaineThetaModPPow n]

#check IsAdicComplete.limRingHom
#synth IsAdicComplete (span {(p : 𝕎 (O^♭))}) (𝕎 (O^♭))

#check fontaineThetaModPPow

def fontaineTheta : 𝕎 (O^♭) →+* O :=
  IsAdicComplete.limRingHom Order.succ_strictMono (factorPowSucc_fontaineThetaModPPow_eq _ _).symm

theorem mk_pow_fontaineTheta (n : ℕ) (x : 𝕎 (O^♭)) :
    Ideal.Quotient.mk (span {(p : O)} ^ (n + 1)) (fontaineTheta x) = fontaineThetaModPPow O p n x :=
  IsAdicComplete.mk_limRingHom Order.succ_strictMono
      (factorPowSucc_fontaineThetaModPPow_eq _ _).symm n x

-- `Mathlib.RingTheory.WittVector.Basic` after `WittVector.map_coeff`
@[simp]
theorem WittVector.map_id (R : Type*) [CommRing R] :
    WittVector.map (RingHom.id R) = RingHom.id (𝕎 R) := by
  ext
  simp

-- move this lemma
omit [Fact (Nat.Prime p)]
  [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
private theorem ghostComponentModPPow.aux : span {(p : O)} ^ (0 + 1) = span {(p : O)} := by
  simp

def ghostComponentModPPow' (n : ℕ): 𝕎 (O ⧸ span {(p : O)}) →+* O ⧸ span {(p : O)}^(n + 1) :=
  RingHom.liftOfSurjective (WittVector.map <| Ideal.Quotient.mk <| span {(p : O)})
    (map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨((Ideal.Quotient.mk <| span {(p : O)} ^ (n + 1))).comp
    (WittVector.ghostComponent (p := p) n), ker_map_le_ker_mk_comp_ghostComponent n⟩

omit
  [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
@[simp]
theorem quotEquivOfEq_ghostComponentModPPow (x : 𝕎 (O ⧸ span {(p : O)})) :
    quotEquivOfEq (ghostComponentModPPow.aux) (ghostComponentModPPow 0 x) =
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
  -- Note to reviewer : `WittVector.map_coeff` should, but does not work in this simp
  rfl

end RingHom

-- theorem modPPow

-- Teichmuller lifts

theorem fontaineTheta_teichmuller (x : O^♭) : fontaineTheta (teichmuller p x) = x.untilt := by
  rw [IsHausdorff.eq_iff_smodEq' (I := span {(p : O)})]
  intro n
  cases n
  · simp
  · simp [SModEq, mk_pow_fontaineTheta]

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
  simp? [f, Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]


def fontaineThetaInvertP :
    Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭)) →+* Localization.Away (p : O) :=
  Localization.awayLift ((algebraMap O _).comp fontaineTheta) (p : 𝕎 (O^♭))
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O))

section PeriodRing

variable (R : Type*) [CommRing R] (f : R)
#synth CommRing (Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭)))

-- import Mathlib.RingTheory.Localization.Away.Basic
#check Localization.awayLift
variable (O p) in
def BDeRhamPlus : Type u :=
  AdicCompletion (R := (Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭))))
      (RingHom.ker fontaineThetaInvertP) (Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭)))

-- Mathlib.RingTheory.AdicCompletion.Algebra
instance : CommRing (BDeRhamPlus O p) := AdicCompletion.instCommRing _

end PeriodRing
def BDeRham : Type u := FractionRing (BDeRhamPlus O p)
notation "𝔹_dR^+(" O ")" => BDeRhamPlus O

end

-- Teichmuller series PR
-- lemmas about frobenius and untilt another PR
-- fontaine theta and Bdr PR
-- surjective to another PR
