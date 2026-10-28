/-
Copyright (c) 2026 Eric Jackson, Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Jackson
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Structure of finite abelian torsion groups

We prove that if all `d`-torsion subgroups of an abelian group `A`, for `d ∣ n`, have
cardinality `d ^ r`, then the `n`-torsion subgroup `A[n]` is `(ZMod n) ^ r`.

The proof has two parts.

* **Prime powers.** `A[p ^ k]` is finite of cardinality `(p ^ k) ^ r`. By the structure theorem
  for finite abelian groups it is a direct sum of cyclic groups `ZMod (n i)` with `n i > 1`.
  Each `n i` divides `p ^ k` (the `i`-th basis vector lies in `A[p ^ k]`), and comparing the
  cardinality of the `p`-torsion shows that there are exactly `r` summands. Then the product
  `∏ n i = (p ^ k) ^ r` of `r` divisors of `p ^ k` forces `n i = p ^ k` for all `i`.
* **Assembly.** `A[n]` is the internal direct sum of its prime-power torsion parts
  (`Submodule.torsionBy_isInternal`), each part is `(ZMod (p ^ e)) ^ r` by the prime-power case,
  and the parts are reassembled by the Chinese remainder theorem (`ZMod.equivPi`).

## Main results

* `Submodule.nonempty_addEquiv_pi_zmod`: the general statement.
* `Submodule.prime_power_case`: the prime-power case.
* `Submodule.torsionByTorsionByAddEquiv`: the `a`-torsion of `A[n]` is the `a`-torsion of `A`.

## Implementation notes

The prime-power case uses the cardinality of the `p`-torsion of a direct sum of cyclic groups,
and the fact that `p ^ (f i)`-torsion of `ZMod (p ^ (f i))` has `p` elements. Both are provided
as private lemmas below; the latter is the case `d = p` of `card_torsionBy_zmod`, which computes
the `d`-torsion of `ZMod n` as `n.gcd d` (for `n ≠ 0`).

## Provenance

The file header lists both copyright holders, reflecting the adaptation described below.
The adapted material comes from `HasseWeil/NTorsion/TorsionGeneralN.lean` in the AINTLIB
project (Apache-2.0). Original copyright notice, reproduced verbatim (Apache-2.0 §4(c)):

  Copyright (c) 2026 Chris Birkbeck. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Chris Birkbeck

Modification statement (Apache-2.0 §4(b)): the CRT assembly below follows that file,
adapted from rank two to arbitrary rank: the prime-power
factorisation `q p = p ^ (n.factorization p)` and the product and pairwise-coprimality premises
of `Submodule.torsionBy_isInternal`, the extraction
`LinearEquiv.ofBijective (DirectSum.coeLinearMap _)`, `piCommAddEquiv` (generalising
`piSwapAddEquiv`), `piCrtAddEquiv`, the shape of the summand bridge
(`torsionByTorsionByAddEquiv`, generalising `summandEquiv`), and the final five-step
composition. The prime-power classification (`prime_power_case`) uses the same standard
strategy as AINTLIB's rank-2 case but different counting machinery; the counting lemmas
(`card_pi_zmod`, `card_torsion_pi`, `card_torsionBy_zmod`), the torsion-restriction helper
(`torsionByAddEquiv`), the order lemma (`addOrderOf_lof_zmod`), and the product lemma
(`eq_of_dvd_of_prod_eq_pow`) are independently implemented.
-/

@[expose] public section

open scoped AddSubgroup DirectSum

namespace Submodule

variable {A : Type*} [AddCommGroup A]

/-! ### Counting torsion in cyclic groups and products -/

/-- The cardinality of a product of cyclic groups. -/
private theorem card_pi_zmod {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    Nat.card (Π i, ZMod (m i)) = ∏ i, m i := by
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_zmod (m i)

/-- The `q`-torsion is computed componentwise on a product of cyclic groups. -/
private theorem card_torsion_pi {ι : Type*} [Fintype ι] (m : ι → ℕ) (q : ℕ) :
    Nat.card (torsionBy ℤ (Π i, ZMod (m i)) (q : ℤ))
      = ∏ i, Nat.card (torsionBy ℤ (ZMod (m i)) (q : ℤ)) := by
  have e : torsionBy ℤ (Π i, ZMod (m i)) (q : ℤ)
      ≃ Π i, torsionBy ℤ (ZMod (m i)) (q : ℤ) :=
    { toFun := fun x i => ⟨x.1 i, by
        have h := congrFun ((mem_torsionBy_iff (q : ℤ) x.1).mp x.2) i
        simpa [Pi.smul_apply] using h⟩
      invFun := fun y => ⟨fun i => (y i).1, by
        rw [mem_torsionBy_iff]
        funext i
        simp [Pi.smul_apply]⟩
      left_inv := fun x => by ext i; rfl
      right_inv := fun y => by ext i; rfl }
  rw [Nat.card_congr e, Nat.card_pi]

/-- An additive equivalence preserves the `q`-torsion subgroup. -/
private def torsionByAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (q : ℕ) : torsionBy ℤ M (q : ℤ) ≃+ torsionBy ℤ N (q : ℤ) where
  toFun x := ⟨e x.1, by
    have h : (q : ℤ) • x.1 = 0 := (mem_torsionBy_iff (q : ℤ) x.1).mp x.2
    rw [mem_torsionBy_iff, ← map_zsmul e (q : ℤ) x.1, h, map_zero]⟩
  invFun y := ⟨e.symm y.1, by
    have h : (q : ℤ) • y.1 = 0 := (mem_torsionBy_iff (q : ℤ) y.1).mp y.2
    rw [mem_torsionBy_iff, ← map_zsmul e.symm (q : ℤ) y.1, h, map_zero]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

/-- **The `d`-torsion of `ZMod n` has `n.gcd d` elements**, for `n ≠ 0`. Indeed it is the
subgroup generated by `n / n.gcd d`, whose additive order is `n / (n / n.gcd d) = n.gcd d`.

The hypothesis `n ≠ 0` is necessary: `ZMod 0` is `ℤ`, which is torsion-free, so its `d`-torsion
is trivial for `d ≠ 0`, whereas `0.gcd d = d`. -/
private theorem card_torsionBy_zmod (n d : ℕ) (hn : n ≠ 0) :
    Nat.card (torsionBy ℤ (ZMod n) d) = n.gcd d := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have : NeZero n := ⟨hn⟩
  set g := n.gcd d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hn0
  have hgdvd : g ∣ n := Nat.gcd_dvd_left n d
  have hngdvd : n / g ∣ n := Nat.div_dvd_of_dvd hgdvd
  have hsplit' : g * (n / g) = n := by
    rw [mul_comm]; exact Nat.div_mul_cancel hgdvd
  have hd : d = g * (d / g) := by
    have h := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n d)).symm
    rwa [← hg] at h
  -- the key arithmetic fact: `n ∣ d * m ↔ n / g ∣ m`
  have harith : ∀ m : ℕ, n ∣ d * m ↔ n / g ∣ m := by
    intro m
    have hdm : g * ((d / g) * m) = d * m := by rw [← mul_assoc, ← hd]
    constructor
    · intro h
      have h2 : g * (n / g) ∣ g * ((d / g) * m) := by rw [hsplit', hdm]; exact h
      exact (Nat.coprime_div_gcd_div_gcd hg0).dvd_of_dvd_mul_left
        (Nat.dvd_of_mul_dvd_mul_left hg0 h2)
    · intro h
      have h2 : g * (n / g) ∣ g * ((d / g) * m) :=
        Nat.mul_dvd_mul_left g (by rw [mul_comm]; exact h.mul_right (d / g))
      rwa [hsplit', hdm] at h2
  -- the torsion subgroup is the one generated by `n / g`
  have hkey : ∀ x : ZMod n, x ∈ torsionBy ℤ (ZMod n) d ↔
      x ∈ AddSubgroup.zmultiples ((n / g : ℕ) : ZMod n) := by
    intro x
    rw [mem_torsionBy_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · intro hx
      have h1 : ((d * x.val : ℕ) : ZMod n) = 0 := by
        rw [← hx, zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
      obtain ⟨c, hc⟩ := (harith x.val).mp ((ZMod.natCast_eq_zero_iff _ _).mp h1)
      refine ⟨(c : ℤ), ?_⟩
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm, ← Nat.cast_mul, ← hc,
        ZMod.natCast_zmod_val]
    · rintro ⟨k, hk⟩
      have hda : (d : ℤ) • ((n / g : ℕ) : ZMod n) = 0 := by
        rw [zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
        have h1 : d * (n / g) = (g * (n / g)) * (d / g) := by
          conv_lhs => rw [hd]
          ring
        rw [h1, hsplit']
        exact dvd_mul_right n (d / g)
      rw [← hk, smul_comm, hda, smul_zero]
  calc Nat.card (torsionBy ℤ (ZMod n) d)
      = Nat.card ↥(AddSubgroup.zmultiples ((n / g : ℕ) : ZMod n)) :=
        Nat.card_congr (Equiv.subtypeEquivRight hkey)
    _ = addOrderOf ((n / g : ℕ) : ZMod n) := Nat.card_zmultiples _
    _ = n / n.gcd (n / g) := ZMod.addOrderOf_coe _ hn
    _ = n / (n / g) := by rw [Nat.gcd_eq_right hngdvd]
    _ = g := Nat.div_div_self hgdvd hn

/-! ### Orders of direct-sum basis vectors -/

/-- The `i`-th basis vector of `⨁ i, ZMod (m i)` has additive order `m i`. -/
private theorem addOrderOf_lof_zmod {ι : Type*} [DecidableEq ι] (m : ι → ℕ) (i : ι) :
    addOrderOf (DirectSum.lof ℤ ι (fun i => ZMod (m i)) i 1) = m i := by
  let L : ZMod (m i) →ₗ[ℤ] DirectSum ι (fun i => ZMod (m i)) :=
    DirectSum.lof ℤ ι (fun i => ZMod (m i)) i
  change addOrderOf (L 1) = m i
  have h3 : addOrderOf (L 1) • (1 : ZMod (m i)) = 0 := by
    have h := addOrderOf_nsmul_eq_zero (x := L 1)
    have hc := congrArg (DirectSum.component ℤ ι (fun i => ZMod (m i)) i) h
    rw [map_nsmul] at hc
    simpa [L] using hc
  refine Nat.dvd_antisymm ?_ ?_
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul]
    simp
  · have h4 : addOrderOf (1 : ZMod (m i)) ∣ addOrderOf (L 1) :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3
    rwa [ZMod.addOrderOf_one] at h4

/-- If `r` positive integers each divide `N` and their product is `N ^ r`, they are all `N`. -/
private theorem eq_of_dvd_of_prod_eq_pow {ι : Type*} [Fintype ι] {N : ℕ} (hN : 0 < N)
    {n : ι → ℕ} (hdvd : ∀ i, n i ∣ N) (hprod : ∏ i, n i = N ^ Fintype.card ι) :
    ∀ i, n i = N := by
  have hcomp : ∏ i, (N / n i) = 1 := by
    have h1 : (∏ i, (N / n i)) * (∏ i, n i) = ∏ _i : ι, N := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => Nat.div_mul_cancel (hdvd i)
    rw [hprod, Finset.prod_const, Finset.card_univ] at h1
    have h1' : (∏ i, N / n i) * N ^ Fintype.card ι = 1 * N ^ Fintype.card ι := by
      rw [one_mul]; exact h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hN _) h1'
  intro i
  have h2 : N / n i = 1 := by
    have h := Finset.dvd_prod_of_mem (fun j => N / n j) (Finset.mem_univ i)
    rw [hcomp] at h
    exact Nat.dvd_one.mp h
  have h3 := Nat.div_mul_cancel (hdvd i)
  rwa [h2, one_mul] at h3

/-! ### The `a`-torsion of `A[n]` -/

/-- If `a ∣ n`, the `a`-torsion of the `n`-torsion subgroup of `A` is the `a`-torsion of `A`:
an element killed by `a` is automatically killed by `n`. -/
noncomputable def torsionByTorsionByAddEquiv {a n : ℕ} (h : a ∣ n) :
    torsionBy ℤ (torsionBy ℤ A n) a ≃+ torsionBy ℤ A a where
  toFun x := ⟨x.1.1, by
    rw [mem_torsionBy_iff]
    have h : ((a : ℤ) • x : torsionBy ℤ (torsionBy ℤ A n) (a : ℤ)) = 0 :=
      smul_torsionBy (a : ℤ) x
    have h1 := congrArg
      (fun z : torsionBy ℤ (torsionBy ℤ A n) (a : ℤ) => ((z : torsionBy ℤ A n) : A)) h
    rw [coe_smul, coe_smul, ZeroMemClass.coe_zero] at h1
    exact h1⟩
  invFun Q := ⟨⟨Q.1, by
    rw [mem_torsionBy_iff]
    obtain ⟨c, rfl⟩ := h
    have hQ : (a : ℤ) • Q.1 = 0 := (mem_torsionBy_iff (a : ℤ) Q.1).mp Q.2
    rw [Nat.cast_mul, mul_comm, mul_smul, hQ, smul_zero]⟩, by
    rw [mem_torsionBy_iff]
    apply Subtype.ext
    rw [coe_smul, ZeroMemClass.coe_zero]
    exact (mem_torsionBy_iff (a : ℤ) Q.1).mp Q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! ### The prime-power case -/

/-- **Prime-power case.** If `#A[d] = d ^ r` for every `d ∣ p ^ k`, then
`A[p ^ k] ≃+ (Fin r → ZMod (p ^ k))`. -/
theorem prime_power_case {p r k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h : ∀ d : ℕ, d ∣ p ^ k → Nat.card A[d] = d ^ r) :
    Nonempty (A[p ^ k] ≃+ (Fin r → ZMod (p ^ k))) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hGcard : Nat.card A[p ^ k] = (p ^ k) ^ r := h _ dvd_rfl
  have hGpos : 0 < Nat.card A[p ^ k] := hGcard ▸ pow_pos (pow_pos hp.pos k) r
  have : Finite A[p ^ k] := (Nat.card_pos_iff.mp hGpos).2
  obtain ⟨ι, hι, n, hn, ⟨φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A[p ^ k]
  -- (1) the `i`-th basis vector lies in `A[p ^ k]`, so `n i ∣ p ^ k`
  have hdvd : ∀ i, n i ∣ p ^ k := by
    intro i
    set w : A[p ^ k] := φ.symm (DirectSum.lof ℤ ι (fun i => ZMod (n i)) i 1) with hw
    have hkill : p ^ k • w = 0 := by
      have h : ((p ^ k : ℕ) : ℤ) • w = 0 := smul_torsionBy ((p ^ k : ℕ) : ℤ) w
      rwa [Nat.cast_smul_eq_nsmul] at h
    have hord : addOrderOf w = n i := by
      rw [hw, AddEquiv.addOrderOf_eq φ.symm, addOrderOf_lof_zmod]
    rw [← hord]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
  -- (2) the product of the cyclic orders is the cardinality of `A[p ^ k]`
  have hprod : ∏ i, n i = (p ^ k) ^ r := by
    rw [← card_pi_zmod n,
      ← Nat.card_congr (DirectSum.linearEquivFunOnFintype ℤ ι
        (fun i => ZMod (n i))).toEquiv,
      ← Nat.card_congr φ.toEquiv, hGcard]
  -- (3) there are exactly `r` summands, by counting the `p`-torsion
  have hcardι : Fintype.card ι = r := by
    have h1 : Nat.card (torsionBy ℤ (torsionBy ℤ A (p ^ k)) p) = p ^ r := by
      refine (Nat.card_congr ?_).trans (h p (dvd_pow_self p hk.ne'))
      exact (torsionByTorsionByAddEquiv (dvd_pow_self p hk.ne')).toEquiv
    have hp_dvd : ∀ i, p ∣ n i := by
      intro i
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).mp (hdvd i)
      have hf0 : f ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hf
        exact absurd (hf ▸ hn i) (lt_irrefl 1)
      rw [hf]; exact dvd_pow_self p hf0
    have h2 : Nat.card (torsionBy ℤ (torsionBy ℤ A (p ^ k)) p) = p ^ Fintype.card ι := by
      calc Nat.card (torsionBy ℤ (torsionBy ℤ A (p ^ k)) p)
          = Nat.card (torsionBy ℤ (DirectSum ι (fun i => ZMod (n i))) (p : ℤ)) :=
            Nat.card_congr (torsionByAddEquiv φ p).toEquiv
        _ = Nat.card (torsionBy ℤ (Π i, ZMod (n i)) (p : ℤ)) :=
            Nat.card_congr (torsionByAddEquiv
              (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (n i))).toAddEquiv p).toEquiv
        _ = ∏ i, Nat.card (torsionBy ℤ (ZMod (n i)) (p : ℤ)) := card_torsion_pi n p
        _ = ∏ _i : ι, p := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [card_torsionBy_zmod (n i) p (by have := hn i; omega), Nat.gcd_eq_right (hp_dvd i)]
        _ = p ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
    exact Nat.pow_right_injective hp.two_le (h2.symm.trans h1)
  -- (4) hence every cyclic factor is `p ^ k`
  have hall : ∀ i, n i = p ^ k :=
    eq_of_dvd_of_prod_eq_pow (pow_pos hp.pos k) hdvd (by rw [hprod, hcardι])
  -- (5) assemble
  refine ⟨φ.trans ?_⟩
  rw [funext hall]
  exact (DirectSum.linearEquivFunOnFintype ℤ ι (fun _ => ZMod (p ^ k))).toAddEquiv.trans
    (LinearEquiv.piCongrLeft (R := ℤ) (φ := fun _ => ZMod (p ^ k))
      (Fintype.equivFinOfCardEq hcardι)).toAddEquiv

/-! ### Assembly over the prime factors -/

/-- The additive swap `(Π i, Fin r → X i) ≃+ (Fin r → Π i, X i)`. -/
private def piCommAddEquiv {ι : Type*} (r : ℕ) (X : ι → Type*) [∀ i, AddCommGroup (X i)] :
    (∀ i, Fin r → X i) ≃+ (Fin r → ∀ i, X i) where
  toFun f j i := f i j
  invFun g i j := g j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Pointwise Chinese remainder theorem: `(Fin r → Π p, ZMod (p ^ kₚ)) ≃+ (Fin r → ZMod n)`. -/
private noncomputable def piCrtAddEquiv {n : ℕ} (hn : n ≠ 0) (r : ℕ) :
    (Fin r → ∀ p : n.primeFactors, ZMod ((p : ℕ) ^ n.factorization (p : ℕ))) ≃+
      (Fin r → ZMod n) :=
  AddEquiv.piCongrRight fun _ : Fin r => (ZMod.equivPi (n := n) hn).symm.toAddEquiv

/-- **Structure of finite abelian torsion groups.** If `#A[d] = d ^ r` for every `d ∣ n`, then
`A[n] ≃+ (Fin r → ZMod n)`.

This is the group-theoretic input to the computation of the `n`-torsion of an elliptic curve:
for the group of points of an elliptic curve over an algebraically closed field and `r = 2` it
gives `E[n] ≃+ (ZMod n)²`. -/
theorem nonempty_addEquiv_pi_zmod {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card A[d] = d ^ r) :
    Nonempty (A[n] ≃+ (Fin r → ZMod n)) := by
  classical
  have hn0 : n ≠ 0 := hn.ne'
  -- the prime-power factors of `n`, as integers
  set q : ℕ → ℤ := fun p => (p : ℤ) ^ n.factorization p with hq_def
  have hprod : (n : ℤ) = ∏ p ∈ n.primeFactors, q p := by
    have hnat : n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p : ℕ) := by
      conv_lhs => rw [Nat.prod_primeFactors_coe_pow_factorization hn0]
      exact Finset.prod_coe_sort n.primeFactors fun p => (p ^ n.factorization p : ℕ)
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hnat
    push_cast at hcast
    exact hcast
  -- the prime-power factors are pairwise coprime
  have hcop : (↑n.primeFactors : Set ℕ).Pairwise (Function.onFun IsCoprime q) := by
    intro p hp p' hp' hne
    change IsCoprime ((p : ℤ) ^ n.factorization p) ((p' : ℤ) ^ n.factorization p')
    exact (Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hp')).mpr hne)).cast
  -- `A[n]` is the internal direct sum of its prime-power torsion parts
  have hM : Module.IsTorsionBy ℤ (torsionBy ℤ A n) (∏ p ∈ n.primeFactors, q p) := by
    rw [← hprod, Module.isTorsionBy_iff_torsionBy_eq_top]
    exact torsionBy_torsionBy_eq_top _
  have hInt : DirectSum.IsInternal fun p : n.primeFactors =>
      torsionBy ℤ (torsionBy ℤ A n) (q p) :=
    torsionBy_isInternal (S := n.primeFactors) (q := q) hcop hM
  -- each summand is `(ZMod (p ^ e)) ^ r` by the prime-power case
  have hterm : ∀ p : n.primeFactors,
      Nonempty (torsionBy ℤ (torsionBy ℤ A n) (q p) ≃+
        (Fin r → ZMod (p.1 ^ n.factorization p.1))) := by
    intro p
    have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hdvd : p.1 ^ n.factorization p.1 ∣ n := Nat.ordProj_dvd n p.1
    have hk : 0 < n.factorization p.1 :=
      hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors p.2)
    obtain ⟨e⟩ := prime_power_case (A := A) (p := p.1) (r := r) (k := n.factorization p.1)
      hpp hk (fun d hd => h d (hd.trans hdvd))
    exact ⟨(torsionByTorsionByAddEquiv hdvd).trans e⟩
  let e_p : ∀ p : n.primeFactors,
      (torsionBy ℤ (torsionBy ℤ A n) (q p) ≃+
        (Fin r → ZMod (p.1 ^ n.factorization p.1))) := fun p => Classical.choice (hterm p)
  -- reassemble: direct sum, product, per-summand equivalences, swap, CRT
  refine ⟨?_⟩
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hInt).symm.toAddEquiv.trans
    ((DirectSum.linearEquivFunOnFintype ℤ _ _).toAddEquiv.trans
      ((AddEquiv.piCongrRight e_p).trans
        ((piCommAddEquiv r (fun p : n.primeFactors =>
          ZMod (p.1 ^ n.factorization p.1))).trans
          (piCrtAddEquiv hn0 r))))

end Submodule
