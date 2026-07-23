/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.GroupTheory.GroupAction.Defs

set_option linter.minImports true

/-!
# The orbit-product identity: the gap-independent core of the orbit-product argument (general DvdK1)

the orbit-product argument (the Galois orbit-product proof of one-variable Duistermaat–van der
Kallen, the sole remaining input to the GMC(2) formalization once `HeightWitnessSupplier` is
discharged) rests on a purely group-theoretic fact: for a finite group `G` acting **transitively**
on a finite set `Ω`, and any `f : Ω → A` into a commutative monoid,

  `∏_{g ∈ G} f (g • x) = (∏_{α ∈ Ω} f α) ^ |Stab_G x|`.

Its field corollary (a proper root-subset product `p = ∏_{β∈S} β` lying in the base field forces
`|Ω| · v(p) = |S| · v(∏_Ω α)` for any valuation `v`) is the valuation contradiction that closes
the orbit-product argument: with `v(∏_Ω) = 0` and `v(p) = 1` (`p = c·t`), `|Ω| = 0`, absurd.

This module proves the group-theoretic core, gap-free and kernel-pure — the orbit-product target.
The one genuinely valued-field piece (the small-root product identity, the small-root product, an
unramified Hensel lift) is separate.
-/

open scoped BigOperators
open MulAction Finset

namespace GMC2.OrbitProduct

variable {G Ω A : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

/-- For a transitive action the fibers of `g ↦ g • x` all have the cardinality of the stabilizer. -/
theorem card_fiber_smul_eq_card_stabilizer [IsPretransitive G Ω] (x y : Ω) :
    Fintype.card {g : G // g • x = y} = Fintype.card (stabilizer G x) := by
  obtain ⟨g0, hg0⟩ := MulAction.exists_smul_eq G x y
  refine Fintype.card_congr ?_
  refine
    { toFun := fun g => ⟨g0⁻¹ * g.1, ?_⟩
      invFun := fun s => ⟨g0 * s.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mem_stabilizer_iff, mul_smul, g.2, ← hg0, inv_smul_smul]
  · rw [mul_smul, s.2, hg0]
  · intro g; ext; simp
  · intro s; ext; simp

/-- **Orbit-product identity.**  Under a transitive finite action, the product over the group of `f`
along the orbit of `x` is the full-orbit product raised to the stabilizer order. -/
theorem prod_smul_eq_prod_pow_card_stabilizer [IsPretransitive G Ω] [CommMonoid A]
    (f : Ω → A) (x : Ω) :
    ∏ g : G, f (g • x) = (∏ α : Ω, f α) ^ Fintype.card (stabilizer G x) := by
  rw [← Fintype.prod_fiberwise (fun g : G => g • x) (fun g => f (g • x))]
  have key : ∀ y : Ω,
      (∏ i : {g : G // (fun g : G => g • x) g = y}, f ((i : G) • x))
        = f y ^ Fintype.card (stabilizer G x) := by
    intro y
    rw [Finset.prod_congr rfl (fun i _ => congrArg f i.2)]
    rw [Finset.prod_const, Finset.card_univ, card_fiber_smul_eq_card_stabilizer]
  rw [Finset.prod_congr rfl (fun y _ => key y), Finset.prod_pow]

/-- All stabilizers of a transitive action have equal order (they are conjugate; here via the
explicit conjugation bijection `s ↦ g₀⁻¹ s g₀` where `g₀ • x = y`). -/
theorem card_stabilizer_eq_card_stabilizer [IsPretransitive G Ω] (x y : Ω) :
    Fintype.card (stabilizer G y) = Fintype.card (stabilizer G x) := by
  obtain ⟨g0, hg0⟩ := MulAction.exists_smul_eq G x y
  refine Fintype.card_congr ?_
  refine
    { toFun := fun s => ⟨g0⁻¹ * s.1 * g0, ?_⟩
      invFun := fun t => ⟨g0 * t.1 * g0⁻¹, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, hg0, s.2, ← hg0, inv_smul_smul]
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hg0, inv_smul_smul, t.2, hg0]
  · intro s; ext; simp [mul_assoc]
  · intro t; ext; simp [mul_assoc]

/-- **Orbit-product equation — the abstract core of the orbit-product argument.** If `A` carries a
distributive `G`-action, `f` is `G`-equivariant, and the subset product `p = ∏_{β∈S} f β` is
`G`-fixed (it lies in the base field of a Galois extension), then

  `p ^ |G| = (∏_{α∈Ω} f α) ^ (|S| · |Stab_G x|)`.

Taking any additive valuation `v` gives `|G|·v(p) = |S|·|Stab|·v(C)`, and with `|G| = |Ω|·|Stab|`
this is `|Ω|·v(p) = |S|·v(C)` — the valuation identity that closes the orbit-product argument
(`v(C)=0`, `v(p)=1` ⟹ `|Ω|=0`, absurd). -/
theorem prod_pow_card_group_eq [IsPretransitive G Ω] [CommMonoid A] [MulDistribMulAction G A]
    (f : Ω → A) (S : Finset Ω) (x : Ω)
    (hf : ∀ (g : G) (β : Ω), f (g • β) = g • f β)
    (hfix : ∀ g : G, g • (∏ β ∈ S, f β) = ∏ β ∈ S, f β) :
    (∏ β ∈ S, f β) ^ Fintype.card G
      = (∏ α : Ω, f α) ^ (S.card * Fintype.card (stabilizer G x)) := by
  -- ∏_{g} (g • p) with p = ∏_{β∈S} f β
  have hL : ∏ _g : G, (∏ β ∈ S, f β) = (∏ β ∈ S, f β) ^ Fintype.card G := by
    rw [Finset.prod_const, Finset.card_univ]
  have hstep : ∀ g : G, (∏ β ∈ S, f β) = ∏ β ∈ S, f (g • β) := by
    intro g
    calc (∏ β ∈ S, f β) = g • (∏ β ∈ S, f β) := (hfix g).symm
      _ = ∏ β ∈ S, g • f β := by rw [Finset.smul_prod']
      _ = ∏ β ∈ S, f (g • β) := by
            exact Finset.prod_congr rfl (fun β _ => (hf g β).symm)
  calc (∏ β ∈ S, f β) ^ Fintype.card G
      = ∏ _g : G, (∏ β ∈ S, f β) := hL.symm
    _ = ∏ g : G, ∏ β ∈ S, f (g • β) := Finset.prod_congr rfl (fun g _ => hstep g)
    _ = ∏ β ∈ S, ∏ g : G, f (g • β) := Finset.prod_comm
    _ = ∏ β ∈ S, (∏ α : Ω, f α) ^ Fintype.card (stabilizer G β) :=
          Finset.prod_congr rfl (fun β _ => prod_smul_eq_prod_pow_card_stabilizer f β)
    _ = ∏ β ∈ S, (∏ α : Ω, f α) ^ Fintype.card (stabilizer G x) :=
          Finset.prod_congr rfl (fun β _ => by rw [card_stabilizer_eq_card_stabilizer β x])
    _ = (∏ α : Ω, f α) ^ (S.card * Fintype.card (stabilizer G x)) := by
          rw [Finset.prod_const, ← pow_mul, Nat.mul_comm]

/-- **The valuation contradiction engine of the orbit-product argument.** For any additive valuation
`v` (a map turning products into sums), the orbit-product equation forces the `G`-fixed subset
product `p` to have the *same-signed* valuation as the full product `C`: if `v(C) = 0` then
`v(p) = 0`. The orbit-product argument applies this with `C = ∏ Ω = (−1)^d r_0/r_d` (valuation `0`
at `t = 0`) and `p = c·t` (valuation `1`), so the hypothesis `v(p) = 1 ≠ 0` contradicts the
conclusion `v(p) = 0`, proving some `CT(Λ^m) ≠ 0`. -/
theorem valuation_zero_of_prod_fixed [IsPretransitive G Ω] [CommMonoid A] [MulDistribMulAction G A]
    (f : Ω → A) (S : Finset Ω) (x : Ω)
    (hf : ∀ (g : G) (β : Ω), f (g • β) = g • f β)
    (hfix : ∀ g : G, g • (∏ β ∈ S, f β) = ∏ β ∈ S, f β)
    (v : A → ℤ) (hv : ∀ a b : A, v (a * b) = v a + v b)
    (hC : v (∏ α : Ω, f α) = 0)
    (hG : 0 < Fintype.card G) :
    v (∏ β ∈ S, f β) = 0 := by
  have h1 : v (1 : A) = 0 := by have := hv 1 1; simp only [mul_one] at this; omega
  have hpow : ∀ (a : A) (n : ℕ), v (a ^ n) = (n : ℤ) * v a := by
    intro a n
    induction n with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, hv, ih]; push_cast; ring
  have heq := prod_pow_card_group_eq f S x hf hfix
  have hval := congrArg v heq
  rw [hpow, hpow, hC, mul_zero] at hval
  -- hval : (card G) * v p = 0
  have hGpos : (0 : ℤ) < Fintype.card G := by exact_mod_cast hG
  rcases mul_eq_zero.mp hval with h | h
  · exact absurd h (ne_of_gt hGpos)
  · exact h

/-- **The orbit-product abstract contradiction capstone.** Packaging
`valuation_zero_of_prod_fixed` with the hypothesis that the fixed subset product has *nonzero*
valuation: the two are contradictory. In the DvdK instantiation `v(∏_Ω f) = v(C_Φ) = 0` (Vieta, a
constant) while `v(∏_S f) = v(c·t) = 1 ≠ 0` (the small-root product identity), so the assumption
"all `CT(Λ^m) = 0`" (which produces the fixed small-root product) is refuted — some `CT(Λ^m) ≠ 0`.
-/
theorem orbit_product_contradiction [IsPretransitive G Ω] [CommMonoid A] [MulDistribMulAction G A]
    (f : Ω → A) (S : Finset Ω) (x : Ω)
    (hf : ∀ (g : G) (β : Ω), f (g • β) = g • f β)
    (hfix : ∀ g : G, g • (∏ β ∈ S, f β) = ∏ β ∈ S, f β)
    (v : A → ℤ) (hv : ∀ a b : A, v (a * b) = v a + v b)
    (hC : v (∏ α : Ω, f α) = 0)
    (hp : v (∏ β ∈ S, f β) ≠ 0)
    (hG : 0 < Fintype.card G) : False :=
  hp (valuation_zero_of_prod_fixed f S x hf hfix v hv hC hG)

end GMC2.OrbitProduct

