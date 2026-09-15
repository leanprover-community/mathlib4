/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.RingTheory.LambdaRing.AdamsHom
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Adams operations on `K(G/P) ⊗ ℚ`

Setup. Let `G` be a reductive algebraic group, `B ⊆ G` a Borel subgroup, `G/B` the flag variety.
`K(G/B)` denotes its (topological or algebraic) K-theory: the Grothendieck group of vector
bundles on `G/B`, with `[E] + [F] := [E ⊕ F]` and `[E] · [F] := [E ⊗ F]`.

## The concrete case `G = GL(n)`

Here `G/B = Fl(n)`, the variety of complete flags `0 ⊂ V_1 ⊂ V_2 ⊂ ⋯ ⊂ V_n = ℂⁿ` with
`dim V_i = i`, and the abstract discussion above becomes fully explicit.
`Fl(n)` carries `n` tautological line bundles `L_1,…,L_n` (`L_i := V_i/V_{i-1}`)
and `K(Fl(n))` is generated, as a ring, by their classes `[L_1],…,[L_n]`.
Adams operations act on a *line* bundle by : `ψᵏ[L] = [L]^k = [L^{⊗k}]`

`KFlag n` below is exactly the algebraic skeleton this produces: `n` generators standing in for
`[L_1],…,[L_n]`-/

/-- The algebraic skeleton of `K(Fl(n)) ⊗ ℚ`
a `ℚ`-algebra `MvPolynomial (Fin n) ℚ`, but wrapped in its own type
so the specific Adams-operations structure below
can be registered as a genuine global `instance`. -/
@[expose] public def KFlag (n : ℕ) : Type := MvPolynomial (Fin n) ℚ

-- `KFlag n` is a `def`, not `abbrev` (deliberately: see above), so it does not
-- automatically unfold to `MvPolynomial (Fin n) ℚ` during the instance-sensitive unification
-- `MvPolynomial.algHom_ext` needs below.
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The `K` theory is a ring via direct sum and tensoring. -/
public noncomputable instance : CommRing (KFlag n) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n) ℚ))

/-- The `K` theory was tensored with `ℚ` so it is a `ℚ` algebra. -/
public noncomputable instance : Algebra ℚ (KFlag n) :=
  inferInstanceAs (Algebra ℚ (MvPolynomial (Fin n) ℚ))

/-- The class `[L_i] ∈ K(Fl(n)) ⊗ ℚ` of the `i`-th tautological line bundle. -/
@[expose] public noncomputable def KFlag.L (n : ℕ) (i : Fin n) : KFlag n := MvPolynomial.X i

-- The Adams operations, worked out directly on `MvPolynomial (Fin n) ℚ`

/--
The `ψ^k` on `ℚ[[L_1]...[L_n]]` where `[L_i]` are the classes
of the `i`-th tautological line bundles.
This is the aux version because it is on the underlying
`MvPolynomial` not on `KFlag`. `flagPsi` does that.
-/
@[expose] public noncomputable def flagPsiAux (n k : ℕ) :
    MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  MvPolynomial.aeval fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ) ^ k

private theorem flagPsiAux_apply_X (n k : ℕ) (i : Fin n) :
    flagPsiAux n k (MvPolynomial.X i) = (MvPolynomial.X i : MvPolynomial (Fin n) ℚ) ^ k :=
  MvPolynomial.aeval_X _ _

private theorem flagPsiAux_one (n : ℕ) :
    flagPsiAux n 1 = AlgHom.id ℚ (MvPolynomial (Fin n) ℚ) := by
  ext1 i
  rw [flagPsiAux_apply_X, pow_one, AlgHom.id_apply]

theorem flagPsiAux_mul (n : ℕ) (a b : ℕ) :
    flagPsiAux n (a * b) = (flagPsiAux n a).comp (flagPsiAux n b) := by
  ext1 i
  simp only [AlgHom.comp_apply, flagPsiAux_apply_X, map_pow, ← pow_mul]

/-- The Adams operations on `KFlag n`: `ψᵏ` acts on each tautological line bundle class `L i`
by `L i ↦ (L i) ^ k`, matching the line-bundle formula `ψᵏ[L] = [L]^k`. -/
@[expose] public noncomputable def flagPsi (n k : ℕ) : KFlag n →ₐ[ℚ] KFlag n := flagPsiAux n k

/-- `ψ^k` on the `KFlag n` is the identity -/
public theorem flagPsi_one (n : ℕ) : flagPsi n 1 = AlgHom.id ℚ (KFlag n) := flagPsiAux_one n

/-- The multiplicativity `ψ^{a*b}` as composition of `ψ^a` and `ψ^b` on `KFlag n` -/
public theorem flagPsi_mul (n : ℕ) (a b : ℕ) :
    flagPsi n (a * b) = (flagPsi n a).comp (flagPsi n b) := flagPsiAux_mul n a b

/-- `KFlag n` genuinely carries Adams operations: `ψᵏ` acting by `k`-th power on each
tautological-line-bundle generator. -/
public noncomputable instance : AdamsOperations ℚ (KFlag n) where
  ψ := flagPsi n
  ψ_one := flagPsi_one n
  ψ_mul _ _ := flagPsi_mul n _ _
  ψ_prime_congr _p hp _ := (isUnit_natCast_of_algebra_rat (R := ℚ) (A := KFlag n) hp.pos.ne').dvd

/-!
## Parabolics: `G/P` for `G = GL(n)`

A parabolic `B ⊆ P ⊆ GL(n)` is determined by
the block sizes of `P`'s Levi factor `GL(n_1) × ⋯ × GL(n_r)`
The partial flag variety `G/P` classifies flags `0 ⊂ W_1 ⊂ ⋯ ⊂ W_r = ℂⁿ`
with `dim W_j = n_1 + ⋯ + n_j`.
`K(G/P) ⊗ ℚ` sits as the subring of `K(Fl(n)) ⊗ ℚ` fixed by
the Levi's Weyl group `S_{n_1} × ⋯ × S_{n_r}` -/

variable {β : Type*}

/-- Permutations of `Fin n` that map each `blockOf`-fiber to itself.
For a composition `n = n_1 + ⋯ + n_r` with `blockOf : Fin n → Fin r` recording block membership,
this is the `S_{n_1} × ⋯ × S_{n_r} ≤ S_n` of the parabolic `P` it determines. -/
@[expose] public def LeviPerm (blockOf : Fin n → β) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i, blockOf (σ i) = blockOf i}
  mul_mem' {a b} ha hb i := by
    change blockOf (a (b i)) = blockOf i
    rw [ha (b i), hb i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by
    change blockOf (a.symm i) = blockOf i
    have h := ha (a.symm i)
    rw [a.apply_symm_apply] at h
    exact h.symm

/-- The subalgebra of `MvPolynomial (Fin n) ℚ` fixed by every block-preserving permutation -/
@[expose] public noncomputable def ParabSubalgebraAux (blockOf : Fin n → β) :
    Subalgebra ℚ (MvPolynomial (Fin n) ℚ) :=
  ⨅ σ : LeviPerm blockOf,
    AlgHom.equalizer (MvPolynomial.rename (σ : Equiv.Perm (Fin n)))
      (AlgHom.id ℚ (MvPolynomial (Fin n) ℚ))

theorem mem_ParabSubalgebraAux (blockOf : Fin n → β) (p : MvPolynomial (Fin n) ℚ) :
    p ∈ ParabSubalgebraAux blockOf ↔
      ∀ σ : LeviPerm blockOf, MvPolynomial.rename (σ : Equiv.Perm (Fin n)) p = p := by
  simp [ParabSubalgebraAux, AlgHom.mem_equalizer]

private theorem flagPsiAux_rename_comm (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    (flagPsiAux n k).comp (MvPolynomial.rename σ) =
      (MvPolynomial.rename σ).comp (flagPsiAux n k) := by
  ext1 i
  simp [AlgHom.comp_apply, flagPsiAux_apply_X, MvPolynomial.rename_X]

/-- `flagPsiAux n k`
commutes with renaming by any permutation
so it preserves the fixed subalgebra of *any* subgroup of
permutations, in particular `ParabSubalgebraAux blockOf`. -/
theorem parabSubalgebraAux_psi_mem (blockOf : Fin n → β) (k : ℕ) :
    ∀ x ∈ ParabSubalgebraAux blockOf, flagPsiAux n k x ∈ ParabSubalgebraAux blockOf := by
  intro x hx
  rw [mem_ParabSubalgebraAux] at hx ⊢
  intro σ
  have h : (MvPolynomial.rename (σ : Equiv.Perm (Fin n))) (flagPsiAux n k x)
      = flagPsiAux n k ((MvPolynomial.rename (σ : Equiv.Perm (Fin n))) x) := by
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, flagPsiAux_rename_comm]
  rw [h, hx σ]

/-- The subalgebra `K(GL(n)/P) ⊗_ℤ ℚ` of `K(GL(n)/B) ⊗_ℤ ℚ`. -/
@[expose] public noncomputable def ParabSubalgebra (blockOf : Fin n → β) : Subalgebra ℚ (KFlag n) :=
  ParabSubalgebraAux blockOf

/-- The subalgebra `K(GL(n)/P) ⊗_ℤ ℚ` is closed under the `ψ^k`s -/
public theorem parabSubalgebra_psi_mem (blockOf : Fin n → β) (k : ℕ) :
    ∀ x ∈ ParabSubalgebra blockOf, AdamsOperations.ψ (R := ℚ) k x ∈ ParabSubalgebra blockOf :=
  parabSubalgebraAux_psi_mem blockOf k

/-- `K(G/P) ⊗ ℚ` inherits Adams operations from `K(G/B) ⊗ ℚ = KFlag n` via
`AdamsOperations.restrict` -/
public noncomputable instance parabAdamsOperations (blockOf : Fin n → β) :
    AdamsOperations ℚ (ParabSubalgebra blockOf) :=
  AdamsOperations.restrict (ParabSubalgebra blockOf) (parabSubalgebra_psi_mem blockOf)
