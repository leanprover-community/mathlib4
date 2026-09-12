/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.RingTheory.LambdaRing.SymmetricFunctions
public import Mathlib.RingTheory.LambdaRing.PrimeExtend

/-!
# Adams operations, plethystic composition, and the λ-ring structure on `Λ_R`

A *λ-ring* is a commutative ring equipped with operations
`λⁿ` satisfying axioms modeled on exterior powers, with `λⁿ(x + y)`.
Over a `ℚ`-algebra, this data is *equivalent* to a family of `R`-algebra endomorphisms `ψⁿ`, the
**Adams operations**, satisfying `ψ¹ = id` and `ψᵐ ∘ ψⁿ = ψ^(mn)` — related to `λⁿ` via Newton's
identities. This file formalizes those Adams-operation axioms.


The file has two parts, in dependency order:

1. **`Λ_R`** having its own Adams operations and plethystic composition.
   `ψⁿ(p_k) = p_{nk}` on `Λ_R` itself, and *plethystic composition* `comp f g := f[g]`
2. **`Λ_R` acting on any `AdamsOperations` ring**
   In the general class, and the action of `Λ_R` on any `R`-algebra carrying `ψ^n` operations.
   This is exactly the *plethystic* formulation of what a λ-ring is,
   (a la Getzler)
-/

/-- A commutative `R`-algebra equipped with Adams operations:
`R`-algebra endomorphisms `ψ n` for each `n : ℕ`,
Each `ψ n` is required to be an `AlgHom`.

`ψ_one`/`ψ_mul` alone are not enough over a general commutative ring
in order to guarantee `ψ` that actually provides the structure of a λ-ring.
The extra axiom `ψ_prime_congr` is the Wilkerson congruence.
In most cases `p` will be a unit and so that divisiblity condition is vacuous,
but it is necessary in general. -/
public class AdamsOperations
  (R A : Type*)
  [CommRing R]
  [CommRing A] [Algebra R A] where
  /-- The `n`-th Adams operation, as an `R`-algebra endomorphism. -/
  ψ : ℕ → A →ₐ[R] A
  ψ_one : ψ 1 = AlgHom.id R A
  ψ_mul : ∀ {m n : ℕ}, 0 < m → 0 < n → ψ (m * n) = (ψ m).comp (ψ n)
  /-- Wilkerson's congruence: `ψ p x ≡ x ^ p (mod p A)`, for every prime `p`.
  Easy whenever `p` is a unit in `A` which is assumed for most other parts
  of this folder -/
  ψ_prime_congr : ∀ p : ℕ, p.Prime → ∀ x : A, (p : A) ∣ (ψ p x - x ^ p)

/-- Whenever `A` is an `R`-algebra with `R` a `ℚ`-algebra for `(p : ℕ)`
the included `(p : A)` is a unit. -/
public theorem isUnit_natCast_of_algebra_rat {R A : Type*} [CommRing R] [Algebra ℚ R] [CommRing A]
    [Algebra R A] {p : ℕ} (hp : p ≠ 0) : IsUnit ((p : A)) := by
  have hQ : IsUnit ((p : ℚ)) := (Nat.cast_ne_zero.mpr hp).isUnit
  have hR : IsUnit ((p : R)) := by
    rw [← map_natCast (algebraMap ℚ R)]
    exact hQ.map (algebraMap ℚ R)
  rw [← map_natCast (algebraMap R A)]
  exact hR.map (algebraMap R A)

/-- Build an `AdamsOperations` instance by supplying only the Adams operations *at the primes*,
- `ψPrime : Nat.Primes → A →ₐ[R] A`
- a proof that they pairwise commute
- a proof of Wilkerson's congruence
The value of `ψ^n` at every other `n` is via unique factorization. -/
@[instance_reducible] public noncomputable def AdamsOperations.ofPrimes
  {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ψPrime : Nat.Primes → A →ₐ[R] A)
    (hcomm : ∀ p q : Nat.Primes, Commute (ψPrime p) (ψPrime q))
    (hcongr : ∀ p : Nat.Primes, ∀ x : A, (p : A) ∣ (ψPrime p x - x ^ (p : ℕ))) :
    AdamsOperations R A where
  ψ := PrimeExtend.extendPrimes ψPrime hcomm
  ψ_one := PrimeExtend.extendPrimes_one ψPrime hcomm
  ψ_mul hm hn := PrimeExtend.extendPrimes_mul ψPrime hcomm hm hn
  ψ_prime_congr p hp x := by
    rw [PrimeExtend.extendPrimes_prime ψPrime hcomm p hp]
    exact hcongr ⟨p, hp⟩ x

namespace SymmFun

/-! ## Part 1: `Λ_R` acting on itself -/

section SelfAction

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The `n`-th Adams operation on `Λ_R`, rescaling power-sum indices:
`ψⁿ(p_k) = p_{nk}`. -/
public noncomputable def psi (n : ℕ) : SymmFun R →ₐ[R] SymmFun R :=
  MvPolynomial.aeval fun k => (MvPolynomial.X (n * (k + 1) - 1) : SymmFun R)

theorem psi_apply_X (n k : ℕ) :
    psi n (MvPolynomial.X k : SymmFun R) = (MvPolynomial.X (n * (k + 1) - 1) : SymmFun R) :=
  MvPolynomial.aeval_X _ _

/-- The particular evaluation of `ψ^n (p_k)` -/
@[simp]
public theorem psi_p (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    psi n (p k hk : SymmFun R) = p (n * k) (Nat.mul_pos hn hk) := by
  rw [p_def, psi_apply_X, p_def]
  congr 1
  rw [Nat.sub_add_cancel hk]

/-- `ψ^1` is the identity -/
public theorem psi_one : (psi 1 : SymmFun R →ₐ[R] SymmFun R) = AlgHom.id R (SymmFun R) := by
  ext1 k
  simp [psi_apply_X]

/-- `ψ^{mn}` is the composition of `ψ^m` and `ψ^n` -/
public theorem psi_mul {m n : ℕ} (_hm : 0 < m) (hn : 0 < n) :
    (psi (m * n) : SymmFun R →ₐ[R] SymmFun R) = (psi m).comp (psi n) := by
  ext1 k
  simp only [AlgHom.comp_apply, psi_apply_X]
  have h1 : 0 < n * (k + 1) := Nat.mul_pos hn (Nat.succ_pos k)
  rw [Nat.sub_add_cancel h1, ← mul_assoc]

/-- Plethystic composition on `Λ_R`: `comp f g := f[g]`
i.e. substitute `ψ^n g` for every power sum `p_n` appearing in `f`. -/
@[expose] public noncomputable def comp (f g : SymmFun R) : SymmFun R :=
  MvPolynomial.aeval (fun n => psi (n + 1) g) f

theorem comp_apply_X (k : ℕ) (g : SymmFun R) : comp (MvPolynomial.X k) g = psi (k + 1) g :=
  MvPolynomial.aeval_X _ _

/-- `(ψ^n g)[h]` = `ψ^n g[h]` -/
public theorem comp_psi (h : SymmFun R) (n : ℕ) (hn : 0 < n) (g : SymmFun R) :
    comp (psi n g) h = psi n (comp g h) := by
  suffices heq : (MvPolynomial.aeval (fun k => psi (k + 1) h) : SymmFun R →ₐ[R] SymmFun R).comp
      (psi n) = (psi n).comp (MvPolynomial.aeval fun k => psi (k + 1) h) by
    exact congrFun (congrArg DFunLike.coe heq) g
  ext1 j
  simp only [AlgHom.comp_apply, psi_apply_X, MvPolynomial.aeval_X]
  rw [Nat.sub_add_cancel (Nat.mul_pos hn (Nat.succ_pos j)), psi_mul hn (Nat.succ_pos j),
    AlgHom.comp_apply]

/-- **Plethystic composition is associative**: `(f ∘ g) ∘ h = f ∘ (g ∘ h)`. -/
public theorem comp_assoc (f g h : SymmFun R) : comp (comp f g) h = comp f (comp g h) := by
  suffices heq : (MvPolynomial.aeval (fun n => psi (n + 1) h) : SymmFun R →ₐ[R] SymmFun R).comp
      (MvPolynomial.aeval fun n => psi (n + 1) g)
      = MvPolynomial.aeval fun n => psi (n + 1) (comp g h) by
    exact congrFun (congrArg DFunLike.coe heq) f
  ext1 k
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  exact comp_psi h (k + 1) (Nat.succ_pos k) g

/-- `p_1 [g] = g`. -/
public theorem comp_p_one_left (g : SymmFun R) : comp (p 1 Nat.one_pos) g = g := by
  change MvPolynomial.aeval (fun n => psi (n + 1) g) (p 1 Nat.one_pos : SymmFun R) = g
  rw [p_def, MvPolynomial.aeval_X]
  change psi 1 g = g
  rw [psi_one, AlgHom.id_apply]

/-- `f[p_1] = f`. -/
public theorem comp_p_one_right (f : SymmFun R) : comp f (p 1 Nat.one_pos) = f := by
  change MvPolynomial.aeval (fun n => psi (n + 1) (p 1 Nat.one_pos : SymmFun R)) f = f
  have hid : (MvPolynomial.aeval (fun n => psi (n + 1) (p 1 Nat.one_pos : SymmFun R))
      : SymmFun R →ₐ[R] SymmFun R) = AlgHom.id R (SymmFun R) := by
    ext1 n
    rw [MvPolynomial.aeval_X, AlgHom.id_apply, p_def, psi_apply_X]
    congr 1
    omega
  rw [hid, AlgHom.id_apply]

/-- `Λ_R` has the structure of an `AdamsOperation` ring -/
public noncomputable instance : AdamsOperations R (SymmFun R) where
  ψ := psi
  ψ_one := psi_one
  ψ_mul := psi_mul
  ψ_prime_congr _p hp _ := (isUnit_natCast_of_algebra_rat (R := R) (A := SymmFun R) hp.pos.ne').dvd

end SelfAction

/-! ## Part 2: `Λ_R` acting on any `AdamsOperations` ring -/

section GeneralAction

variable {R : Type*} [CommRing R] [Algebra ℚ R]

variable {A : Type*} [CommRing A] [Algebra R A] [AdamsOperations R A]

/-- The action of `Λ_R` on any `R`-algebra `A` with `AdamsOperations`.
For `a : A`, `act a : SymmFun R →ₐ[R] A` sends `p_n ↦ ψⁿ(a)`,
and from that extended to all of `SymmFun R`. -/
@[expose] public noncomputable def act (a : A) : SymmFun R →ₐ[R] A :=
  MvPolynomial.aeval fun n => AdamsOperations.ψ (R := R) (n + 1) a

theorem act_apply_X (a : A) (n : ℕ) :
    act a (MvPolynomial.X n : SymmFun R) = AdamsOperations.ψ (R := R) (n + 1) a :=
  MvPolynomial.aeval_X _ _

/-- On `p_n` in `SymmFun R`, `act a` as an algebra homomorphism
with that as it's domain has value `ψ^n (a)` as required. -/
@[simp]
public theorem act_p (a : A) (n : ℕ) (hn : 0 < n) :
    act a (p n hn : SymmFun R) = AdamsOperations.ψ (R := R) n a := by
  rw [p_def, act_apply_X, Nat.sub_add_cancel hn]

/-- On `p_1` in `SymmFun R`, `act a` as an algebra homomorphism
with that as it's domain has value `ψ^1 (a) = a` as required. -/
public theorem act_p_one (a : A) : act a (p 1 Nat.one_pos : SymmFun R) = a := by
  rw [act_p a 1 Nat.one_pos, AdamsOperations.ψ_one (R := R), AlgHom.id_apply]

/-- `f[x+y] = Σ f₍₁₎[x] · f₍₂₎[y]` where
`Δf = Σ f₍₁₎⊗f₍₂₎` is `Λ_R`'s comultiplication.
This is the λ-ring axiom `λⁿ(x+y) = Σᵢ₊ⱼ₌ₙ λⁱ(x)λʲ(y)`
but with `p_n` and `ψ^n` instead of `e_n` and `λ^n` -/
public theorem act_add (x y : A) (f : SymmFun R) :
    act (x + y) f =
      Algebra.TensorProduct.lmul' R
        (Algebra.TensorProduct.map (act x) (act y) (Coalgebra.comul (R := R) f)) := by
  suffices h : act (x + y) = (Algebra.TensorProduct.lmul' R).comp
      ((Algebra.TensorProduct.map (act x) (act y)).comp
        (Bialgebra.comulAlgHom R (SymmFun R))) by
    exact congrFun (congrArg DFunLike.coe h) f
  ext1 k
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_X, map_add,
    Algebra.TensorProduct.map_tmul, act_apply_X, Algebra.TensorProduct.lmul'_apply_tmul,
    map_one, mul_one, one_mul]

/--
`pₘ[xy] = pₘ[x]·pₘ[y]`, i.e. `ψᵐ(xy) = ψᵐ(x)ψᵐ(y)`
This is the content of the λ-ring axiom `λⁿ(xy) = Pₙ(λ¹(x),…,λⁿ(x),λ¹(y),…,λⁿ(y))`
via Grothendieck's universal polynomials `Pₙ` — which this file does not construct. -/
public theorem act_mul_p (x y : A) (m : ℕ) (hm : 0 < m) :
    act (x * y) (p m hm : SymmFun R) = act x (p m hm : SymmFun R) * act y (p m hm : SymmFun R) := by
  simp only [act_p, map_mul]

/-- At `A = SymmFun R`, `act` is exactly plethystic composition. -/
public theorem act_eq_comp (f g : SymmFun R) : act g f = comp f g := rfl

/-- For `a : A`, sending `p_l ↦ ψ^l (a)` and extending to all of `SymmFun R`
means that on `ψ^n g` for in `g ∈ SymmFun R` is the same as doing it on `g` directly
and then applying `ψ^n`.
-/
public theorem act_psi (a : A) (n : ℕ) (hn : 0 < n) (g : SymmFun R) :
    act a (psi n g) = AdamsOperations.ψ (R := R) n (act a g) := by
  suffices h : (act a).comp (psi n) = (AdamsOperations.ψ (R := R) n).comp (act a) by
    exact congrFun (congrArg DFunLike.coe h) g
  ext1 j
  simp only [AlgHom.comp_apply, psi_apply_X, act_apply_X]
  rw [Nat.sub_add_cancel (Nat.mul_pos hn (Nat.succ_pos j)),
    AdamsOperations.ψ_mul (R := R) hn (Nat.succ_pos j), AlgHom.comp_apply]

/-- **The general-`A` counterpart of `comp_assoc`**
(f \circ g) \circ a = f ∘ (g ∘ a) -/
public theorem act_comp (a : A) (f g : SymmFun R) :
  act a (act g f) = act (act a g) f := by
  suffices h : (act a).comp (act g) = act (act a g) by
    exact congrFun (congrArg DFunLike.coe h) f
  ext1 k
  simp only [AlgHom.comp_apply, act_apply_X]
  exact act_psi a (k + 1) (Nat.succ_pos k) g

/-- Sanity check: `act_comp` at `A = SymmFun R` does specialize to `comp_assoc`. -/
example (f g h : SymmFun R) : comp (comp f g) h = comp f (comp g h) := by
  simpa only [act_eq_comp] using act_comp h f g

end GeneralAction

end SymmFun
