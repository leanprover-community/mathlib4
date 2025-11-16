/-
Copyright (c) 2025 Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Junyan Xu
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Lüroth's theorem

The goal of this project is to prove Lüroth's theorem, which says that for every field K,
every intermediate field between K and the rational function field K(X) is either K or
isomorphic to K(X) as an K-algebra. The proof depends on the following lemma on degrees of
rational functions:

If `f` is a rational function, i.e. an element in the field `K(X)` (`FractionRing K[X]`)
for some field `K`, we can write `f = p / q` where `p` and `q` are coprime polynomials in `K[X]`
with `q` nonzero.

We define the degree of `f` to be the larger of the degrees (`Polynomial.natDegree`)
of `p` and `q`. It turns out that if `f` is not a constant, its degree is equal to the degree of
the field extension K(X)/K(f) (`Module.finrank K⟮f⟯ (FractionRing K[X])`).

(In fact, since `finrank` is defined to be 0 when the extension is infinite,
the equality continue to hold even when `f` is a constant.)

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Springer, 2003, Proposition 11.3.1.
- N. Jacobson, *Basic Algebra II: Second Edition*, 1989 (Dover edition 2009), Theorem 8.38.

-/

variable {K : Type*} [Field K]

open Polynomial IntermediateField

namespace Polynomial

noncomputable section

variable (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) (coprime : IsCoprime p q)
include hp hq coprime

local notation:10000 K"(X)" => FractionRing K[X]

abbrev toRatFunc : K[X] →+* K(X) := algebraMap ..

set_option quotPrecheck false

/- `f = p / q` -/
local notation "f" => p.toRatFunc / q.toRatFunc

/- `X` considered as an element in K(X). -/
local notation "rfX" => toRatFunc (K := K) X

/- First show that `X` generates K(X) over K(f). -/
theorem adjoin_X_eq_top : K⟮f⟯⟮rfX⟯ = ⊤ := by
  sorry

/- Since `X` generates K(X) over K(f), the degree of the field extension K(X)/K(f) is equal to
the degree of the minimal polynomial of `X` over K(f). `p - f * q` is the obvious candidate for
the minimal polynomial of `X` (where `p` and `q` are considered as elements of K(f)[X] rather than
K[X], and `f` considered as an element of K(f)). First show that X is indeed a root of `p - f * q`,
and therefore K(X) is algebraic over K(f): -/

def minpolyDiv : K⟮f⟯[X] :=
  p.map (algebraMap K K⟮f⟯) - C (AdjoinSimple.gen K f) * q.map (algebraMap K K⟮f⟯)

omit hp coprime in
theorem minpolyDiv_aeval : (minpolyDiv p q).aeval rfX = 0 := by
  have toRatFunc_ne_zero : q.toRatFunc ≠ 0 :=
    (map_ne_zero_iff _ <| IsFractionRing.injective _ _).mpr hq
  simp only [minpolyDiv, aeval_sub, aeval_map_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen]
  simp_rw [aeval_algebraMap_apply, aeval_X_left_apply, div_mul_cancel₀ _ toRatFunc_ne_zero]
  exact sub_self ((algebraMap K[X] K(X)) p)

-- Note: this needs f is not a constant, i.e. `max p.natDegree q.natDegree ≠ 0`.
theorem isAlgebraic_div : IsAlgebraic K⟮f⟯ rfX := by
  use minpolyDiv p q
  refine ⟨?_, minpolyDiv_aeval p q hq⟩
  sorry

theorem isAlgebraic_adjoin_div : Algebra.IsAlgebraic K⟮f⟯ K(X) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮rfX⟯ := by
    apply IntermediateField.isAlgebraic_adjoin_simple
    rw [←isAlgebraic_iff_isIntegral]
    exact isAlgebraic_div p q hp hq coprime
  exact ((IntermediateField.equivOfEq (adjoin_X_eq_top p q hp hq coprime)).trans
    IntermediateField.topEquiv).isAlgebraic

/- Hints:

* `IntermediateField.isAlgebraic_adjoin` and `isAlgebraic_iff_isIntegral` together with
  `minpolyDiv_aeval` shows that `K⟮f⟯⟮rfX⟯` is algebraic over `K⟮f⟯`.

* Now use `IntermediateField.equivOfEq` and `IntermediateField.topEquiv` to construct an `AlgHom`
  between `K⟮f⟯⟮rfX⟯` and K(X), and use `AlgEquiv.isAlgebraic` to conclude. -/

theorem finrank_eq_natDegree_minpoly :
    Module.finrank K⟮f⟯ K(X) = (minpoly K⟮f⟯ rfX).natDegree :=
  sorry -- use `IntermediateField.adjoin.finrank`

theorem transcendental_polynomial : Algebra.Transcendental K K(X) := by
  sorry -- show that `rfX` is a transcendental element

theorem transcendental_adjoin_div : Algebra.Transcendental K K⟮f⟯ := by
  sorry -- argue by contradiction,
  -- using `transcendental_polynomial`, `isAlgebraic_adjoin_div` and `Algebra.IsAlgebraic.trans`

theorem transcendental_div : Transcendental K f := by
  sorry -- argue by contradiction using `IntermediateField.isAlgebraic_adjoin`

local notation "K[f]" => Algebra.adjoin K {f}

def algEquivOfTranscendental : K[X] ≃ₐ[K] K[f] :=
  sorry -- use `AlgEquiv.ofBijective`:
  -- `transcendental_div` and `transcendental_iff_injective` gives injectivity

lemma algEquivOfTranscendental_apply_X :
    algEquivOfTranscendental p q X = ⟨f, Algebra.subset_adjoin rfl⟩ := by
  sorry

#synth EuclideanDomain K[X] -- Polynomial.instEuclideanDomain
example : IsIntegrallyClosed K[X] := inferInstance

/- Since K[f] is isomorphic to K[X] and K[X] is integrally closed, K[f] is also integrally closed.
-/
theorem isIntegrallyClosed_adjoin_div : IsIntegrallyClosed K[f] := by
  sorry -- use `IsIntegrallyClosed.of_equiv`

/- If `p.natDegree > q.natDegree`, then `minpolyDiv p q` has degree equal to the degree of `p`.
If moreover `p` is monic, then `minpolyDiv p q` is also monic. For convenience, we shall assume
these conditions henceforth. -/

variable (lt : q.natDegree < p.natDegree)
include lt

theorem natDegree_minpolyDiv : (minpolyDiv p q).natDegree = p.natDegree := by
  sorry

variable (monic : p.Monic)
include monic

theorem monic_minpolyDiv : (minpolyDiv p q).Monic := by
  sorry

/- By `minpoly.eq_iff_aeval_eq_zero`, to show that `minpolyDiv p q` is indeed the minimal
polynomial of X over K(f), it suffices to show it is irreducible.
The key lemma `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (due to Gauss)
shows that it suffices to show it is irreducible over K[f]. -/

/-- Same as `minpolyDiv` but as a polynomial over K[f] instead of K(f). -/
def minpolyDiv' : K[f][X] :=
  p.map (algebraMap ..) - C ⟨f, Algebra.subset_adjoin rfl⟩ * q.map (algebraMap ..)

open scoped IntermediateField.algebraAdjoinAdjoin
#synth Algebra K[f] K⟮f⟯

theorem map_minpolyDiv' : (minpolyDiv' p q).map (algebraMap ..) = minpolyDiv p q := by
  sorry

/- If we swap the two variables `f` and `X`, then `p - C f * q` becomes `C p - f * C q`. -/

def swap : K[X][X] ≃+* K[X][X] :=
  .ofRingHom (eval₂RingHom (mapRingHom C) (C X)) (eval₂RingHom (mapRingHom C) (C X))
    (by ext <;> simp) (by ext <;> simp)

theorem algEquivOfTranscendental_swap_C_sub_C_X :
    map (algEquivOfTranscendental p q) (swap (C p - C q * X)) = minpolyDiv' p q := by
  sorry

theorem irreducible_mul_X_sub : Irreducible (C p - C q * X) := by
  sorry
  -- use `Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective` with `φ = toRatFunc`.
  -- `C p - C q * X` is primitive because `p` and `q` are coprime.
  -- `(C p - C q * X).map φ` is irreducible by `Polynomial.irreducible_of_degree_eq_one`.

theorem irreducible_minpolyDiv' : Irreducible (minpolyDiv' p q) := by
  sorry -- use `MulEquiv.irreducible_iff`

theorem irreducible_minpolyDiv : Irreducible (minpolyDiv p q) := by
  sorry -- `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`

theorem minpolyDiv_eq_minpoly : minpolyDiv p q = minpoly K⟮f⟯ rfX := by
  sorry -- use `minpoly.eq_iff_aeval_eq_zero`

-- Finally we conclude:
theorem finrank_eq_max_natDegree : Module.finrank K⟮f⟯ K(X) = max p.natDegree q.natDegree :=
  sorry

/- Next steps:

* Remove the condition `p.Monic`: dividing `p` by the leading coefficient does not change the
  degree, and does not affect the intermediate field generated by `f`.

* Remove the condition `q.natDegree < p.natDegree`: if `p.natDegree < q.natDegree`, notice that
  `q / p` generates the same intermediate field as `p / q`. If `p.natDegree = q.natDegree`,
  notice that `(p - c * q) / q` generates the same intermediate field, and you can choose `c`
  such that `p - c * q` has a lower degree.
  It can happen that both `p` and `q` are constants (i.e. of degree 0), in which case
  `K⟮f⟯ = ⊥` and [K(X) : K⟮f⟯] = ∞, but in Lean we have `Module.finrank K⟮f⟯ K(X) = 0`.

* Also remove these conditions from `transcendental_div`.

* Now we are ready to attack Lüroth's theorem.
  Let `E` be an intermediate field between `K` and `K(X)`,
  we must show that `E = K⟮f⟯` for some `f : K(X)` transcendental over `K`. -/

end

end Polynomial

open Polynomial

local notation:10000 K"(X)" => FractionRing K[X]

theorem FractionRing.exists_isCoprime_eq_div (f : K(X)) :
    ∃ p q : K[X], IsCoprime p q ∧ f = p.toRatFunc / q.toRatFunc := by
  sorry

/- First it is easy to show that `K(X)` does not contain any algebraic element over `K` other than
elements of `K`. Proof: use (a generalized version of) `transcendental_div`.
Potentially useful: `Localization.rec` and `FractionRing.mk_eq_div`. -/
instance : IsIntegrallyClosedIn K K(X) := by
  sorry

variable (E : IntermediateField K K(X)) (hE : E ≠ ⊥)
include hE

instance : Algebra.IsAlgebraic E K(X) := by
  sorry
  -- Choose `f ∈ E \ K`, then `K(X)` is algebraic over `K⟮f⟯`, and therefore algebraic over `E`.

/-- The minimal polynomial of `X : K(X)` over an intermediate field `E`. -/
def IntermediateField.minpolyX : E[X] :=
  minpoly E (X : K[X]).toRatFunc

-- TODO: fill in more details here from [Cohn] and [Jacobson]

theorem luroth : ∃ f : K(X), Transcendental K f ∧ E = K⟮f⟯ := by
  sorry
