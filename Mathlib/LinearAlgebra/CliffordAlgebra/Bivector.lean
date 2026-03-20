/-
Copyright (c) 2026 Ian Michael Arnoldy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Michael Arnoldy
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Multivectors and bivectors in Clifford algebras

The grade-$n$ elements ($n$-vectors) of a Clifford algebra form a
submodule. When $n = 2$, these are the bivectors, and they form a
Lie subalgebra under the commutator bracket. This gives the standard
construction of the orthogonal Lie algebra $\mathfrak{so}(Q)$
from the Clifford algebra $\mathrm{Cl}(Q)$.

An $n$-vector is a finite sum of products of $n$ copies of $\iota$:
$\iota(m_1) \cdots \iota(m_n)$ for $m_1, \ldots, m_n \in M$. The
key fact for bivectors ($n = 2$) is that the commutator of two such
products is again a linear combination of bivectors, using the
Clifford relation $\iota(m) \cdot \iota(m) = Q(m)$.

## Main definitions

* `CliffordAlgebra.nvector`: the `Submodule R (CliffordAlgebra Q)`
  of grade-$n$ elements, spanned by products
  $\iota(m_1) \cdots \iota(m_n)$.
* `CliffordAlgebra.bivector`: abbreviation for `nvector 2 Q`, the
  submodule spanned by products $\iota(m_1) \cdot \iota(m_2)$.
* `CliffordAlgebra.bivectorLieSubalgebra`: the `LieSubalgebra`
  of bivectors under the commutator bracket.

## Main results

* `CliffordAlgebra.mem_nvector`: characterization of membership
  in `nvector n Q`.
* `CliffordAlgebra.ι_mul_ι_mem_bivector`: a product
  $\iota(m_1) \cdot \iota(m_2)$ lies in the bivector submodule.
* `CliffordAlgebra.lie_ι_mul_ι`: the explicit commutator formula
  for two bivectors.
* `CliffordAlgebra.lie_mem_bivector`: closure of the bivector
  submodule under the Lie bracket.
* `CliffordAlgebra.bivector_le_evenOdd_zero`: bivectors lie
  in the even part of the Clifford algebra.

## Implementation notes

The Clifford algebra `CliffordAlgebra Q` is a `Ring`, hence gets
a `LieRing` instance via `LieRing.ofAssociativeRing` with bracket
$[x, y] = x y - y x$. Similarly, `Algebra R (CliffordAlgebra Q)`
gives `LieAlgebra R (CliffordAlgebra Q)` for free.

We define `nvector n Q` as the span of ordered products of `n`
copies of `ι`, represented via `(List.ofFn f).prod` for
`f : Fin n → M`. The case `n = 2` recovers the bivector submodule,
upgraded to a `LieSubalgebra` after proving bracket closure. The
closure proof reduces to generators via `Submodule.span_induction₂`
and then applies the explicit commutator formula.

`QuadraticMap.polar` appears in the commutator formula because
`QuadraticForm R M` is a reducible abbreviation for
`QuadraticMap R M R`, and the polar form is defined on the
general `QuadraticMap`.

## Tags

Clifford algebra, multivector, bivector, Lie algebra, orthogonal
-/

@[expose] public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (Q : QuadraticForm R M)

/-- The `LieModule` instance for the Clifford algebra acting on
itself. Provided explicitly because automatic synthesis exceeds
the default heartbeat limit for the deep instance chain through
`CliffordAlgebra → Algebra → Ring → LieRing → LieModule`.
This may warrant an upstream fix. -/
instance instLieModuleSelf : LieModule R
    (CliffordAlgebra Q) (CliffordAlgebra Q) :=
  lieAlgebraSelfModule

section NVector

/-- The submodule of grade-$n$ elements ($n$-vectors) in a
Clifford algebra, spanned by ordered products
$\iota(m_1) \cdots \iota(m_n)$ for $m_1, \ldots, m_n \in M$. -/
def nvector (n : ℕ) : Submodule R (CliffordAlgebra Q) :=
  Submodule.span R
    {x : CliffordAlgebra Q |
      ∃ ms : Fin n → M,
        x = (List.ofFn (fun i => ι Q (ms i))).prod}

/-- Characterization of membership in `nvector n Q`. -/
@[simp]
theorem mem_nvector (n : ℕ) (x : CliffordAlgebra Q) :
    x ∈ nvector Q n ↔
    x ∈ Submodule.span R
      {y | ∃ ms : Fin n → M,
        y = (List.ofFn (fun i => ι Q (ms i))).prod} :=
  Iff.rfl

/-- An ordered product $\iota(m_0) \cdots \iota(m_{n-1})$ lies
in the $n$-vector submodule. -/
theorem prod_ι_mem_nvector (n : ℕ) (ms : Fin n → M) :
    (List.ofFn (fun i => ι Q (ms i))).prod ∈
    nvector Q n :=
  Submodule.subset_span ⟨ms, rfl⟩

end NVector

section Bivector

/-- The submodule of bivectors in a Clifford algebra, defined as
`nvector 2 Q`, spanned by products $\iota(m_1) \cdot \iota(m_2)$
for $m_1, m_2 \in M$. -/
def bivector : Submodule R (CliffordAlgebra Q) :=
  nvector Q 2

/-- A product of two `ι` applications equals the `List.ofFn`
product for `Fin 2`. Used to convert between pair form and
`nvector 2` generators. -/
private theorem nvector_two_prod (ms : Fin 2 → M) :
    (List.ofFn (fun i : Fin 2 => ι Q (ms i))).prod =
    ι Q (ms 0) * ι Q (ms 1) := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp [List.prod_cons, List.prod_nil]

/-- A product $\iota(m_1) \cdot \iota(m_2)$ lies in the
bivector submodule. -/
@[simp]
theorem ι_mul_ι_mem_bivector (m₁ m₂ : M) :
    ι Q m₁ * ι Q m₂ ∈ bivector Q := by
  have : ι Q m₁ * ι Q m₂ =
      (List.ofFn (fun i : Fin 2 =>
        ι Q (![m₁, m₂] i))).prod := by
    rw [nvector_two_prod]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [this]
  exact prod_ι_mem_nvector Q 2 ![m₁, m₂]

/-- Characterization of membership in `bivector Q` in terms of
the pair-form spanning set. -/
@[simp]
theorem mem_bivector (x : CliffordAlgebra Q) :
    x ∈ bivector Q ↔
    x ∈ Submodule.span R
      {y | ∃ m₁ m₂ : M, y = ι Q m₁ * ι Q m₂} := by
  constructor
  · intro hx
    refine Submodule.span_le.mpr ?_ hx
    rintro y ⟨ms, rfl⟩
    rw [nvector_two_prod]
    exact Submodule.subset_span ⟨ms 0, ms 1, rfl⟩
  · intro hx
    refine Submodule.span_le.mpr ?_ hx
    rintro y ⟨m₁, m₂, rfl⟩
    exact ι_mul_ι_mem_bivector Q m₁ m₂

/-- Zero lies in the bivector submodule. -/
theorem zero_mem_bivector :
    (0 : CliffordAlgebra Q) ∈ bivector Q :=
  (bivector Q).zero_mem

/-- Every bivector lies in the even part of the Clifford
algebra, i.e., in `evenOdd Q 0`. -/
theorem bivector_le_evenOdd_zero :
    bivector Q ≤ evenOdd Q 0 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨ms, rfl⟩
  rw [nvector_two_prod]
  exact ι_mul_ι_mem_evenOdd_zero Q (ms 0) (ms 1)

end Bivector

section Commutator

variable {Q}

/-- Subtraction form of the Clifford anticommutation relation:
$\iota(b) \cdot \iota(a) =
\operatorname{algebraMap}(\operatorname{polar}(Q)(a, b))
- \iota(a) \cdot \iota(b)$.
This is `CliffordAlgebra.ι_mul_ι_comm` with the arguments to
$\iota$ swapped (and `polar` symmetry applied). -/
theorem ι_mul_ι_comm' (a b : M) :
    ι Q b * ι Q a =
    algebraMap R _ (QuadraticMap.polar Q a b) -
    ι Q a * ι Q b :=
  eq_sub_of_add_eq' (ι_mul_ι_add_swap a b)

/-- Expansion of $\iota(a)\iota(b) \cdot \iota(c)\iota(d)$ via
Clifford swap relations. The residual term
$\iota(c)\iota(a) \cdot \iota(b)\iota(d)$ cancels against the
corresponding term in `mul_ι_mul_ι_right`. -/
private theorem mul_ι_mul_ι_left (a b c d : M) :
    ι Q a * ι Q b * (ι Q c * ι Q d) =
    algebraMap R _ (QuadraticMap.polar Q b c) *
      (ι Q a * ι Q d) -
    algebraMap R _ (QuadraticMap.polar Q a c) *
      (ι Q b * ι Q d) +
    ι Q c * ι Q a * (ι Q b * ι Q d) := by
  rw [mul_assoc (ι Q a) (ι Q b),
      ← mul_assoc (ι Q b) (ι Q c) (ι Q d),
      ι_mul_ι_comm b c, sub_mul, mul_sub (ι Q a),
      ← mul_assoc (ι Q a) (algebraMap R _ _) (ι Q d),
      ← Algebra.commutes
        (QuadraticMap.polar Q b c) (ι Q a),
      mul_assoc (algebraMap R _ _) (ι Q a) (ι Q d),
      ← mul_assoc (ι Q a) (ι Q c * ι Q b) (ι Q d),
      ← mul_assoc (ι Q a) (ι Q c) (ι Q b),
      mul_assoc (ι Q a * ι Q c) (ι Q b) (ι Q d),
      ι_mul_ι_comm a c, sub_mul, ← sub_add]

/-- Expansion of $\iota(c)\iota(d) \cdot \iota(a)\iota(b)$ via
Clifford swap relations. The residual term
$\iota(c)\iota(a) \cdot \iota(b)\iota(d)$ cancels against the
corresponding term in `mul_ι_mul_ι_left`. -/
private theorem mul_ι_mul_ι_right (a b c d : M) :
    ι Q c * ι Q d * (ι Q a * ι Q b) =
    algebraMap R _ (QuadraticMap.polar Q a d) *
      (ι Q c * ι Q b) -
    algebraMap R _ (QuadraticMap.polar Q b d) *
      (ι Q c * ι Q a) +
    ι Q c * ι Q a * (ι Q b * ι Q d) := by
  rw [mul_assoc (ι Q c) (ι Q d),
      ← mul_assoc (ι Q d) (ι Q a) (ι Q b),
      ι_mul_ι_comm' a d, sub_mul, mul_sub (ι Q c),
      ← mul_assoc (ι Q c) (algebraMap R _ _) (ι Q b),
      ← Algebra.commutes
        (QuadraticMap.polar Q a d) (ι Q c),
      mul_assoc (algebraMap R _ _) (ι Q c) (ι Q b),
      ← mul_assoc (ι Q c) (ι Q a * ι Q d) (ι Q b),
      ← mul_assoc (ι Q c) (ι Q a) (ι Q d),
      mul_assoc (ι Q c * ι Q a) (ι Q d) (ι Q b),
      ι_mul_ι_comm' b d, mul_sub,
      ← Algebra.commutes (QuadraticMap.polar Q b d)
        (ι Q c * ι Q a),
      ← sub_add]

/-- The commutator of two bivector generators expressed as a
linear combination of bivectors:
$[\iota(a)\iota(b),\, \iota(c)\iota(d)] =
  B(b,c)\,\iota(a)\iota(d)
  - B(a,c)\,\iota(b)\iota(d)
  - B(a,d)\,\iota(c)\iota(b)
  + B(b,d)\,\iota(c)\iota(a)$
where $B = \operatorname{polar}(Q)$. -/
theorem lie_ι_mul_ι (a b c d : M) :
    ⁅ι Q a * ι Q b, ι Q c * ι Q d⁆ =
    algebraMap R _ (QuadraticMap.polar Q b c) *
      (ι Q a * ι Q d) -
    algebraMap R _ (QuadraticMap.polar Q a c) *
      (ι Q b * ι Q d) -
    algebraMap R _ (QuadraticMap.polar Q a d) *
      (ι Q c * ι Q b) +
    algebraMap R _ (QuadraticMap.polar Q b d) *
      (ι Q c * ι Q a) := by
  simp only [Bracket.bracket]
  rw [mul_ι_mul_ι_left a b c d,
      mul_ι_mul_ι_right a b c d]
  abel

/-- The commutator of two bivector generators lies in the
bivector submodule. Each term in the commutator formula
`lie_ι_mul_ι` has the form
$\operatorname{algebraMap}(r) \cdot \iota(m_1)\iota(m_2)$,
which lies in `bivector Q` via `Submodule.smul_mem` (since
`algebraMap r * x = r • x` in any `Algebra`). -/
theorem lie_ι_mul_ι_mem_bivector (a b c d : M) :
    ⁅ι Q a * ι Q b, ι Q c * ι Q d⁆ ∈ bivector Q := by
  rw [lie_ι_mul_ι a b c d]
  refine (bivector Q).add_mem ((bivector Q).sub_mem
    ((bivector Q).sub_mem ?_ ?_) ?_) ?_
  all_goals (rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul]; exact (bivector Q).smul_mem _ (ι_mul_ι_mem_bivector Q _ _))

end Commutator

section LieSubalgebra

variable {Q}

/-- The bivector submodule is closed under the Lie bracket.
The proof reduces to generators via `Submodule.span_induction₂`
and applies `lie_ι_mul_ι_mem_bivector` on each pair. -/
theorem lie_mem_bivector {x y : CliffordAlgebra Q}
    (hx : x ∈ bivector Q) (hy : y ∈ bivector Q) :
    ⁅x, y⁆ ∈ bivector Q := by
  rw [mem_bivector] at hx hy
  have hmem : ⁅x, y⁆ ∈ Submodule.span R
      {z | ∃ m₁ m₂ : M, z = ι Q m₁ * ι Q m₂} := by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact (mem_bivector Q _).mp
        (lie_ι_mul_ι_mem_bivector a b c d)
    | zero_left _ _ =>
      rw [zero_lie]; exact Submodule.zero_mem _
    | zero_right _ _ =>
      rw [lie_zero]; exact Submodule.zero_mem _
    | add_left _ _ _ _ _ _ h₁ h₂ =>
      rw [add_lie]; exact Submodule.add_mem _ h₁ h₂
    | add_right _ _ _ _ _ _ h₁ h₂ =>
      rw [lie_add]; exact Submodule.add_mem _ h₁ h₂
    | smul_left r _ _ _ _ h =>
      rw [smul_lie]; exact Submodule.smul_mem _ r h
    | smul_right r _ _ _ _ h =>
      rw [lie_smul]; exact Submodule.smul_mem _ r h
  rwa [← mem_bivector] at hmem

variable (Q) in
/-- The bivectors in a Clifford algebra form a Lie subalgebra
under the commutator bracket $[x, y] = xy - yx$. This gives
the standard construction of $\mathfrak{so}(Q)$ from
$\mathrm{Cl}(Q)$. -/
def bivectorLieSubalgebra :
    LieSubalgebra R (CliffordAlgebra Q) where
  toSubmodule := bivector Q
  lie_mem' := lie_mem_bivector

@[simp]
theorem mem_bivectorLieSubalgebra
    (x : CliffordAlgebra Q) :
    x ∈ bivectorLieSubalgebra Q ↔
    x ∈ bivector Q :=
  Iff.rfl

end LieSubalgebra

end CliffordAlgebra
