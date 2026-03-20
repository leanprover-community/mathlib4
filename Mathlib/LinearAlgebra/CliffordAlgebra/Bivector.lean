/-
Copyright (c) 2026 Ian Michael Arnoldy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Michael Arnoldy
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

/-!
# Bivectors in Clifford algebras

The grade-2 elements (bivectors) of a Clifford algebra form a Lie
subalgebra under the commutator bracket. This gives the standard
construction of the orthogonal Lie algebra $\mathfrak{so}(Q)$
from the Clifford algebra $\mathrm{Cl}(Q)$.

A bivector is a finite sum of products
$\iota(m_1) \cdot \iota(m_2)$ for $m_1, m_2 \in M$. The key
fact is that the commutator of two such products is again a
linear combination of bivectors, using the Clifford relation
$\iota(m) \cdot \iota(m) = Q(m)$.

## Main definitions

* `CliffordAlgebra.bivector`: the `Submodule R (CliffordAlgebra Q)`
  spanned by products $\iota(m_1) \cdot \iota(m_2)$.
* `CliffordAlgebra.bivectorLieSubalgebra`: the `LieSubalgebra`
  of bivectors under the commutator bracket.

## Main results

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

We define bivectors as a `Submodule` and then upgrade to
`LieSubalgebra` after proving bracket closure. The closure proof
reduces to generators via `Submodule.span_induction₂` and then
applies the explicit commutator formula.

`QuadraticMap.polar` appears in the commutator formula because
`QuadraticForm R M` is a reducible abbreviation for
`QuadraticMap R M R`, and the polar form is defined on the
general `QuadraticMap`.

## Tags

Clifford algebra, bivector, Lie algebra, orthogonal
-/

noncomputable section

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

section Bivector

/-- The submodule of bivectors in a Clifford algebra, spanned
by products $\iota(m_1) \cdot \iota(m_2)$
for $m_1, m_2 \in M$. -/
def bivector : Submodule R (CliffordAlgebra Q) :=
  Submodule.span R
    {x : CliffordAlgebra Q |
      ∃ m₁ m₂ : M, x = ι Q m₁ * ι Q m₂}

/-- A product $\iota(m_1) \cdot \iota(m_2)$ lies in the
bivector submodule. -/
@[simp]
theorem ι_mul_ι_mem_bivector (m₁ m₂ : M) :
    ι Q m₁ * ι Q m₂ ∈ bivector Q :=
  Submodule.subset_span ⟨m₁, m₂, rfl⟩

/-- Characterization of membership in `bivector Q`. -/
@[simp]
theorem mem_bivector (x : CliffordAlgebra Q) :
    x ∈ bivector Q ↔
    x ∈ Submodule.span R
      {y | ∃ m₁ m₂ : M, y = ι Q m₁ * ι Q m₂} :=
  Iff.rfl

/-- Zero lies in the bivector submodule. -/
theorem zero_mem_bivector :
    (0 : CliffordAlgebra Q) ∈ bivector Q :=
  (bivector Q).zero_mem

/-- Every bivector lies in the even part of the Clifford
algebra, i.e., in `evenOdd Q 0`. -/
theorem bivector_le_evenOdd_zero :
    bivector Q ≤ evenOdd Q 0 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m₁, m₂, rfl⟩
  exact ι_mul_ι_mem_evenOdd_zero Q m₁ m₂

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
  -- Reassociate to get ι b * ι c adjacent
  conv_lhs => rw [show ι Q a * ι Q b *
    (ι Q c * ι Q d) =
    ι Q a * (ι Q b * ι Q c) * ι Q d
    from by noncomm_ring]
  -- Substitute ι b * ι c = polar(b,c) - ι c * ι b
  rw [ι_mul_ι_comm b c]
  -- Distribute
  conv_lhs => rw [show ι Q a *
    (algebraMap R _ (QuadraticMap.polar Q b c) -
      ι Q c * ι Q b) * ι Q d =
    ι Q a * algebraMap R _
      (QuadraticMap.polar Q b c) * ι Q d -
    ι Q a * (ι Q c * ι Q b) * ι Q d
    from by noncomm_ring]
  -- Move algebraMap past ι a (scalars commute)
  rw [show ι Q a * algebraMap R _
    (QuadraticMap.polar Q b c) =
    algebraMap R _
      (QuadraticMap.polar Q b c) * ι Q a
    from (Algebra.commutes _ _).symm]
  -- Reassociate first term
  rw [show algebraMap R _
    (QuadraticMap.polar Q b c) * ι Q a * ι Q d =
    algebraMap R _
      (QuadraticMap.polar Q b c) *
      (ι Q a * ι Q d) from by noncomm_ring]
  -- Get ι a * ι c adjacent
  rw [show ι Q a * (ι Q c * ι Q b) * ι Q d =
    (ι Q a * ι Q c) * (ι Q b * ι Q d)
    from by noncomm_ring]
  -- Swap ι a * ι c
  rw [ι_mul_ι_comm a c]
  -- Distribute and clean up
  rw [show (algebraMap R _
    (QuadraticMap.polar Q a c) -
      ι Q c * ι Q a) * (ι Q b * ι Q d) =
    algebraMap R _
      (QuadraticMap.polar Q a c) *
      (ι Q b * ι Q d) -
    ι Q c * ι Q a * (ι Q b * ι Q d)
    from by noncomm_ring]
  noncomm_ring

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
  -- Reassociate to get ι d * ι a adjacent
  conv_lhs => rw [show ι Q c * ι Q d *
    (ι Q a * ι Q b) =
    ι Q c * (ι Q d * ι Q a) * ι Q b
    from by noncomm_ring]
  -- Substitute ι d * ι a = polar(a,d) - ι a * ι d
  rw [ι_mul_ι_comm' a d]
  -- Distribute
  conv_lhs => rw [show ι Q c *
    (algebraMap R _ (QuadraticMap.polar Q a d) -
      ι Q a * ι Q d) * ι Q b =
    ι Q c * algebraMap R _
      (QuadraticMap.polar Q a d) * ι Q b -
    ι Q c * (ι Q a * ι Q d) * ι Q b
    from by noncomm_ring]
  -- Move algebraMap past ι c (scalars commute)
  rw [show ι Q c * algebraMap R _
    (QuadraticMap.polar Q a d) =
    algebraMap R _
      (QuadraticMap.polar Q a d) * ι Q c
    from (Algebra.commutes _ _).symm]
  -- Reassociate first term
  rw [show algebraMap R _
    (QuadraticMap.polar Q a d) * ι Q c * ι Q b =
    algebraMap R _
      (QuadraticMap.polar Q a d) *
      (ι Q c * ι Q b) from by noncomm_ring]
  -- Get ι d * ι b adjacent
  rw [show ι Q c * (ι Q a * ι Q d) * ι Q b =
    ι Q c * ι Q a * (ι Q d * ι Q b)
    from by noncomm_ring]
  -- Swap ι d * ι b
  rw [ι_mul_ι_comm' b d]
  -- Distribute and clean up
  rw [show ι Q c * ι Q a *
    (algebraMap R _
      (QuadraticMap.polar Q b d) -
      ι Q b * ι Q d) =
    algebraMap R _
      (QuadraticMap.polar Q b d) *
      (ι Q c * ι Q a) -
    ι Q c * ι Q a * (ι Q b * ι Q d) from by
    rw [mul_sub, show ι Q c * ι Q a *
      algebraMap R _
        (QuadraticMap.polar Q b d) =
      algebraMap R _
        (QuadraticMap.polar Q b d) *
        (ι Q c * ι Q a) from
      (Algebra.commutes _ _).symm]]
  noncomm_ring

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
  noncomm_ring

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
  · exact Submodule.smul_mem _ _
        (ι_mul_ι_mem_bivector Q a d)
  · exact Submodule.smul_mem _ _
        (ι_mul_ι_mem_bivector Q b d)
  · exact Submodule.smul_mem _ _
        (ι_mul_ι_mem_bivector Q c b)
  · exact Submodule.smul_mem _ _
        (ι_mul_ι_mem_bivector Q c a)

end Commutator

section LieSubalgebra

variable {Q}

/-- The bivector submodule is closed under the Lie bracket.
The proof reduces to generators via `Submodule.span_induction₂`
and applies `lie_ι_mul_ι_mem_bivector` on each pair. -/
theorem lie_mem_bivector {x y : CliffordAlgebra Q}
    (hx : x ∈ bivector Q) (hy : y ∈ bivector Q) :
    ⁅x, y⁆ ∈ bivector Q := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact lie_ι_mul_ι_mem_bivector a b c d
  | zero_left _ _ =>
    rw [zero_lie]; exact (bivector Q).zero_mem
  | zero_right _ _ =>
    rw [lie_zero]; exact (bivector Q).zero_mem
  | add_left _ _ _ _ _ _ h₁ h₂ =>
    rw [add_lie]; exact (bivector Q).add_mem h₁ h₂
  | add_right _ _ _ _ _ _ h₁ h₂ =>
    rw [lie_add]; exact (bivector Q).add_mem h₁ h₂
  | smul_left r _ _ _ _ h =>
    rw [smul_lie]; exact (bivector Q).smul_mem r h
  | smul_right r _ _ _ _ h =>
    rw [lie_smul]; exact (bivector Q).smul_mem r h

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
