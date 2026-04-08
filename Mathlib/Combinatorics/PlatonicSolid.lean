/-
Copyright (c) 2026 J. York Seale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. York Seale
-/
import Mathlib.Tactic

/-!
# Classification of Platonic Solids

A Platonic solid (regular convex polyhedron) is determined by its Schläfli symbol `{p, q}`,
where `p ≥ 3` is the number of sides of each face and `q ≥ 3` is the number of faces meeting
at each vertex. The angle defect condition for a convex polyhedron requires

  `1/p + 1/q > 1/2`

This file proves that exactly five pairs `(p, q)` satisfy these constraints,
corresponding to the five Platonic solids:

| Symbol | Name | Faces | Vertices | Edges |
|--------|------|-------|----------|-------|
| {3, 3} | Tetrahedron | 4 | 4 | 6 |
| {4, 3} | Cube | 6 | 8 | 12 |
| {3, 4} | Octahedron | 8 | 6 | 12 |
| {5, 3} | Dodecahedron | 12 | 20 | 30 |
| {3, 5} | Icosahedron | 20 | 12 | 30 |

## Main results

* `PlatonicSolid`: Inductive type enumerating the five Platonic solids.
* `PlatonicSolid.schlafli`: The Schläfli symbol `(p, q)` for each solid.
* `schlafli_constraint_iff`: A pair `(p, q)` with `p ≥ 3` and `q ≥ 3` satisfies
  `2 * p + 2 * q > p * q` (the integer form of `1/p + 1/q > 1/2`)
  if and only if it is the Schläfli symbol of a Platonic solid.
* `PlatonicSolid.card`: `Fintype.card PlatonicSolid = 5`.

## References

* [Coxeter, H.S.M., *Regular Polytopes*][coxeter1973]
* [Euclid, *Elements*, Book XIII, Proposition 18][euclid]

## Tags

platonic solid, regular polyhedron, Schläfli symbol, classification
-/

/-- The five Platonic solids (regular convex polyhedra). -/
inductive PlatonicSolid where
  | tetrahedron   -- {3, 3}
  | cube          -- {4, 3}
  | octahedron    -- {3, 4}
  | dodecahedron  -- {5, 3}
  | icosahedron   -- {3, 5}
  deriving DecidableEq, Fintype, Repr

namespace PlatonicSolid

/-- The Schläfli symbol `(p, q)` of a Platonic solid, where `p` is the number of sides
of each face and `q` is the number of faces meeting at each vertex. -/
def schlafli : PlatonicSolid → ℕ × ℕ
  | .tetrahedron  => (3, 3)
  | .cube         => (4, 3)
  | .octahedron   => (3, 4)
  | .dodecahedron => (5, 3)
  | .icosahedron  => (3, 5)

/-- The Schläfli symbol map is injective: distinct solids have distinct symbols. -/
theorem schlafli_injective : Function.Injective schlafli := by
  intro a b h
  cases a <;> cases b <;> simp [schlafli] at h <;> try rfl

/-- The number of faces of each Platonic solid. -/
def faces : PlatonicSolid → ℕ
  | .tetrahedron  => 4
  | .cube         => 6
  | .octahedron   => 8
  | .dodecahedron => 12
  | .icosahedron  => 20

/-- The number of vertices of each Platonic solid. -/
def vertices : PlatonicSolid → ℕ
  | .tetrahedron  => 4
  | .cube         => 8
  | .octahedron   => 6
  | .dodecahedron => 20
  | .icosahedron  => 12

/-- The number of edges of each Platonic solid. -/
def edges : PlatonicSolid → ℕ
  | .tetrahedron  => 6
  | .cube         => 12
  | .octahedron   => 12
  | .dodecahedron => 30
  | .icosahedron  => 30

/-- Euler's formula `V - E + F = 2` holds for each Platonic solid. -/
theorem euler_formula (s : PlatonicSolid) :
    s.vertices + s.faces = s.edges + 2 := by
  cases s <;> rfl

/-- The edge count satisfies `2E = pF` for Schläfli symbol `(p, q)`. -/
theorem edge_face_relation (s : PlatonicSolid) :
    2 * s.edges = s.schlafli.1 * s.faces := by
  cases s <;> rfl

/-- The edge count satisfies `2E = qV` for Schläfli symbol `(p, q)`. -/
theorem edge_vertex_relation (s : PlatonicSolid) :
    2 * s.edges = s.schlafli.2 * s.vertices := by
  cases s <;> rfl

/-- Duality: swapping `(p, q)` to `(q, p)` exchanges faces and vertices. -/
def dual : PlatonicSolid → PlatonicSolid
  | .tetrahedron  => .tetrahedron   -- self-dual
  | .cube         => .octahedron
  | .octahedron   => .cube
  | .dodecahedron => .icosahedron
  | .icosahedron  => .dodecahedron

/-- The dual of a solid has the swapped Schläfli symbol. -/
theorem dual_schlafli (s : PlatonicSolid) :
    (s.dual).schlafli = (s.schlafli.2, s.schlafli.1) := by
  cases s <;> rfl

/-- Duality is an involution. -/
theorem dual_involutive : Function.Involutive dual := by
  intro s; cases s <;> rfl

/-- The dual of a solid has faces equal to the original's vertices. -/
theorem dual_faces_eq_vertices (s : PlatonicSolid) :
    s.dual.faces = s.vertices := by
  cases s <;> rfl

/-- There are exactly five Platonic solids. -/
theorem card : Fintype.card PlatonicSolid = 5 := by decide

end PlatonicSolid

/-! ## The Schläfli constraint and classification -/

/-- The integer form of the Schläfli angle defect condition `1/p + 1/q > 1/2`.
Multiplying through by `2pq` (positive since `p, q ≥ 3`), this becomes
`2q + 2p > pq`. We state it as `2 * p + 2 * q > p * q` to avoid subtraction on `ℕ`. -/
def SchlafliConstraint (p q : ℕ) : Prop :=
  3 ≤ p ∧ 3 ≤ q ∧ 2 * p + 2 * q > p * q

/-- Every Platonic solid's Schläfli symbol satisfies the constraint. -/
theorem PlatonicSolid.satisfies_constraint (s : PlatonicSolid) :
    SchlafliConstraint s.schlafli.1 s.schlafli.2 := by
  cases s <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num [schlafli, SchlafliConstraint]

/-- The key finiteness lemma: if `p ≥ 3` and `q ≥ 3` and `2p + 2q > pq`,
then `p ≤ 5`. -/
theorem schlafli_p_le_five {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h : 2 * p + 2 * q > p * q) : p ≤ 5 := by
  by_contra h_gt
  push_neg at h_gt
  have hp6 : 6 ≤ p := h_gt
  have h1 : p * q ≥ 6 * q := Nat.mul_le_mul_right q hp6
  have h2 : 6 * q ≥ 6 * 3 := Nat.mul_le_mul_left 6 hq
  nlinarith

/-- Similarly, `q ≤ 5`. -/
theorem schlafli_q_le_five {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h : 2 * p + 2 * q > p * q) : q ≤ 5 := by
  have h' : 2 * q + 2 * p > q * p := by linarith [mul_comm p q]
  exact schlafli_p_le_five hq hp h'

/-- Classification: a pair `(p, q)` satisfies the Schläfli constraint if and only if
it is the symbol of a Platonic solid. -/
theorem schlafli_constraint_iff {p q : ℕ} :
    SchlafliConstraint p q ↔
    (p, q) = (3, 3) ∨ (p, q) = (4, 3) ∨ (p, q) = (3, 4) ∨
    (p, q) = (5, 3) ∨ (p, q) = (3, 5) := by
  constructor
  · intro ⟨hp, hq, h⟩
    have hp5 := schlafli_p_le_five hp hq h
    have hq5 := schlafli_q_le_five hp hq h
    interval_cases p <;> interval_cases q <;>
      simp_all [SchlafliConstraint] <;> omega
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by omega, by omega, by omega⟩

/-- The classification rephrased: the Schläfli symbols of Platonic solids are exactly
the solutions to the constraint. -/
theorem schlafli_constraint_iff_exists_solid {p q : ℕ} :
    SchlafliConstraint p q ↔ ∃ s : PlatonicSolid, s.schlafli = (p, q) := by
  rw [schlafli_constraint_iff]
  constructor
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.tetrahedron, rfl⟩
    · exact ⟨.cube, rfl⟩
    · exact ⟨.octahedron, rfl⟩
    · exact ⟨.dodecahedron, rfl⟩
    · exact ⟨.icosahedron, rfl⟩
  · rintro ⟨s, hs⟩
    cases s <;> simp [PlatonicSolid.schlafli] at hs <;> obtain ⟨rfl, rfl⟩ := hs
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; left; rfl
    · right; right; right; right; rfl
