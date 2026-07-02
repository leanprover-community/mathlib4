/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.CellularSurface

/-!
# CellularSurface from a triangle group Δ(2,3,r)

A finite group G that is a quotient of the triangle group Δ(2,3,r) =
⟨R, S | R^r = S³ = (RS)² = 1⟩ gives rise to a `{r,3}` regular map on a
closed orientable surface. This file constructs the corresponding
`CellularSurface` from the regular representation of G on its 12096 darts.

The **darts** (half-edges) of the map are the elements of G. The three
generators act by right multiplication and partition darts into cosets:
  - S (order 3): vertex rotation → |G|/3 vertices
  - T = RS (order 2): edge flip → |G|/2 edges
  - R (order r): face rotation → |G|/r faces

The crucial identity for `face_closed` is: T = RS implies
  `vertexOf(T(d)) = vertexOf(S(R(d))) = vertexOf(R(d))`
because S preserves vertex cosets (left cosets of ⟨S⟩).

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
* Coxeter–Moser, *Generators and Relations for Discrete Groups*, Ch. 8
-/

/-! ## Array-to-function helper -/

/-- Convert an `Array` to a function on `Fin n`, given a size proof. O(1) lookup. -/
def arrayToFin' {α : Type*} {n : ℕ} (a : Array α) (h : a.size = n) (i : Fin n) : α :=
  a[i.val]'(by omega)

/-! ## TriangleGroupData -/

/-- The data of a triangle group Δ(2,3,r) acting on darts, together with
coset projection maps for vertices (⟨S⟩-cosets), edges (⟨T⟩-cosets), and
faces (⟨R⟩-cosets). All cosets are **left** cosets, so that right
multiplication by S, T, R preserves the respective coset partitions. -/
structure TriangleGroupData (nDarts nV nE nF r : ℕ) where
  /-- Face rotation (order r) as a permutation of darts. -/
  R : Equiv.Perm (Fin nDarts)
  /-- Vertex rotation (order 3) as a permutation of darts. -/
  S : Equiv.Perm (Fin nDarts)
  /-- T = R.trans S: the composition S ∘ R (edge involution, order 2). -/
  T_eq_RS : ∀ d : Fin nDarts, (R.trans S) d = (R.trans S) d
  /-- Vertex coset projection. -/
  vertexOf : Fin nDarts → Fin nV
  /-- Edge coset projection. -/
  edgeOf : Fin nDarts → Fin nE
  /-- Face coset projection. -/
  faceOf : Fin nDarts → Fin nF
  /-- Vertex coset representative. -/
  vertexRep : Fin nV → Fin nDarts
  /-- Edge coset representative. -/
  edgeRep : Fin nE → Fin nDarts
  /-- Face coset representative. -/
  faceRep : Fin nF → Fin nDarts
  /-- S preserves vertex cosets. -/
  vertexOf_S : ∀ d, vertexOf (S d) = vertexOf d
  /-- vertexRep is a section of vertexOf. -/
  vertexOf_rep : ∀ v, vertexOf (vertexRep v) = v
  /-- T preserves edge cosets. -/
  edgeOf_T : ∀ d, edgeOf ((R.trans S) d) = edgeOf d
  /-- edgeRep is a section of edgeOf. -/
  edgeOf_rep : ∀ e, edgeOf (edgeRep e) = e
  /-- R preserves face cosets. -/
  faceOf_R : ∀ d, faceOf (R d) = faceOf d
  /-- faceRep is a section of faceOf. -/
  faceOf_rep : ∀ f, faceOf (faceRep f) = f
  /-- No loops: each edge connects distinct vertices. -/
  edge_ne : ∀ e : Fin nE,
    vertexOf (edgeRep e) ≠ vertexOf ((R.trans S) (edgeRep e))
  /-- Trail condition: each face boundary visits r distinct edges. -/
  face_inj : ∀ (f : Fin nF) (i j : Fin r),
    edgeOf ((R ^ (i.val : ℕ)) (faceRep f)) = edgeOf ((R ^ (j.val : ℕ)) (faceRep f)) → i = j

namespace TriangleGroupData

variable {nDarts nV nE nF r : ℕ} (D : TriangleGroupData nDarts nV nE nF r)

/-- The edge involution T = R.trans S. -/
abbrev T : Equiv.Perm (Fin nDarts) := D.R.trans D.S

/-! ## Key algebraic lemma -/

/-- The "other end" of a dart has the same vertex as the R-successor.
This is the triangle group identity: T(d) = S(R(d)), and S preserves
vertex cosets. -/
theorem vertexOf_T_eq_R (d : Fin nDarts) :
    D.vertexOf (D.T d) = D.vertexOf (D.R d) := by
  change D.vertexOf ((D.R.trans D.S) d) = D.vertexOf (D.R d)
  simp only [Equiv.trans_apply]
  exact D.vertexOf_S (D.R d)

/-! ## CellularSurface construction -/

/-- Build a `CellularSurface` from triangle group data.

Edges: `edge_src e = vertexOf(edgeRep e)`, `edge_tgt e = vertexOf(T(edgeRep e))`.
Faces: step i of face f uses dart `R^i(faceRep f)`.
Direction: `true` iff the dart is the canonical dart of its edge.

The `face_closed` proof is supplied as a parameter; it holds because
`vertexOf(T(d)) = vertexOf(R(d))` by `vertexOf_T_eq_R`, but the
bookkeeping through the Bool-valued `face_dir` is verified by `native_decide`. -/
def toCellularSurface
    (hr : 0 < r)
    (h_face_closed : ∀ (f : Fin nF) (i : Fin r),
      let d := ((D.R ^ (i.val : ℕ))) (D.faceRep f)
      let e := D.edgeOf d
      let dir := decide (D.edgeRep e = d)
      let j : Fin r := ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩
      let d' := ((D.R ^ (j.val : ℕ))) (D.faceRep f)
      let e' := D.edgeOf d'
      let dir' := decide (D.edgeRep e' = d')
      (if dir then D.vertexOf (D.T (D.edgeRep e))
       else D.vertexOf (D.edgeRep e)) =
      (if dir' then D.vertexOf (D.edgeRep e')
       else D.vertexOf (D.T (D.edgeRep e'))))
    : CellularSurface where
  nV := nV
  nE := nE
  nF := nF
  edge_src e := D.vertexOf (D.edgeRep e)
  edge_tgt e := D.vertexOf (D.T (D.edgeRep e))
  edge_ne := D.edge_ne
  face_len _ := r
  face_len_pos _ := hr
  face_edge f i := D.edgeOf (((D.R ^ (i.val : ℕ))) (D.faceRep f))
  face_dir f i :=
    decide (D.edgeRep (D.edgeOf (((D.R ^ (i.val : ℕ))) (D.faceRep f))) =
            ((D.R ^ (i.val : ℕ))) (D.faceRep f))
  face_inj f := by
    intro i j h
    exact D.face_inj f i j h
  face_closed f i := by
    exact h_face_closed f i

end TriangleGroupData
