/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Combinatorics.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimplicialComplex.Topology.Simplex

/-!
# Geometric realisation of a simplicial complex

For a simplicial complex `X`, its **geometric realisation** `|X|` is the space of
formal convex combinations of vertices contained in a single face of `X`. Concretely, a
point is given by a supporting face `A : Finset U` together with barycentric coordinates
`w : U → ℝ` supported on `A`, summing to `1`, and with all coordinates in `[0, 1]`.

We equip `|X|` with the **final topology** with respect to the family of inclusions
`Simplex s → |X|` over all faces `s ∈ X.faces`. This makes the inclusions continuous and
characterises continuity out of `|X|` by checking on each face.

## Main definitions

* `GeomReal X` : the type of points in the geometric realisation of `X`.
* `GeomReal.inclusion` : the inclusion `Simplex s → |X|` for a face `s`.
* `GeomReal.toSimplex` : turn `p : |X|` into a point of the simplex on its supporting face.
* `GeomReal.instTopologicalSpace` : the final (coinduced supremum) topology on `|X|`.

## Main results

* `GeomReal.inclusion_continuous` : each inclusion `Simplex s → |X|` is continuous.
* `GeomReal.inclusion_toSimplex`, `GeomReal.toSimplex_inclusion` :
  the two “change of packaging” maps are inverse up to `shrink`.
* `GeomReal.continuous_iff` : continuity out of `|X|` can be checked on each face.
* `GeomReal.function_ext` : functions out of `|X|` agree if they agree on every face.
* `GeomReal.ext_weight` : extensionality by weights: `p = q` if `p.weight = q.weight`.

## Implementation notes

* The topology on `|X|` is `⨆ s, coinduced (inclusion s)`. We use
  `continuous_iff_coinduced_le` to prove `inclusion_continuous` and `continuous_iff`.

## Tags

simplicial complex, geometric realisation, final topology
-/

open Simplex SimplicialComplex

variable {U : Type*} [DecidableEq U]
variable {X : SimplicialComplex U}
variable {Y : Type*} [TopologicalSpace Y]

/-- A point of the geometric realisation `|X|` is a convex combination of vertices in a single
face. We store the supporting face, the weight function, and the usual barycentric axioms. -/
@[ext] structure GeomReal (X : SimplicialComplex U) where
  /-- The supporting face. -/
  face : Finset U
  /-- Proof that the supporting face is indeed a face of `X`. -/
  face_mem : face ∈ X.faces
  /-- Barycentric coordinates on vertices. -/
  weight : U → ℝ
  /-- The support of `weight` is exactly `face`. -/
  support_eq : ∀ v, v ∈ face ↔ weight v ≠ 0
  /-- The weights sum to `1` on the face. -/
  sum_eq_one : (∑ v ∈ face, weight v) = 1
  /-- Every weight lies in `[0, 1]`. -/
  range_mem_Icc : ∀ v, weight v ∈ Set.Icc (0 : ℝ) 1

/-- Coerce a geometric–realisation point to its weight function. -/
instance {X} : CoeFun (GeomReal (U := U) X) (fun _ ↦ U → ℝ) :=
  ⟨GeomReal.weight⟩

namespace GeomReal

omit [DecidableEq U] in
/-- **Extensionality by weights for points**
Two points in the geometric realisation are equal as soon as their weight
functions coincide. In particular, the supporting face then also agrees since
`v ∈ p.face ↔ p.weight v ≠ 0`. -/
lemma ext_weight {X : SimplicialComplex U} {p q : GeomReal X}
    (hweight : p.weight = q.weight) : p = q := by
  have hface : p.face = q.face := by
    ext v
    have hp : v ∈ p.face ↔ p.weight v ≠ 0 := p.support_eq v
    have hq : v ∈ q.face ↔ q.weight v ≠ 0 := q.support_eq v
    have hw : p.weight v = q.weight v := congrArg (fun f => f v) hweight
    constructor
    · intro hv
      have : p.weight v ≠ 0 := hp.mp hv
      exact hq.mpr (by simpa [hw] using this)
    · intro hv
      have : q.weight v ≠ 0 := hq.mp hv
      exact hp.mpr (by simpa [hw] using this)
  exact
    (by
      cases p with
      | mk p_face p_face_mem p_weight p_support p_sum p_icc =>
        cases q with
        | mk q_face q_face_mem q_weight q_support q_sum q_icc =>
          cases hface
          cases hweight
          rfl)

/-- The canonical inclusion of a standard simplex (over the face `s`) into `|X|`. -/
noncomputable def inclusion (s : X.faces) :
    Simplex s.1 → GeomReal X := fun pt => by
  let A' := supportFinset pt
  have hsub : A' ⊆ s.1 := by
    intro v hv; exact (Finset.mem_filter.1 hv).1
  have hA' : (A' : Finset U) ∈ X.faces := X.downward_closed s.property hsub
  have hsupport : ∀ v, v ∈ A' ↔ pt v ≠ 0 := by
    intro v; dsimp [A']; exact mem_supportFinset pt
  have hsum : (∑ v ∈ A', pt v) = 1 := by
    have hvanish :
        ∀ v ∈ s.1, v ∉ A' → pt v = 0 := by
      intro v _ hv; by_contra hne; exact hv ((hsupport v).mpr hne)
    have hEq : (∑ v ∈ A', pt v) = (∑ v ∈ s.1, pt v) :=
      Finset.sum_subset hsub hvanish
    simpa [hEq] using pt.sum_eq_one
  exact
    { face := A'
      face_mem := hA'
      weight := pt
      support_eq := hsupport
      sum_eq_one := hsum
      range_mem_Icc := pt.range_mem_Icc }

/-- The final topology on `|X|`, i.e., the supremum of the topologies coinduced by the inclusions
`Simplex s → |X|`. -/
noncomputable instance instTopologicalSpace (X : SimplicialComplex U) :
    TopologicalSpace (GeomReal X) :=
  ⨆ (s : X.faces),
    TopologicalSpace.coinduced (inclusion s) (inferInstance : TopologicalSpace (Simplex s.1))

/-- Each face inclusion map is continuous. -/
@[simp] lemma inclusion_continuous (s : X.faces) : Continuous (inclusion s) := by
  refine (continuous_iff_coinduced_le).2 ?_
  exact le_iSup_of_le s le_rfl

/-- View `p : |X|` as a point of the simplex on its supporting face. -/
noncomputable def toSimplex (p : GeomReal X) :
    Simplex p.face := by
  refine
    { weight := p.weight
      support_subset := ?_
      sum_eq_one := by simpa using p.sum_eq_one
      range_mem_Icc := p.range_mem_Icc }
  intro v hv
  have : v ∉ p.face := hv
  have : ¬ p.weight v ≠ 0 := (not_congr (p.support_eq v)).mp this
  exact not_not.mp this

omit [DecidableEq U] in
/-- The weight function does not change when passing to `p.toSimplex`. -/
@[simp] lemma toSimplex_weight (p : GeomReal X) :
    (toSimplex (X := X) p : U → ℝ) = p.weight := rfl

/-- Repackaging via `toSimplex` and then including recovers the original point. -/
@[simp] lemma inclusion_toSimplex (p : GeomReal X) :
    inclusion (s := ⟨p.face, p.face_mem⟩) (toSimplex p) = p := by
  ext v
  · change v ∈ Simplex.supportFinset (toSimplex p) ↔ v ∈ p.face
    have h₁ :
        v ∈ Simplex.supportFinset (toSimplex p) ↔
          (toSimplex p : U → ℝ) v ≠ 0 :=
      Simplex.mem_supportFinset (toSimplex p) (v := v)
    have h₂ : v ∈ p.face ↔ p.weight v ≠ 0 := p.support_eq v
    simpa [toSimplex_weight (X := X) p] using h₁.trans h₂.symm
  · rfl

/-- `toSimplex` after an inclusion is `shrink`. -/
@[simp] lemma toSimplex_inclusion (t : X.faces) (p : Simplex t.1) :
    toSimplex (inclusion t p) = Simplex.shrink p := by
  apply Simplex.ext
  funext v; rfl

omit [DecidableEq U] in
/-- Face inclusions commute with the `simplexEmbedding` maps. -/
@[simp] lemma inclusion_simplexEmbedding
    {X : SimplicialComplex U} [DecidableEq U]
    {A B : X.faces} (hAB : (A : Finset U) ⊆ (B : Finset U))
    (p : Simplex A.1) :
  inclusion (s := B) (simplexEmbedding hAB p) = inclusion (s := A) p := by
  ext v
  · change v ∈ (Simplex.supportFinset (simplexEmbedding hAB p)) ↔
           v ∈ Simplex.supportFinset p
    simp [Simplex.supportFinset_simplexEmbedding, Simplex.mem_supportFinset]
  · rfl

/-- On `|X|`, continuity can be checked on each face inclusion. -/
lemma continuous_iff (f : GeomReal X → Y) :
    Continuous f ↔ ∀ s : X.faces, Continuous (fun p => f (inclusion s p)) := by
  constructor
  · intro hf s
    exact hf.comp (inclusion_continuous (X := X) s)
  · intro h
    refine (continuous_iff_coinduced_le).2 ?_
    have H : (⨆ s : X.faces,
          TopologicalSpace.coinduced
            (fun p => f (inclusion s p))
            (inferInstance : TopologicalSpace (Simplex s.1)))
        ≤ (inferInstance : TopologicalSpace Y) :=
      iSup_le (fun s => (continuous_iff_coinduced_le).1 (h s))
    simpa [instTopologicalSpace] using H


/-- **Extensionality for maps out of `|X|`.** Two maps `f, g : |X| → Y` are equal if they agree
on each included simplex. -/
lemma function_ext {X : SimplicialComplex U} {Y : Type*}
  (f g : GeomReal X → Y) (h_agree : ∀ s : X.faces, f ∘ inclusion s = g ∘ inclusion s) :
  f = g := by
  funext p
  let s : X.faces := ⟨p.face, p.face_mem⟩
  have hp : inclusion s (toSimplex p) = p := inclusion_toSimplex (p := p)
  calc
    f p = f (inclusion s (toSimplex p)) := by rw [hp]
    _   = g (inclusion s (toSimplex p)) := by
      simpa using congrFun (h_agree s) (toSimplex p)
    _   = g p := by rw [hp]

end GeomReal

#lint
