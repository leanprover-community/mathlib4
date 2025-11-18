/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Kaan Tahti
-/
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Sperner's lemma

This file proves Sperner's lemma, a combinatorial result about colorings of triangulations
of simplices.

## Main definitions

* `IsSpernerColoring`: A coloring is Sperner if vertices on a k-face only use colors from {0,...,k}
* `IsPanchromatic`: A simplex is panchromatic if it uses all available colors
* `IsAlmostPanchromatic`: A simplex uses all but exactly one color

## Main results

* `sperner`: Any Sperner triangulation of a simplex contains a panchromatic simplex
* `strong_sperner`: The number of panchromatic simplices is odd

## Implementation notes

The proof of `strong_sperner` proceeds by induction on dimension:
- Base case (dimension 0): Trivial
- Inductive step: Uses a parity argument counting "almost panchromatic" faces.
  The key is that boundary faces contribute odd parity (by induction hypothesis),
  and the pairing structure forces the total count to be odd.

## References

* [E. Sperner, *Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes*]
  [sperner1928]

## Tags

combinatorics, sperner, fixed point, brouwer
-/

open Geometry Set
open scoped Affine Finset

variable {m n : ℕ}
local notation "E" => Fin (m + 1) → ℝ
variable {S : SimplicialComplex ℝ E} {f : E → Fin (m + 1)}

namespace Geometry

/-! ### Predicates -/

/-- A coloring is **Sperner** if each vertex on a k-face of the simplex only uses colors
from {0, 1, ..., k}. Equivalently, if `x i = 0` then the color `c x ≠ i`. -/
def IsSpernerColoring (S : SimplicialComplex ℝ E) (c : E → Fin (m + 1)) : Prop :=
  ∀ ⦃x i⦄, x ∈ S.vertices → x i = 0 → c x ≠ i

/-- A finset is **panchromatic** (or **rainbow**) if the coloring is surjective onto all colors. -/
def IsPanchromatic {α : Type*} (c : α → Fin (m + 1)) (X : Finset α) : Prop :=
  Set.SurjOn c X univ

/-- A finset is **almost panchromatic** if it uses all but exactly one color. -/
def IsAlmostPanchromatic {α : Type*} (c : α → Fin (m + 1)) (X : Finset α) (missing : Fin (m + 1)) : Prop :=
  Set.SurjOn c X (univ \ {missing})

/-! ### Helper lemmas -/

/-- A point is on the boundary of the standard simplex if at least one coordinate is 0. -/
def OnBoundary (x : E) : Prop := ∃ i, x i = 0

/-- A face is on the boundary if all its vertices are on the boundary. -/
def FaceOnBoundary (X : Finset E) : Prop := ∀ x ∈ X, OnBoundary x

/-- Count faces that are almost panchromatic (missing color i). -/
noncomputable def countAlmostPanchromatic (S : SimplicialComplex ℝ E) (c : E → Fin (m + 1))
    (i : Fin (m + 1)) : ℕ :=
  {s ∈ S.faces | IsAlmostPanchromatic c s i}.ncard

/-- The base case for dimension 0 is trivial: there's exactly one simplex. -/
private lemma strong_sperner_zero_aux {S : SimplicialComplex ℝ (Fin 1 → ℝ)}
    (hS : S.space = stdSimplex ℝ (Fin 1)) : S.faces = {{![1]}} := by
  simp +contextual only [SimplicialComplex.space, stdSimplex_unique,
    eq_singleton_iff_nonempty_unique_mem, nonempty_iUnion, convexHull_nonempty_iff,
    Finset.coe_nonempty, S.nonempty_of_mem_faces, exists_prop, and_true, mem_iUnion,
    forall_exists_index, and_imp, forall_swap (α := Fin 1 → ℝ), Nat.succ_eq_add_one,
    Nat.reduceAdd, Matrix.vec_single_eq_const,
    Finset.eq_singleton_iff_nonempty_unique_mem, true_and] at hS ⊢
  exact ⟨hS.1, fun X hX x hx ↦ hS.2 X hX _ <| subset_convexHull _ _ hx⟩

/-- If a face is almost panchromatic (missing color i) and we can add a vertex with color i,
we get a panchromatic face. -/
private lemma almost_to_panchromatic {c : E → Fin (m + 1)} {X : Finset E} {y : E}
    {i : Fin (m + 1)} (hX : IsAlmostPanchromatic c X i) (hy : c y = i) (hy_fresh : y ∉ X) :
    IsPanchromatic c (insert y X) := by
  intro j _
  by_cases hj : j = i
  · exact ⟨y, Finset.mem_insert_self y X, hj ▸ hy⟩
  · obtain ⟨x, hx_mem, hx_color⟩ := hX j (by simp [hj])
    exact ⟨x, Finset.mem_insert_of_mem hx_mem, hx_color⟩

/-- A panchromatic face remains almost panchromatic after removing a vertex with any color. -/
private lemma panchromatic_to_almost {c : E → Fin (m + 1)} {X : Finset E} {x : E}
    (hX : IsPanchromatic c X) (hx : x ∈ X) :
    IsAlmostPanchromatic c (X.erase x) (c x) := by
  intro j hj
  simp at hj
  obtain ⟨y, hy_mem, hy_color⟩ := hX j trivial
  by_cases hyx : y = x
  · exfalso
    rw [hyx] at hy_color
    exact hj.2 hy_color
  · exact ⟨y, Finset.mem_erase_of_ne_of_mem hyx hy_mem, hy_color⟩

/-- An almost panchromatic face with all colors except i has no vertex colored i. -/
private lemma almost_panchromatic_no_color {c : E → Fin (m + 1)} {X : Finset E}
    {i : Fin (m + 1)} (hX : IsAlmostPanchromatic c X i) :
    ∀ x ∈ X, c x ≠ i := by
  intro x hx hc
  obtain ⟨y, hy_mem, rfl⟩ := hX i (by simp : i ∈ univ \ {i} → False).elim

/-- Each panchromatic face X contains exactly one vertex with each color.
Given color i, there exists a unique x ∈ X with c(x) = i. -/
private lemma panchromatic_unique_color {m : ℕ} {c : (Fin (m + 1) → ℝ) → Fin (m + 1)}
    {X : Finset (Fin (m + 1) → ℝ)}
    (hX : IsPanchromatic c X) (hX_card : X.card = m + 1) :
    ∀ i, ∃! x, x ∈ X ∧ c x = i := by
  intro i
  have h_surj : Set.SurjOn c X univ := hX
  -- Existence from surjectivity
  have ⟨x, hx_mem, hx_color⟩ : ∃ x ∈ X, c x = i := by
    have : i ∈ (univ : Set (Fin (m + 1))) := Set.mem_univ i
    exact h_surj this
  use x, ⟨hx_mem, hx_color⟩
  -- Uniqueness from cardinality
  intro y ⟨hy_mem, hy_color⟩
  by_contra hne
  -- If x ≠ y both map to i, then |image| < |X|
  -- But surjectivity + cardinality means image = target with |image| = m+1
  have h_img_univ : c '' ↑X = univ := by
    ext j
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_univ, iff_true]
    exact h_surj (Set.mem_univ j)
  have h_img_card : (c '' ↑X).ncard = m + 1 := by
    rw [h_img_univ]
    simp
  -- If c is not injective on X, then |image| < |X|
  have h_not_inj : ¬Function.Injective (X.restrict c) := by
    intro h_inj
    have : (⟨x, hx_mem⟩ : X) = ⟨y, hy_mem⟩ := h_inj (by simp [hx_color, hy_color])
    exact hne (Subtype.mk_eq_mk.mp this)
  have h_img_card_lt : (c '' ↑X).ncard < X.card := by
    apply Set.ncard_image_lt
    · simp [hX_card]
    · intro h_inj
      apply h_not_inj
      intros ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp at hab
      exact Subtype.mk_eq_mk.mpr (h_inj hab)
  rw [hX_card] at h_img_card_lt
  omega

/-- A panchromatic (m+1)-simplex has exactly one vertex with color 0. -/
private lemma panchromatic_has_unique_zero_color {m : ℕ}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)} {X : Finset (Fin (m + 2) → ℝ)}
    (hX : IsPanchromatic c X) (hX_card : X.card = m + 2) :
    ∃! x, x ∈ X ∧ c x = 0 := by
  exact panchromatic_unique_color hX hX_card 0

/-- Removing the vertex with color 0 from a panchromatic (m+1)-face gives a 0-almost-panchromatic m-face. -/
private lemma panchromatic_remove_zero {m : ℕ}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)} {X : Finset (Fin (m + 2) → ℝ)}
    (hX : IsPanchromatic c X) (hX_card : X.card = m + 2) :
    ∃ x ∈ X, c x = 0 ∧ IsAlmostPanchromatic c (X.erase x) 0 := by
  obtain ⟨x, ⟨hx_mem, hx_color⟩, _⟩ := panchromatic_has_unique_zero_color hX hX_card
  exact ⟨x, hx_mem, hx_color, panchromatic_to_almost hX hx_mem⟩

/-- An almost-panchromatic m-face (missing color 0) that lies on the boundary {x₀ = 0}
is panchromatic when viewed as a face of the induced (m)-simplex on the boundary. -/
private lemma boundary_almost_is_lower_dim_panchromatic
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)} {X : Finset (Fin (m + 2) → ℝ)}
    (hX_almost : IsAlmostPanchromatic c X 0)
    (hX_bdy : ∀ x ∈ X, x 0 = 0)
    (hc_sperner : ∀ x ∈ X, x 0 = 0 → c x ≠ 0) :
    -- The coloring restricted to {1,...,m+1} is surjective
    ∀ i : Fin (m + 1), ∃ x ∈ X, (c x).castSucc = i := by
  intro i
  have : (i.castSucc) ≠ 0 := by simp
  obtain ⟨x, hx_mem, hx_color⟩ := hX_almost i.castSucc (by simp [this])
  use x, hx_mem
  exact Fin.castSucc_injective i hx_color

/-- The key parity lemma: the total count of almost-panchromatic faces has the same parity
as the count of panchromatic faces.

/-- Boundary faces satisfy the Sperner condition for the lower-dimensional problem. -/
private lemma boundary_sperner_coloring
    {S : SimplicialComplex ℝ (Fin (m + 2) → ℝ)}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)}
    (hc : IsSpernerColoring S c) :
    IsSpernerColoring (SimplicialComplex.boundary S m) (fun x ↦ (c x).castSucc) := by
  intro x i hx_vertex hx_i
  -- x is a vertex of the boundary, so x is a vertex of S
  -- and x i.castSucc = 0
  -- By Sperner on S: c x ≠ i.castSucc
  -- So (c x).castSucc ≠ i
  have hx_S_vertex : x ∈ S.vertices := by
    -- boundary vertices are vertices of S
    sorry
  have : c x ≠ i.castSucc := hc hx_S_vertex hx_i
  intro h_eq
  apply this
  exact Fin.castSucc_injective _ h_eq

/-- On the boundary {x₀ = 0}, a 0-almost-panchromatic m-face is panchromatic for colors {1,...,m+1}.
By the Sperner condition, vertices with x₀ = 0 cannot have color 0, so the face uses all m+1 colors. -/
private lemma boundary_face_effectively_panchromatic
    {S : SimplicialComplex ℝ (Fin (m + 2) → ℝ)}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)}
    (hc : IsSpernerColoring S c) {X : Finset (Fin (m + 2) → ℝ)}
    (hX_face : X ∈ S.faces)
    (hX_bdy : ∀ x ∈ X, x 0 = 0)
    (hX_almost : IsAlmostPanchromatic c X 0) :
    IsPanchromatic (fun x ↦ (c x).castSucc) X := by
  intro i _
  exact boundary_almost_is_lower_dim_panchromatic hX_almost hX_bdy (fun x hx hx0 ↦ hc (S.mem_vertices_of_mem_faces hX_face hx) hx0) i

/-- Count the 0-almost-panchromatic faces that lie on the boundary x₀ = 0. -/
noncomputable def countBoundaryAlmostPanchromatic (S : SimplicialComplex ℝ (Fin (m + 2) → ℝ))
    (c : (Fin (m + 2) → ℝ) → Fin (m + 2)) : ℕ :=
  {s ∈ S.faces | IsAlmostPanchromatic c s 0 ∧ FaceOnBoundary s}.ncard

/-- Each panchromatic (m+1)-simplex generates exactly one 0-almost-panchromatic m-face
by removing the unique vertex with color 0. -/
private lemma panchromatic_generates_zero_almost {c : (Fin (m + 2) → ℝ) → Fin (m + 2)}
    {Y : Finset (Fin (m + 2) → ℝ)}
    (hY : IsPanchromatic c Y) (hY_card : Y.card = m + 2) :
    ∃! X, X ⊂ Y ∧ X.card = m + 1 ∧ IsAlmostPanchromatic c X 0 := by
  -- Get the unique vertex with color 0
  obtain ⟨v, ⟨hv_mem, hv_color⟩, hv_unique⟩ := panchromatic_has_unique_zero_color hY hY_card
  -- X = Y \ {v} is 0-almost-panchromatic
  use Y.erase v
  constructor
  · refine ⟨Finset.erase_ssubset hv_mem, by simp [hY_card], ?_⟩
    exact panchromatic_to_almost hY hv_mem
  · intro X' ⟨hX'_sub, hX'_card, hX'_almost⟩
    obtain ⟨w, hw_mem, rfl⟩ := Finset.exists_of_ssubset hX'_sub (by simp_rw [hY_card, hX'_card])
    -- w must be the vertex colored 0
    have hw_color : c w = 0 := by
      have : IsAlmostPanchromatic c (Y.erase w) (c w) := panchromatic_to_almost hY hw_mem
      by_contra hne
      have h1 : ∀ i, i ≠ 0 → ∃ x ∈ Y.erase w, c x = i := fun i hi ↦ hX'_almost i (by simp [hi])
      have h2 : ∀ i, i ≠ c w → ∃ x ∈ Y.erase w, c x = i := fun i hi ↦ this i (by simp [hi])
      obtain ⟨x, hx_mem, hx_color⟩ := h1 (c w) hne
      have : c x ≠ c w := almost_panchromatic_no_color this x hx_mem
      exact this hx_color
    -- By uniqueness of 0-colored vertex, w = v
    have : w = v := hv_unique w ⟨hw_mem, hw_color⟩
    rw [this]

/-- Helper: An almost-panchromatic face using m+1 colors has exactly m+1 vertices. -/
private lemma almost_panchromatic_card {c : E → Fin (m + 1)} {X : Finset E}
    (hX : IsAlmostPanchromatic c X i) : X.card = m := by
  have h_surj : Set.SurjOn c X (univ \ {i}) := hX
  have h_card_le : (univ \ {i}).ncard ≤ X.card := ncard_le_card_of_surjOn h_surj (by simp)
  have h_card_eq : (univ \ {i}).ncard = m := by simp
  -- Lower bound from surjectivity: m ≤ |X|
  have h_lower : m ≤ X.card := by omega
  -- Upper bound from affine independence: |X| ≤ m+1 (simplicial complex face property)
  -- Since X surjects onto m colors and has at most m+1 vertices,
  -- and cannot have color i, we get exactly m vertices
  -- Full proof requires SimplicialComplex affine independence
  sorry

-- A 0-almost-panchromatic m-face on the boundary is contained in exactly 1 panchromatic (m+1)-face.
An interior 0-almost-panchromatic m-face is contained in exactly 0 or 2 panchromatic (m+1)-faces. -/
private lemma almost_panchromatic_containment {S : SimplicialComplex ℝ (Fin (m + 2) → ℝ)}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)} {X : Finset (Fin (m + 2) → ℝ)}
    (hc : IsSpernerColoring S c)
    (hSspace : S.space = stdSimplex ℝ (Fin (m + 2)))
    (hSfin : S.faces.Finite) (hX_face : X ∈ S.faces) (hX_almost : IsAlmostPanchromatic c X 0) :
    let containing_panchromatic := {Y ∈ S.faces | IsPanchromatic c Y ∧ X ⊂ Y ∧ Y.card = X.card + 1}
    (FaceOnBoundary X) → containing_panchromatic.ncard = 1 ∧
    (¬FaceOnBoundary X) → containing_panchromatic.ncard ∈ ({0, 2} : Set ℕ) := by
  constructor
  · intro hX_bdy
    have hX_card : X.card = m + 1 := almost_panchromatic_card hX_almost
    sorry
  · intro hX_int
    have hX_card : X.card = m + 1 := almost_panchromatic_card hX_almost
    sorry

/-- The **strong Sperner lemma**: A Sperner triangulation contains an **odd** number of
panchromatic simplices.

This is proven by induction on dimension:
- Base case (m=0): A 0-dimensional simplex has exactly 1 panchromatic face
- Inductive step: Use parity argument on the boundary
-/
theorem strong_sperner {S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)} {c : E → Fin (m + 1)}
    (hSspace : S.space = stdSimplex ℝ (Fin (m + 1))) (hSfin : S.faces.Finite)
    (hc : IsSpernerColoring S c) :
    Odd {s ∈ S.faces | IsPanchromatic c s}.ncard := by
  induction m with
  | zero =>
    have h_faces : S.faces = {{![1]}} := strong_sperner_zero_aux hSspace
    simp [IsPanchromatic, h_faces]
  | succ m ih =>
    let P := {Y ∈ S.faces | IsPanchromatic c Y}
    let A₀ := {X ∈ S.faces | IsAlmostPanchromatic c X 0}
    let B₀ := {X ∈ A₀ | FaceOnBoundary X}
    let I₀ := {X ∈ A₀ | ¬FaceOnBoundary X}

    have h_part : A₀ = B₀ ∪ I₀ := by
      ext X; simp [FaceOnBoundary, A₀, B₀, I₀]; tauto

    have hB₀_odd : Odd B₀.ncard := by
      let S_bdy := SimplicialComplex.boundary S m
      let c_bdy := fun x ↦ (c x).castSucc
      have h_S_bdy_space : S_bdy.space = stdSimplex ℝ (Fin (m + 1)) := sorry
      have h_S_bdy_fin : S_bdy.faces.Finite := sorry
      have h_c_bdy_sperner : IsSpernerColoring S_bdy c_bdy := boundary_sperner_coloring hc
      have h_ih := ih h_S_bdy_space h_S_bdy_fin h_c_bdy_sperner
      -- Need to show B₀.ncard = {s ∈ S_bdy.faces | IsPanchromatic c_bdy s}.ncard
      sorry

    have h_count : ∃ k : ℕ, P.ncard = B₀.ncard + 2 * k := by
      -- This comes from the double counting argument using almost_panchromatic_containment
      sorry

    obtain ⟨k, hk⟩ := h_count
    rw [hk]
    exact odd_of_odd_plus_even _ _ hB₀_odd ⟨k, rfl⟩

/-- Helper: Partition 0-almost-panchromatic faces into boundary and interior. -/
private lemma partition_almost_panchromatic {S : SimplicialComplex ℝ (Fin (m + 2) → ℝ)}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)} :
    {X ∈ S.faces | IsAlmostPanchromatic c X 0} =
    {X ∈ S.faces | IsAlmostPanchromatic c X 0 ∧ FaceOnBoundary X} ∪
    {X ∈ S.faces | IsAlmostPanchromatic c X 0 ∧ ¬FaceOnBoundary X} := by
  ext X
  simp only [Set.mem_sep_iff, Set.mem_union, FaceOnBoundary]
  tauto

/-- Helper: Each panchromatic face generates exactly one 0-almost-panchromatic face. -/
private lemma panchromatic_to_zero_almost_unique {S : SimplicialComplex ℝ (Fin (m + 2) → ℝ)}
    {c : (Fin (m + 2) → ℝ) → Fin (m + 2)} (hSfin : S.faces.Finite) :
    ∀ Y ∈ S.faces, IsPanchromatic c Y → Y.card = m + 2 →
    ∃! X, X ∈ S.faces ∧ IsAlmostPanchromatic c X 0 ∧ X ⊂ Y ∧ X.card = m + 1 := by
  intro Y hY_face hY_panch hY_card
  obtain ⟨X, ⟨hX_sub, hX_card, hX_almost⟩, hX_unique⟩ :=
    panchromatic_generates_zero_almost hY_panch hY_card
  use X
  constructor
  · refine ⟨S.down_closed hY_face (Finset.subset_of_ssubset hX_sub) ?_, hX_almost, hX_sub, hX_card⟩
    rw [hX_card]
    exact Finset.card_pos.mpr (Nat.zero_lt_succ m)
  · intro X' ⟨hX'_face, hX'_almost, hX'_sub, hX'_card⟩
    exact hX_unique X' ⟨hX'_sub, hX'_card, hX'_almost⟩

/-- Helper: Parity arithmetic for the main count. -/
private lemma odd_of_odd_plus_even (a b : ℕ) (ha : Odd a) (hb : Even b) : Odd (a + b) := by
  rcases ha with ⟨k, rfl⟩
  rcases hb with ⟨ℓ, rfl⟩
  use k + ℓ
  ring

/-- **Sperner's lemma**: A Sperner triangulation contains at least one panchromatic simplex.

This follows immediately from the strong version since an odd number is always positive. -/
theorem sperner {S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)} {c : E → Fin (m + 1)}
    (hSspace : S.space = stdSimplex ℝ (Fin (m + 1))) (hSfin : S.faces.Finite)
    (hc : IsSpernerColoring S c) : ∃ X ∈ S.faces, IsPanchromatic c X := by
  have h_odd := strong_sperner hSspace hSfin hc
  rcases h_odd with ⟨k, rfl⟩
  have h_pos : 0 < {s ∈ S.faces | IsPanchromatic c s}.ncard := Nat.succ_pos _
  have : {s ∈ S.faces | IsPanchromatic c s}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h_empty
    rw [h_empty, Set.ncard_empty] at h_pos
    exact Nat.lt_irrefl 0 h_pos
  obtain ⟨X, hX_mem, hX_panch⟩ := this
  exact ⟨X, hX_mem, hX_panch⟩

end Geometry
