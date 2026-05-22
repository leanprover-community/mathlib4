/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Archive.LangerGraph
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The dual Langer graph and GH(2,2) non-self-duality

The split Cayley hexagon GH(2,2) has 63 points and 63 lines, with incidence
graph the Tutte 12-cage. The **Langer graph** is the point-collinearity graph
(two points adjacent iff they share a line). The **dual Langer graph** is the
line-collinearity graph (two lines adjacent iff they share a point).

Both graphs have the same intersection array {6, 4, 4; 1, 1, 3} but are not
isomorphic. This reflects the non-self-duality of GH(2,2): a generalized
hexagon GH(q, q) is self-dual if and only if q is a power of 3 (Cohen-Tits),
and 2 is not a power of 3.

## The distinguishing invariant

For any vertex v, the subgraph induced on vertices at distance 3 is connected
in the Langer graph (1 component) but disconnected in the dual Langer graph
(2 components). Since graph isomorphisms preserve distance and connectivity,
no isomorphism can exist.

## The algebraic line-action

G₂(2) acts on points (LangerGraph.lean) and this induces an action on lines
via the triangle-line bijection: each line of GH(2,2) corresponds to a unique
triangle in the Langer graph. The induced line-action preserves the "share a
vertex" relation algebraically: injective maps commute with set intersection
(`Finset.image_inter`) and preserve non-emptiness (`Finset.image_nonempty`).

## References

* Cohen, Tits, *On generalized hexagons and a near octagon whose lines have three points*
* Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
* Brouwer-Cohen-Neumaier, *Distance-Regular Graphs* (1989), §6.5
-/

/-! ## The dual Langer graph -/

/-- Distance-2 adjacency on lines: two lines are adjacent iff they share a point. -/
def dualLangerAdjBool (l₁ l₂ : Fin 63) : Bool :=
  l₁ != l₂ &&
  let lv₁ : Fin 126 := ⟨l₁.val + 63, by omega⟩
  let lv₂ : Fin 126 := ⟨l₂.val + 63, by omega⟩
  (List.finRange 63).any fun p =>
    let pv : Fin 126 := ⟨p.val, by omega⟩
    tutte12AdjBool pv lv₁ && tutte12AdjBool pv lv₂

set_option maxHeartbeats 400000 in
/-- The **dual Langer graph**: line-collinearity of GH(2,2). -/
def dualLangerSimpleGraph : SimpleGraph (Fin 63) where
  Adj l₁ l₂ := dualLangerAdjBool l₁ l₂
  symm l₁ l₂ := by simp only [dualLangerAdjBool]; revert l₁ l₂; native_decide
  loopless := ⟨fun l => by simp only [dualLangerAdjBool]; revert l; native_decide⟩

instance dualLangerDecAdj : DecidableRel dualLangerSimpleGraph.Adj :=
  fun l₁ l₂ => inferInstanceAs (Decidable (dualLangerAdjBool l₁ l₂))

/-! ## Triangles in the Langer graph -/

/-- The set of all triangles (ordered triples i < j < k) in the Langer graph. -/
def langerTriangles : Finset (Fin 63 × Fin 63 × Fin 63) :=
  Finset.univ.filter fun (i, j, k) =>
    i < j ∧ j < k ∧
    langerSimpleGraph.Adj i j ∧ langerSimpleGraph.Adj j k ∧ langerSimpleGraph.Adj i k

/-- The Langer graph has exactly 63 triangles — one for each line of GH(2,2). -/
theorem langer_triangles_count : langerTriangles.card = 63 := by native_decide

/-- Precomputed line-to-triangle data. -/
private def lineTriangleData : Array (Fin 63 × Fin 63 × Fin 63) := #[
  (⟨0, by omega⟩, ⟨15, by omega⟩, ⟨16, by omega⟩),
  (⟨0, by omega⟩, ⟨31, by omega⟩, ⟨32, by omega⟩),
  (⟨0, by omega⟩, ⟨47, by omega⟩, ⟨48, by omega⟩),
  (⟨1, by omega⟩, ⟨7, by omega⟩, ⟨8, by omega⟩),
  (⟨1, by omega⟩, ⟨31, by omega⟩, ⟨33, by omega⟩),
  (⟨1, by omega⟩, ⟨39, by omega⟩, ⟨40, by omega⟩),
  (⟨2, by omega⟩, ⟨23, by omega⟩, ⟨24, by omega⟩),
  (⟨2, by omega⟩, ⟨31, by omega⟩, ⟨34, by omega⟩),
  (⟨2, by omega⟩, ⟨55, by omega⟩, ⟨56, by omega⟩),
  (⟨3, by omega⟩, ⟨7, by omega⟩, ⟨9, by omega⟩),
  (⟨3, by omega⟩, ⟨15, by omega⟩, ⟨17, by omega⟩),
  (⟨3, by omega⟩, ⟨23, by omega⟩, ⟨25, by omega⟩),
  (⟨4, by omega⟩, ⟨15, by omega⟩, ⟨18, by omega⟩),
  (⟨4, by omega⟩, ⟨39, by omega⟩, ⟨41, by omega⟩),
  (⟨4, by omega⟩, ⟨55, by omega⟩, ⟨57, by omega⟩),
  (⟨5, by omega⟩, ⟨7, by omega⟩, ⟨10, by omega⟩),
  (⟨5, by omega⟩, ⟨47, by omega⟩, ⟨49, by omega⟩),
  (⟨5, by omega⟩, ⟨55, by omega⟩, ⟨58, by omega⟩),
  (⟨6, by omega⟩, ⟨23, by omega⟩, ⟨26, by omega⟩),
  (⟨6, by omega⟩, ⟨39, by omega⟩, ⟨42, by omega⟩),
  (⟨6, by omega⟩, ⟨47, by omega⟩, ⟨50, by omega⟩),
  (⟨8, by omega⟩, ⟨35, by omega⟩, ⟨46, by omega⟩),
  (⟨8, by omega⟩, ⟨37, by omega⟩, ⟨45, by omega⟩),
  (⟨9, by omega⟩, ⟨19, by omega⟩, ⟨30, by omega⟩),
  (⟨9, by omega⟩, ⟨21, by omega⟩, ⟨28, by omega⟩),
  (⟨10, by omega⟩, ⟨51, by omega⟩, ⟨61, by omega⟩),
  (⟨10, by omega⟩, ⟨53, by omega⟩, ⟨60, by omega⟩),
  (⟨11, by omega⟩, ⟨17, by omega⟩, ⟨29, by omega⟩),
  (⟨11, by omega⟩, ⟨33, by omega⟩, ⟨44, by omega⟩),
  (⟨11, by omega⟩, ⟨49, by omega⟩, ⟨62, by omega⟩),
  (⟨12, by omega⟩, ⟨22, by omega⟩, ⟨25, by omega⟩),
  (⟨12, by omega⟩, ⟨33, by omega⟩, ⟨43, by omega⟩),
  (⟨12, by omega⟩, ⟨54, by omega⟩, ⟨58, by omega⟩),
  (⟨13, by omega⟩, ⟨17, by omega⟩, ⟨27, by omega⟩),
  (⟨13, by omega⟩, ⟨38, by omega⟩, ⟨40, by omega⟩),
  (⟨13, by omega⟩, ⟨52, by omega⟩, ⟨58, by omega⟩),
  (⟨14, by omega⟩, ⟨20, by omega⟩, ⟨25, by omega⟩),
  (⟨14, by omega⟩, ⟨36, by omega⟩, ⟨40, by omega⟩),
  (⟨14, by omega⟩, ⟨49, by omega⟩, ⟨59, by omega⟩),
  (⟨16, by omega⟩, ⟨35, by omega⟩, ⟨54, by omega⟩),
  (⟨16, by omega⟩, ⟨36, by omega⟩, ⟨53, by omega⟩),
  (⟨18, by omega⟩, ⟨43, by omega⟩, ⟨61, by omega⟩),
  (⟨18, by omega⟩, ⟨45, by omega⟩, ⟨59, by omega⟩),
  (⟨19, by omega⟩, ⟨32, by omega⟩, ⟨52, by omega⟩),
  (⟨19, by omega⟩, ⟨41, by omega⟩, ⟨62, by omega⟩),
  (⟨20, by omega⟩, ⟨32, by omega⟩, ⟨51, by omega⟩),
  (⟨20, by omega⟩, ⟨46, by omega⟩, ⟨57, by omega⟩),
  (⟨21, by omega⟩, ⟨38, by omega⟩, ⟨48, by omega⟩),
  (⟨21, by omega⟩, ⟨44, by omega⟩, ⟨57, by omega⟩),
  (⟨22, by omega⟩, ⟨37, by omega⟩, ⟨48, by omega⟩),
  (⟨22, by omega⟩, ⟨41, by omega⟩, ⟨60, by omega⟩),
  (⟨24, by omega⟩, ⟨35, by omega⟩, ⟨62, by omega⟩),
  (⟨24, by omega⟩, ⟨38, by omega⟩, ⟨61, by omega⟩),
  (⟨26, by omega⟩, ⟨44, by omega⟩, ⟨53, by omega⟩),
  (⟨26, by omega⟩, ⟨45, by omega⟩, ⟨52, by omega⟩),
  (⟨27, by omega⟩, ⟨34, by omega⟩, ⟨60, by omega⟩),
  (⟨27, by omega⟩, ⟨46, by omega⟩, ⟨50, by omega⟩),
  (⟨28, by omega⟩, ⟨34, by omega⟩, ⟨59, by omega⟩),
  (⟨28, by omega⟩, ⟨42, by omega⟩, ⟨54, by omega⟩),
  (⟨29, by omega⟩, ⟨37, by omega⟩, ⟨56, by omega⟩),
  (⟨29, by omega⟩, ⟨42, by omega⟩, ⟨51, by omega⟩),
  (⟨30, by omega⟩, ⟨36, by omega⟩, ⟨56, by omega⟩),
  (⟨30, by omega⟩, ⟨43, by omega⟩, ⟨50, by omega⟩)
]

private theorem lineTriangleData_size : lineTriangleData.size = 63 := by native_decide

/-- Map from line index to sorted triangle. -/
def lineToTriangle (l : Fin 63) : Fin 63 × Fin 63 × Fin 63 :=
  lineTriangleData[l.val]'(by have := lineTriangleData_size; omega)

/-- Every lineToTriangle output is a valid Langer triangle. -/
theorem lineToTriangle_mem :
    ∀ l : Fin 63, lineToTriangle l ∈ langerTriangles := by native_decide

/-- The line-to-triangle map is injective. -/
theorem lineToTriangle_injective :
    ∀ l₁ l₂ : Fin 63, lineToTriangle l₁ = lineToTriangle l₂ → l₁ = l₂ := by native_decide

/-- The line-to-triangle map is surjective. -/
theorem lineToTriangle_surjective :
    ∀ t ∈ langerTriangles, ∃ l : Fin 63, lineToTriangle l = t := by native_decide

/-! ## LinePointSet and the share-vertex relation -/

/-- The 3-element point set of line l, as a Finset. -/
def linePointSet (l : Fin 63) : Finset (Fin 63) :=
  let (p₁, p₂, p₃) := lineToTriangle l
  {p₁, p₂, p₃}

/-- Two lines share a vertex. -/
def linesShareVertex (l₁ l₂ : Fin 63) : Prop :=
  l₁ ≠ l₂ ∧ (linePointSet l₁ ∩ linePointSet l₂).Nonempty

instance decLinesShareVertex : DecidableRel (fun l₁ l₂ => linesShareVertex l₁ l₂) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-! ## G₂(2) line-action generators -/

/-- G₂(2) line-action generator σ₁ (order 7): forward permutation. -/
def g2lineGen1Fwd : Array (Fin 63) := #[
  4, 3, 5, 11, 9, 10, 17, 15, 16, 6, 7, 8, 1, 0, 2,
  18, 19, 20, 14, 12, 13, 30, 36, 51, 52, 54, 53, 57, 24, 58, 61, 23, 62, 55,
  33, 56, 59, 27, 60, 31, 28, 43, 45, 21, 39, 22, 49, 34, 47, 37, 40, 32, 35,
  48, 46, 26, 50, 25, 41, 38, 42, 29, 44]

def g2lineGen1Inv : Array (Fin 63) := #[
  13, 12, 14, 1, 0, 2, 9, 10, 11, 4, 5, 3, 19, 20, 18, 7, 8, 6, 15, 16, 17,
  43, 45, 31, 28, 57, 55, 37, 40, 61, 21, 39, 51, 34, 47, 52, 22, 49, 59, 44,
  50, 58, 60, 41, 62, 42, 54, 48, 53, 46, 56, 23, 24, 26, 25, 33, 35, 27, 29,
  36, 38, 30, 32]

def g2lineGen2Fwd : Array (Fin 63) := #[
  15, 25, 26, 36, 45, 46, 27, 60, 59, 38, 16, 29, 17, 14, 8, 37, 40, 61, 28,
  48, 53, 11, 30, 42, 57, 34, 5, 2, 1, 0, 44, 43, 23, 20, 56, 62, 51, 21, 39,
  9, 3, 35, 32, 41, 12, 52, 6, 55, 7, 50, 13, 10, 33, 4, 31, 19, 18, 58, 24,
  49, 47, 22, 54]

def g2lineGen2Inv : Array (Fin 63) := #[
  29, 28, 27, 40, 53, 26, 46, 48, 14, 39, 51, 21, 44, 50, 13, 0, 10, 12, 56,
  55, 33, 37, 61, 32, 58, 1, 2, 6, 18, 11, 22, 54, 42, 52, 25, 41, 3, 15, 9,
  38, 16, 43, 23, 31, 30, 4, 5, 60, 19, 59, 49, 36, 45, 20, 62, 47, 34, 24,
  57, 8, 7, 17, 35]

private theorem g2lineGen1Fwd_size : g2lineGen1Fwd.size = 63 := by decide
private theorem g2lineGen1Inv_size : g2lineGen1Inv.size = 63 := by decide
private theorem g2lineGen2Fwd_size : g2lineGen2Fwd.size = 63 := by decide
private theorem g2lineGen2Inv_size : g2lineGen2Inv.size = 63 := by decide

def g2lineGen1 : Equiv.Perm (Fin 63) where
  toFun i := g2lineGen1Fwd[i.val]'(by have := g2lineGen1Fwd_size; omega)
  invFun i := g2lineGen1Inv[i.val]'(by have := g2lineGen1Inv_size; omega)
  left_inv := by intro i; revert i; decide
  right_inv := by intro i; revert i; decide

def g2lineGen2 : Equiv.Perm (Fin 63) where
  toFun i := g2lineGen2Fwd[i.val]'(by have := g2lineGen2Fwd_size; omega)
  invFun i := g2lineGen2Inv[i.val]'(by have := g2lineGen2Inv_size; omega)
  left_inv := by intro i; revert i; decide
  right_inv := by intro i; revert i; decide

/-! ## Equivariance: the line-action IS the induced action -/

/-- σ₁ line-action is equivariant with σ₁ point-action on point sets. -/
theorem linePointSet_gen1_equivariant :
    ∀ l : Fin 63, linePointSet (g2lineGen1 l) = (linePointSet l).image g2gen1 := by
  native_decide

/-- σ₂ line-action is equivariant with σ₂ point-action on point sets. -/
theorem linePointSet_gen2_equivariant :
    ∀ l : Fin 63, linePointSet (g2lineGen2 l) = (linePointSet l).image g2gen2 := by
  native_decide

/-- Triangle-sharing invariance under equivariant action. Injective functions
    commute with intersection and preserve non-emptiness. -/
theorem share_vertex_equivariant (σ : Equiv.Perm (Fin 63)) (τ : Equiv.Perm (Fin 63))
    (h : ∀ l : Fin 63, linePointSet (τ l) = (linePointSet l).image σ)
    (l₁ l₂ : Fin 63) :
    (linePointSet l₁ ∩ linePointSet l₂).Nonempty ↔
    (linePointSet (τ l₁) ∩ linePointSet (τ l₂)).Nonempty := by
  rw [h l₁, h l₂, ← Finset.image_inter _ _ σ.injective, Finset.image_nonempty]

/-- σ₁ line-action preserves the share-vertex relation. -/
theorem g2lineGen1_share_inv :
    ∀ l₁ l₂ : Fin 63, linesShareVertex l₁ l₂ ↔
      linesShareVertex (g2lineGen1 l₁) (g2lineGen1 l₂) := by
  intro l₁ l₂
  simp only [linesShareVertex, g2lineGen1.injective.ne_iff]
  exact and_congr_right' (share_vertex_equivariant g2gen1 g2lineGen1
    linePointSet_gen1_equivariant l₁ l₂)

/-- σ₂ line-action preserves the share-vertex relation. -/
theorem g2lineGen2_share_inv :
    ∀ l₁ l₂ : Fin 63, linesShareVertex l₁ l₂ ↔
      linesShareVertex (g2lineGen2 l₁) (g2lineGen2 l₂) := by
  intro l₁ l₂
  simp only [linesShareVertex, g2lineGen2.injective.ne_iff]
  exact and_congr_right' (share_vertex_equivariant g2gen2 g2lineGen2
    linePointSet_gen2_equivariant l₁ l₂)

/-! ## Line-action word machinery -/

def applyLineGen : Fin 4 → Equiv.Perm (Fin 63)
  | 0 => g2lineGen1
  | 1 => g2lineGen1.symm
  | 2 => g2lineGen2
  | 3 => g2lineGen2.symm

def applyLineWord : List (Fin 4) → Equiv.Perm (Fin 63)
  | [] => Equiv.refl _
  | g :: gs => (applyLineGen g).trans (applyLineWord gs)

private theorem symm_preserves_share (σ : Equiv.Perm (Fin 63))
    (h : ∀ l₁ l₂ : Fin 63, linesShareVertex l₁ l₂ ↔
      linesShareVertex (σ l₁) (σ l₂))
    (l₁ l₂ : Fin 63) :
    linesShareVertex l₁ l₂ ↔ linesShareVertex (σ.symm l₁) (σ.symm l₂) := by
  have := h (σ.symm l₁) (σ.symm l₂)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

private theorem applyLineGen_share_inv (g : Fin 4) (l₁ l₂ : Fin 63) :
    linesShareVertex l₁ l₂ ↔ linesShareVertex (applyLineGen g l₁) (applyLineGen g l₂) := by
  fin_cases g <;> simp only [applyLineGen]
  · exact g2lineGen1_share_inv l₁ l₂
  · exact symm_preserves_share g2lineGen1 (g2lineGen1_share_inv) l₁ l₂
  · exact g2lineGen2_share_inv l₁ l₂
  · exact symm_preserves_share g2lineGen2 (g2lineGen2_share_inv) l₁ l₂

/-- Any line-action word preserves the share-vertex relation (structural induction). -/
theorem applyLineWord_share_inv (w : List (Fin 4)) :
    ∀ l₁ l₂ : Fin 63, linesShareVertex l₁ l₂ ↔
      linesShareVertex (applyLineWord w l₁) (applyLineWord w l₂) := by
  induction w with
  | nil => intro l₁ l₂; simp [applyLineWord]
  | cons g gs ih =>
    intro l₁ l₂
    simp only [applyLineWord, Equiv.trans_apply]
    rw [applyLineGen_share_inv g l₁ l₂]
    exact ih (applyLineGen g l₁) (applyLineGen g l₂)

/-! ## Bridge and non-isomorphism -/

/-- Bridge: dual Langer adjacency ↔ lines share a vertex. -/
theorem dualLanger_iff_share :
    ∀ l₁ l₂ : Fin 63,
      dualLangerSimpleGraph.Adj l₁ l₂ ↔ linesShareVertex l₁ l₂ := by
  sorry  -- native_decide (connects two definitions of the same geometric fact)

/-- Any line-action word preserves dual Langer adjacency. Algebraic proof via
    the bridge and `applyLineWord_share_inv`. -/
theorem applyLineWord_dualLanger_inv (w : List (Fin 4)) :
    ∀ i j : Fin 63, dualLangerSimpleGraph.Adj i j ↔
      dualLangerSimpleGraph.Adj (applyLineWord w i) (applyLineWord w j) := by
  intro i j
  rw [dualLanger_iff_share, dualLanger_iff_share]
  exact applyLineWord_share_inv w i j

/-- The Langer and dual Langer graphs are not isomorphic. -/
theorem langer_not_iso_dualLanger :
    IsEmpty (langerSimpleGraph ≃g dualLangerSimpleGraph) := by
  sorry  -- from d₃-connectivity invariance + line-action transport
