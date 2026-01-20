import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Order.Basic

open Set Topology
structure Polygon (P : Type*) (n : ℕ)  [NeZero n] [AddCommGroup P] [Module ℝ P] where
  vertices : Fin n → P
  n_ge_3 : n ≥ 3
  adj_distinct : ∀ i, vertices i ≠ vertices (i + 1)
#check @Polygon.vertices

abbrev EuclideanPolygon (n : ℕ) [NeZero n] := Polygon (EuclideanSpace ℝ (Fin 2)) n

#check (EuclideanPolygon 5)
#check @EuclideanPolygon

namespace Polygon

variable {P : Type*} {n : ℕ} [NeZero n]
variable [AddCommGroup P] [Module ℝ P]

def edgeSet (poly : Polygon P n) (i : Fin n) : Set P :=
  segment ℝ (poly.vertices i) (poly.vertices (i + 1))

def edgePath (poly : Polygon P n) (i : Fin n) : ℝ → P :=
  AffineMap.lineMap (poly.vertices i) (poly.vertices (i + 1))

def boundary (poly : Polygon P n) : Set P := ⋃ i, poly.edgeSet i

end Polygon


def myTriangle : Polygon (ℝ × ℝ) 3 where
  vertices := ![(0, 0), (1, 0), (0, 1)]
  n_ge_3 := le_refl 3
  adj_distinct := by
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero]

#check myTriangle.edgePath


def IsSimpleClosedCurve (γ : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2),
    Continuous f ∧ Function.Injective f ∧ range f = γ

axiom jordan_curve_theorem {γ : Set (EuclideanSpace ℝ (Fin 2))} (hγ : IsSimpleClosedCurve γ) :
  ∃ (interior exterior : Set (EuclideanSpace ℝ (Fin 2))),
  γ ∪ interior ∪ exterior = univ  ∧
    IsConnected interior ∧
    IsConnected exterior ∧
    IsOpen interior ∧
    IsOpen exterior ∧
    Bornology.IsBounded interior ∧
    ¬Bornology.IsBounded exterior ∧
    frontier interior = γ ∧
    frontier exterior = γ

structure SimplePolygon (P : Type*) (n : ℕ) [NeZero n] [AddCommGroup P] [Module ℝ P]
    extends Polygon P n where
  simple : ∀ i j : Fin n,
    (j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) →
    Disjoint (toPolygon.edgeSet i) (toPolygon.edgeSet j)

abbrev SimpleEuclideanPolygon (n : ℕ) [NeZero n] :=
  SimplePolygon (EuclideanSpace ℝ (Fin 2)) n

namespace SimplePolygon

variable {n : ℕ} [NeZero n]
variable (poly : SimpleEuclideanPolygon n)

noncomputable def boundaryParam : ℝ → EuclideanSpace ℝ (Fin 2) := fun t =>
    if t = 1 then poly.vertices 0
  else
    let i : Fin n := ⟨⌊t * n⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
    let t' : ℝ := t * n - i
    poly.toPolygon.edgePath i t'


#check @SimplePolygon.boundaryParam

theorem boundaryParam_zero_eq_one : poly.boundaryParam 0 = poly.boundaryParam 1 := by
  simp only [boundaryParam]
  simp
  simp only [Polygon.edgePath]
  simp

theorem boundaryParam_continuousOn_piece (k : Fin n) :
  ContinuousOn poly.boundaryParam (Icc (k / n) ((k + 1) / n)) := by
  unfold boundaryParam
  simp
  let lo : ℝ := k.val / n
  let hi : ℝ := (k.val + 1) / n
  have onPiece : ∀ x ∈ Icc lo hi, (⌊x * n⌋.toNat % n = ↑k ∨ x = hi) := by
    intro x
    intro xin
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    by_cases h : x = hi
    right
    exact h
    simp only [Icc,lo,hi] at xin
    simp only [hi] at h
    push_neg at h
    have neqkplus1 : x * ↑n ≠ ↑↑k + 1 := by
      contrapose! h
      rw [eq_div_iff (ne_of_gt hn)]
      exact h
    have : ↑↑k ≤ x * ↑n ∧ x * ↑n < ↑↑k + 1 := by
      obtain ⟨hlo, hhi⟩ := xin
      constructor
      exact (mul_inv_le_iff₀ hn).mp hlo
      have : x * ↑n ≤ ↑↑k + 1 := by exact (le_div_iff₀ hn).mp hhi
      exact Std.lt_of_le_of_ne this neqkplus1
    left
    have floorEq : ⌊x * ↑n⌋ = ↑k := by
      rw [Int.floor_eq_iff]
      exact_mod_cast this
    simp [floorEq, Int.toNat_natCast, Nat.mod_eq_of_lt k.isLt]
  by_cases last : (k.val + 1 : ℝ) / n = 1
  sorry
  intro x hx
  simp only [lo,hi] at onPiece
  have hx' := onPiece x hx
  rcases hx' with onSegment | atEnd
  have hx1 : x ≠ 1 := by
    intro heq
    subst heq
    have h1 : (1 : ℝ) ≤ hi := hx.2
    have hk_lt : k.val + 1 < n := by
      by_contra h; push_neg at h
      apply last
      have heq : k.val + 1 = n := le_antisymm (Nat.succ_le_of_lt k.isLt) h
      have : (↑↑k + 1 : ℝ) = ↑n := by exact_mod_cast heq
      rw [this, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
    have h2 : hi < 1 := by
      simp only [hi]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      rw [div_lt_one hn_pos]
      norm_cast
    linarith
  apply ContinuousWithinAt.congr_of_eventuallyEq _ (eventually_nhdsWithin_of_forall (fun t ht => ?_))
  simp only [hx1]
  simp
  simp only [onSegment]
  simp only [Fin.eta]
  rfl
  apply Continuous.continuousWithinAt
  unfold Polygon.edgePath
  apply Continuous.comp
  exact AffineMap.lineMap_continuous
  continuity
  have : k + 1 ≠ n := by
    intro h
    apply last
    rw [div_eq_one_iff_eq (Nat.cast_ne_zero.mpr (NeZero.ne n))]
    exact_mod_cast h
  have : (↑k + 1) % n = ↑k + 1 := by
    refine Nat.mod_eq_of_lt ?_
    have := k.isLt
    omega
  have hk_lt : k.val + 1 < n := by omega
  have ht1 : t ≠ 1 := by
    intro heq
    subst heq
    have h1 : (1 : ℝ) ≤ hi := ht.2
    have h2 : hi < 1 := by
      simp only [hi]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      rw [div_lt_one hn_pos]
      norm_cast
    linarith
  simp only [ht1, ↓reduceIte]
  specialize onPiece t
  apply onPiece at ht
  rcases ht with onSegment' | atEnd'
  simp only [onSegment']
  simp only [atEnd']
  simp
  simp only [this]
  simp
  simp only [Polygon.edgePath]
  simp
  congr 1
  apply Fin.ext
  simp only [Fin.val_add]
  rw[← this]
  norm_num
  have hx1 : x ≠ 1 := by
    intro heq
    subst heq
    have h1 : (1 : ℝ) ≤ hi := hx.2
    have hk_lt : k.val + 1 < n := by
      by_contra h; push_neg at h
      apply last
      have heq : k.val + 1 = n := le_antisymm (Nat.succ_le_of_lt k.isLt) h
      have : (↑↑k + 1 : ℝ) = ↑n := by exact_mod_cast heq
      rw [this, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
    have h2 : hi < 1 := by
      simp only [hi]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      rw [div_lt_one hn_pos]
      norm_cast
    linarith
  subst atEnd
  refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun t => poly.edgePath k (t * ↑n - ↑↑k)) ?cont ?eq_on ?eq_at
  apply Continuous.continuousWithinAt
  simp only [Polygon.edgePath]
  continuity
  apply eventually_nhdsWithin_of_forall
  intro x hx'
  have hx1 : x ≠ 1 := by
    have hk_le : k.val + 1 ≤ n := by omega
    have hk_lt : k.val + 1 < n := by
      exact Nat.lt_of_le_of_ne hk_le (by omega : k.val + 1 ≠ n)
    have hx_le : x ≤ (↑↑k + 1)/↑n := by
      exact (Set.mem_Icc.mp hx').right
    have h : (↑↑k + 1)/↑n < 1 := by
      have h1 : (↑↑k + 1 : ℝ) < (n : ℝ) := by
        norm_cast
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    have xle1 : x < 1 := by
      have h' : (↑↑k + 1 : ℝ) / ↑n < 1 := by
        have hk_lt : k.val + 1 < n := by omega
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
        rw [div_lt_one hn_pos]
        norm_cast
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      linarith
    exact Ne.symm (ne_of_gt xle1)
  simp only [hx1, ↓reduceIte]
  specialize onPiece x
  apply onPiece at hx'
  rcases hx' with onSegment | atEnd
  simp only [onSegment]
  subst atEnd
  simp
  have hk_lt : k.val + 1 < n := by
    by_contra h
    push_neg at h
    have hle : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have heq : k.val + 1 = n := le_antisymm hle h
    apply last
    have heq' : (↑↑k + 1 : ℝ) = (n : ℝ) := by exact_mod_cast heq
    rw [heq']
    field_simp
    simp
  have : (↑k + 1) % n = ↑k + 1 := by
    exact Nat.mod_eq_of_lt hk_lt
  simp only [this,Polygon.edgePath]
  simp
  congr 1
  ext
  simp only [Fin.val_add]
  convert (Nat.mod_eq_of_lt hk_lt).symm
  simp
  exact Nat.mod_eq_of_lt (by omega : 1 < n)
  simp only [hx1, ↓reduceIte]
  simp
  have hk_lt : k.val + 1 < n := by
    by_contra h
    push_neg at h
    have hle : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have heq : k.val + 1 = n := le_antisymm hle h
    apply last
    have heq' : (↑↑k + 1 : ℝ) = (n : ℝ) := by exact_mod_cast heq
    rw [heq']
    field_simp
    simp
  have mod_eq : (k.val + 1) % n = k.val + 1 := Nat.mod_eq_of_lt hk_lt
  simp only [mod_eq, Polygon.edgePath]
  have param_eq : (↑↑k + 1 : ℝ) - ↑(k.val + 1) = 0 := by simp
  simp only [param_eq, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  congr 1
  ext
  simp only [Fin.val_add]
  have hk_lt : k.val + 1 < n := by
    by_contra h
    push_neg at h
    have hle : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have heq : k.val + 1 = n := le_antisymm hle h
    apply hx1
    have : (↑↑k + 1 : ℝ) = ↑n := by exact_mod_cast heq
    rw [this, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
  have h1 : (1 : Fin n).val = 1 := by
    exact Nat.mod_eq_of_lt (by omega : 1 < n)
  rw [h1]
  exact mod_eq.symm






theorem boundaryParam_continuousOn : ContinuousOn poly.boundaryParam (Icc 0 1) := by
  unfold boundaryParam

  sorry

noncomputable def circleMap : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2) :=
  AddCircle.liftIco 1 0 poly.boundaryParam

theorem circleMap_continuous : Continuous poly.circleMap := by
  sorry

theorem circleMap_injective : Function.Injective poly.circleMap := by
  sorry

theorem circleMap_range : range poly.circleMap = poly.toPolygon.boundary := by
  sorry

theorem boundary_isSimpleClosedCurve : IsSimpleClosedCurve poly.toPolygon.boundary :=
  ⟨poly.circleMap, poly.circleMap_continuous, poly.circleMap_injective, poly.circleMap_range⟩

end SimplePolygon
