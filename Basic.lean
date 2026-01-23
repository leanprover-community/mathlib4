import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.LocallyFinite
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

theorem edgeSet_eq_image (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet i = poly.edgePath i '' Icc (0 : ℝ) 1 := by
  simp only [edgeSet, edgePath, segment_eq_image_lineMap]

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

structure JordanDecomposition (γ : Set (EuclideanSpace ℝ (Fin 2))) where
  interior : Set (EuclideanSpace ℝ (Fin 2))
  exterior : Set (EuclideanSpace ℝ (Fin 2))
  partition : γ ∪ interior ∪ exterior = univ
  interior_isConnected : IsConnected interior
  exterior_isConnected : IsConnected exterior
  interior_isOpen : IsOpen interior
  exterior_isOpen : IsOpen exterior
  interior_isBounded : Bornology.IsBounded interior
  exterior_not_bounded : ¬Bornology.IsBounded exterior
  frontier_interior : frontier interior = γ
  frontier_exterior : frontier exterior = γ

noncomputable axiom jordan_curve_theorem {γ : Set (EuclideanSpace ℝ (Fin 2))}
    (hγ : IsSimpleClosedCurve γ) : JordanDecomposition γ


structure SimplePolygon (P : Type*) (n : ℕ) [NeZero n] [AddCommGroup P] [Module ℝ P]
    extends Polygon P n where
  non_adjacent_disjoint : ∀ i j : Fin n,
    (j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) →
    Disjoint (toPolygon.edgeSet i) (toPolygon.edgeSet j)

  adjacent_inter: ∀ i : Fin n, (toPolygon.edgeSet i ∩ toPolygon.edgeSet (i + 1))
        = ({toPolygon.vertices (i + 1)} : Set P)

abbrev SimpleEuclideanPolygon (n : ℕ) [NeZero n] :=
  SimplePolygon (EuclideanSpace ℝ (Fin 2)) n

namespace SimplePolygon

variable {n : ℕ} [NeZero n]
variable (poly : SimpleEuclideanPolygon n)
#check poly.adjacent_inter

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

theorem boundaryParam_continuousOn_piece (k : Fin n) : ContinuousOn poly.boundaryParam (Icc (k / n) ((k.val + 1) / n)) := by
  unfold boundaryParam
  simp
  let lo : ℝ := k.val / n
  let hi : ℝ := (k.val + 1) / n
  have onPiece : ∀ x ∈ Icc lo hi, (⌊x * n⌋.toNat % n = ↑k ∨ x = hi) := by
    intro x xin
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
  intro x hx
  have hk_eq : k.val + 1 = n := by
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have h := div_eq_one_iff_eq hn |>.mp last
    exact_mod_cast h
  by_cases hx1 : x = 1
  subst hx1
  refine ContinuousWithinAt.congr_of_eventuallyEq
    (f := fun t => poly.toPolygon.edgePath k (t * ↑n - ↑↑k)) ?_ ?_ ?_
  · apply Continuous.continuousWithinAt
    unfold Polygon.edgePath
    continuity
  · apply eventually_nhdsWithin_of_forall
    intro t ht
    by_cases ht1 : t = 1
    · subst ht1
      simp only [↓reduceIte, one_mul, Polygon.edgePath]
      have hparam : (↑n : ℝ) - ↑↑k = 1 := by
        have hkval : k.val = n - 1 := by omega
        have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
        have : (n : ℝ) - (n - 1 : ℕ) = 1 := by
          rw [Nat.cast_sub hn_pos]
          ring
        rw [hkval]
        exact this
      rw [hparam, AffineMap.lineMap_apply_one]
      congr 1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_zero]
      have h1 : (1 : Fin n).val = 1 % n := rfl
      simp only [h1, Nat.add_mod_mod, hk_eq, Nat.mod_self]
    · simp only [ht1, ↓reduceIte]
      have ht' := onPiece t ht
      rcases ht' with hfloor | heq
      · simp only [hfloor]
      · simp only [hi] at heq
        rw [last] at heq
        exact absurd heq ht1
  · -- eq_at: show they agree at t = 1
    simp only [↓reduceIte, one_mul, Polygon.edgePath]
    have hparam : (↑n : ℝ) - ↑↑k = 1 := by
      have hkval : k.val = n - 1 := by omega
      have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
      have : (n : ℝ) - (n - 1 : ℕ) = 1 := by
        rw [Nat.cast_sub hn_pos]
        ring
      rw [hkval]
      exact this
    rw [hparam, AffineMap.lineMap_apply_one]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_zero]
    have h1 : (1 : Fin n).val = 1 % n := rfl
    simp only [h1, Nat.add_mod_mod, hk_eq, Nat.mod_self]
  simp only [lo,hi] at onPiece
  have hx' := onPiece x hx
  rcases hx' with onSegment | atEnd
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
  by_cases ht1 : t = 1
  simp only [ht1, if_true]
  have hparam : (1 : ℝ) * ↑n - ↑↑k = 1 := by
    have h := div_eq_one_iff_eq (Nat.cast_ne_zero.mpr (NeZero.ne n)) |>.mp last
    field_simp
    linarith
  rw [hparam]
  simp only [Polygon.edgePath]
  simp
  congr 1
  have : (k + 1 : Fin n).val = 0 := by
    simp [Fin.val_add]
    simp [hk_eq]
  exact Fin.ext this.symm
  simp only [ht1, ite_false]
  congr 1
  ext
  exact (onPiece t ht).resolve_right (fun h => ht1 (last ▸ h))
  congr 1
  exact_mod_cast (onPiece t ht).resolve_right (fun h => ht1 (last ▸ h))
  exact absurd (atEnd.trans last) hx1
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
      refine Nat.lt_of_le_of_ne hk_le ?_
      intro heq
      apply last
      have h : (↑↑k + 1 : ℝ) = ↑n := by
        exact_mod_cast heq
      rw [h, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
    have hx_le : x ≤ (↑↑k + 1)/↑n := by
      exact (Set.mem_Icc.mp hx').right
    have h : (↑↑k + 1)/↑n < 1 := by
      have h1 : (↑↑k + 1 : ℝ) < (n : ℝ) := by
        norm_cast
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      exact Nat.div_lt_one_iff (NeZero.pos n) |>.mpr hk_lt
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
  have hn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have cover :
      (Icc (0:ℝ) 1) = ⋃ k : Fin n, Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ)) := by

        sorry
  have contOnCover :
      ContinuousOn poly.boundaryParam
        (⋃ k : Fin n, Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))) := by
    have hloc :
        LocallyFinite (fun k : Fin n => Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))) :=
      locallyFinite_of_finite (fun k : Fin n => Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ)))
    refine (LocallyFinite.continuousOn_iUnion (g := poly.boundaryParam) (f := fun k : Fin n =>
      Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))) hloc ?_ ?_)
    · intro k
      simpa using (isClosed_Icc :
        IsClosed (Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))))
    · intro k
      simpa using poly.boundaryParam_continuousOn_piece k
  simpa [cover] using contOnCover

noncomputable def circleMap : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2) :=
  AddCircle.liftIco 1 0 poly.boundaryParam

theorem circleMap_continuous : Continuous poly.circleMap := by
  apply AddCircle.liftIco_continuous
  simpa using poly.boundaryParam_zero_eq_one
  · simpa using poly.boundaryParam_continuousOn

theorem edgePaths_injOn_Ico : ∀ i : Fin n, InjOn (poly.edgePath i) (Ico 0 1) := by
  unfold Polygon.edgePath
  intro i x hx y hy h
  have hv : poly.vertices i ≠ poly.vertices (i + 1) := poly.toPolygon.adj_distinct i
  set v0 := poly.vertices i
  set v1 := poly.vertices (i + 1)
  have hdir : (v1 - v0) ≠ 0 := by
    -- v1 - v0 = 0 ↔ v1 = v0
    simp [sub_eq_zero]
    push_neg
    exact Ne.symm (poly.adj_distinct i)
  -- rewrite lineMap to v0 + t • (v1 - v0)
  have h' : v0 + x • (v1 - v0) = v0 + y • (v1 - v0) := by
    -- If this `simpa` doesn't work in your file, see note below.
    simpa [v0, v1, AffineMap.lineMap_apply] using h
  -- cancel v0
  have h'' : x • (v1 - v0) = y • (v1 - v0) := by
    exact add_left_cancel h'
  -- turn that into (x - y) • (v1 - v0) = 0
  have hxmy : (x - y) • (v1 - v0) = 0 := by
    have : x • (v1 - v0) - y • (v1 - v0) = 0 := by
      simpa using (sub_eq_zero.mpr h'')
    simpa [sub_smul] using this

  -- now scalar * nonzero vector = 0 ⇒ scalar = 0
  have : x - y = 0 := (smul_eq_zero.mp hxmy).resolve_right hdir
  exact sub_eq_zero.mp this

theorem boundaryParam_injOn_Ico : InjOn poly.boundaryParam (Ico 0 1) := by
  intro x hx y hy hxy
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hx_ne1 : x ≠ (1:ℝ) := ne_of_lt hx.2
  have hy_ne1 : y ≠ (1:ℝ) := ne_of_lt hy.2
  simp [boundaryParam, hx_ne1, hy_ne1] at hxy
  set ix : Fin n :=
      ⟨⌊x * (n : ℝ)⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
  set iy : Fin n :=
      ⟨⌊y * (n : ℝ)⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
  by_cases h : ix = iy
  simp only [h] at hxy
  #check edgePaths_injOn_Ico poly iy
  have htx :
    x * (n : ℝ) - (⌊x * (n : ℝ)⌋.toNat % n : ℝ) ∈ Ico (0:ℝ) 1 := by
    have hx_mul_lt : x * (n : ℝ) < (n : ℝ) := by
      nlinarith [hx.2, npos]
    have hx_mul_nonneg : 0 ≤ x * (n : ℝ) := by
      nlinarith [hx.1, le_of_lt npos]
    have hfloor_nonneg : 0 ≤ (⌊x * (n : ℝ)⌋ : ℤ) :=
      Int.floor_nonneg.mpr hx_mul_nonneg
    have hfloor_lt_n : (⌊x * (n : ℝ)⌋ : ℤ) < n :=
      Int.floor_lt.mpr hx_mul_lt
    have hfloor_toNat : (⌊x * (n : ℝ)⌋.toNat : ℤ) = ⌊x * (n : ℝ)⌋ :=
      Int.toNat_of_nonneg hfloor_nonneg
    have hfloor_toNat_lt : ⌊x * (n : ℝ)⌋.toNat < n := by
      have : (⌊x * (n : ℝ)⌋.toNat : ℤ) < n := by
        simpa [hfloor_toNat] using hfloor_lt_n
      exact Int.ofNat_lt.mp this
    have hmod_eq :
        ⌊x * (n : ℝ)⌋.toNat % n = ⌊x * (n : ℝ)⌋.toNat := by
        exact Nat.mod_eq_of_lt hfloor_toNat_lt


    sorry
  sorry



  sorry

theorem circleMap_injective : Function.Injective poly.circleMap := by
  unfold Function.Injective
  intro a₁ a₂
  unfold circleMap
  simp only [AddCircle.liftIco, AddCircle.equivIco]
  simp
  simp only [QuotientAddGroup.equivIcoMod ]
  simp
  intro h
  set t₁ := AddCircle.equivIco 1 0 a₁ with ht₁_def
  set t₂ := AddCircle.equivIco 1 0 a₂ with ht₂_def
  have ht₁_mem : t₁.val ∈ Ico (0 : ℝ) 1 := by simpa using t₁.property
  have ht₂_mem : t₂.val ∈ Ico (0 : ℝ) 1 := by simpa using t₂.property
  have heq : t₁.val = t₂.val := poly.boundaryParam_injOn_Ico ht₁_mem ht₂_mem h
  have : t₁ = t₂ := Subtype.ext heq
  calc a₁ = (AddCircle.equivIco 1 0).symm t₁ := by simp [ht₁_def]
    _ = (AddCircle.equivIco 1 0).symm t₂ := by rw [this]
    _ = a₂ := by simp [ht₂_def]

theorem circleMap_range : range poly.circleMap = poly.toPolygon.boundary := by
  unfold circleMap Polygon.boundary
  ext p
  simp only [mem_range, mem_iUnion]
  constructor
  · -- Forward: if p is in the range of circleMap, it's in some edgeSet
    intro ⟨a, ha⟩
    -- Get the representative t ∈ [0, 1)
    let t := (AddCircle.equivIco 1 0 a).val
    have ht_mem : t ∈ Ico (0 : ℝ) 1 := by simpa using (AddCircle.equivIco 1 0 a).property
    have ht1 : t ≠ 1 := ne_of_lt ht_mem.2
    -- The segment index
    let i : Fin n := ⟨⌊t * n⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
    use i
    -- boundaryParam t ∈ edgeSet i
    simp only [Polygon.edgeSet]
    -- liftIco applies boundaryParam to the representative
    simp only [AddCircle.liftIco, Function.comp_apply, Set.restrict_apply] at ha
    simp only [boundaryParam] at ha
    rw [← ha]
    -- edgePath i (t * n - i) is in segment
    unfold Polygon.edgePath
    -- Need to show lineMap is in segment for parameter in [0, 1]
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    -- First, establish that i.val = ⌊t * n⌋ (since t * n < n)
    have ht_mul_n_lt : t * n < n := by
      have ht1 : t < 1 := ht_mem.2
      have : t * n < 1 * n := by nlinarith
      linarith
    have ht_mul_n_nonneg : 0 ≤ t * n := by
      have h0 : 0 ≤ t := ht_mem.1
      nlinarith
    have hfloor_nonneg : 0 ≤ ⌊t * n⌋ := Int.floor_nonneg.mpr ht_mul_n_nonneg
    have hfloor_lt_n : ⌊t * n⌋ < n := Int.floor_lt.mpr ht_mul_n_lt
    have hfloor_toNat : (⌊t * n⌋.toNat : ℤ) = ⌊t * n⌋ := Int.toNat_of_nonneg hfloor_nonneg
    have hfloor_toNat_lt : ⌊t * n⌋.toNat < n := by
      have : (⌊t * n⌋.toNat : ℤ) < n := hfloor_toNat ▸ hfloor_lt_n
      exact Int.ofNat_lt.mp this
    have hmod_eq : ⌊t * n⌋.toNat % n = ⌊t * n⌋.toNat := Nat.mod_eq_of_lt hfloor_toNat_lt
    have hi_val : (i.val : ℝ) = ⌊t * n⌋ := by
      simp only [i, hmod_eq]
      have : (⌊t * n⌋.toNat : ℝ) = (⌊t * n⌋.toNat : ℤ) := by norm_cast
      rw [this, hfloor_toNat]
    -- The parameter t * n - i is in [0, 1]
    have hparam_nonneg : 0 ≤ t * n - i := by
      rw [hi_val]
      exact sub_nonneg.mpr (Int.floor_le (t * n))
    have hparam_le_one : t * n - i ≤ 1 := by
      rw [hi_val]
      have := Int.lt_floor_add_one (t * n)
      linarith
    split_ifs with ht1'
    · -- Case t = 1, contradicts ht1
      exact absurd ht1' ht1
    · -- Case t ≠ 1
      rw [segment_eq_image_lineMap]
      have hparam_mem : t * n - i ∈ Icc (0 : ℝ) 1 := ⟨hparam_nonneg, hparam_le_one⟩
      exact mem_image_of_mem _ hparam_mem
  · -- Backward: if p is in some edgeSet, it's in the range of circleMap
    intro h
    rcases h with ⟨i, hi⟩
    rw[poly.edgeSet_eq_image i,mem_image] at hi
    rcases hi with ⟨t, htmem⟩
    let s : ℝ := (i.val + t) / n
    by_cases s1 : s = 1
    have nit : n = (i : ℕ)  + t := by
      have hn0 : ( (n : ℝ) ) ≠ 0 := by
        exact_mod_cast (NeZero.ne n)

      have hs : ((↑↑i + t) / (n : ℝ)) = (1 : ℝ) := by
        simpa [s] using s1

      have h : (↑↑i + t) = (1 : ℝ) * (n : ℝ) := by
        exact (div_eq_iff hn0).1 hs
      simpa [one_mul, add_comm, add_left_comm, add_assoc] using h.symm
    have tle1 : t ≤ 1 := (Set.mem_Icc.mp htmem.left).right
    have nlei1 : n ≤ (i : ℕ) + 1 := by
      have hreal : (n : ℝ) ≤ (i : ℝ) + 1 := by
        linarith [nit, tle1]
      exact_mod_cast hreal
    have : n ≥ (i : ℕ) + 1 := Nat.succ_le_of_lt i.isLt
    have ni1 : n = (i : ℕ) + 1 := by exact Nat.le_antisymm nlei1 this
    have t1 : t = 1 := by
      have hthisR : (n : ℝ) = (i : ℝ) + 1 := by
      -- cast `this` to ℝ
        have := congrArg (fun m : ℕ => (m : ℝ)) ni1
        -- simplify the cast of `(i : ℕ) + 1`
        simpa [Nat.cast_add, Nat.cast_one] using this

      have hit : (i : ℝ) + t = (i : ℝ) + 1 := by
        -- rewrite `(n:ℝ)` using `nit` and `hthisR`
        calc
          (i : ℝ) + t = (n : ℝ) := by simpa using nit.symm
          _ = (i : ℝ) + 1 := hthisR

      exact add_left_cancel hit
    have hp : p = poly.edgePath i 1 := by
      calc
        p = poly.edgePath i t := by simpa using htmem.2.symm
        _ = poly.edgePath i 1 := by simp [t1]
    unfold Polygon.edgePath at hp
    simp at hp
    have hn3 : (3 : ℕ) ≤ n := poly.n_ge_3
    have h1lt : (1 : ℕ) < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hn3
    have hmod : ((i : ℕ) + 1) % n = 0 := by
      -- rewrite the denominator using ni1, so it's x % x
      simp [ni1]
    have hi_add_one : (i + 1 : Fin n) = 0 := by
      apply Fin.ext
      -- (i+1).val = (i.val + 1) % n
      -- and 0.val = 0
      simp [Fin.val_add, hmod]
    have hwrap : poly.vertices (i + 1) = poly.vertices 0 := by
      simp [hi_add_one]

    rw[hp]
    simp[hwrap]
    unfold boundaryParam
    use (0 : AddCircle (1:ℝ))
    simp
    have h0 : (0 : ℝ) ∈ Set.Ico (0:ℝ) (0 + (1:ℝ)) := by simp
    let f : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun t =>
        if t = 1 then poly.vertices 0
        else
          poly.edgePath
            ⟨⌊t * (n:ℝ)⌋.toNat % n, by
              simpa using (by
                exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))
                )⟩
            (t * (n:ℝ) - (⌊t * (n:ℝ)⌋.toNat % n : ℕ))
    have hlift : AddCircle.liftIco (1:ℝ) 0 f 0 = f 0 := by
  -- `0` in AddCircle is the coercion of `⟨0,h0⟩`
      simpa [f] using
        (AddCircle.liftIco_coe_apply (p := (1:ℝ)) (a := (0:ℝ)) (f := f) (x := (0:ℝ)) h0)
    rw [hlift]
    simp [f]
    simp only [Polygon.edgePath]
    simp
    use s
    simp only [AddCircle.liftIco, Function.comp_apply, Set.restrict_apply]
    have hs_nonneg : 0 ≤ s := by
      simp only [s]
      apply div_nonneg
      · have := htmem.1.1; linarith
      · exact le_of_lt (Nat.cast_pos.mpr (NeZero.pos n))

    have hs_le_one : s ≤ 1 := by
      simp only [s]
      rw [div_le_one (Nat.cast_pos.mpr (NeZero.pos n))]
      have hi_nat : i.val ≤ n - 1 := by omega
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
      have hi : (i.val : ℝ) ≤ n - 1 := by
        have : (n - 1 : ℕ) = (n : ℝ) - 1 := by simp [Nat.cast_sub hn1]
        calc (i.val : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hi_nat
          _ = n - 1 := this
      linarith [htmem.1.2]
    have hs_lt_one : s < 1 := lt_of_le_of_ne hs_le_one s1
    have hrep : ↑((AddCircle.equivIco (1 : ℝ) 0) (s : AddCircle (1 : ℝ))) = s := by
      have hs_mem : s ∈ Ico (0 : ℝ) (0 + 1) := by simp [hs_nonneg, hs_lt_one]
      simp [AddCircle.equivIco_coe_eq hs_mem]
    rw[hrep]
    simp only [boundaryParam, if_neg s1]
    have : ⌊s * ↑n⌋.toNat % n = ↑i ∨ s = (↑↑i + 1) / ↑n := by
      have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      by_cases ht1 : t = 1
      · -- t = 1 means s = (i + 1) / n
        right
        simp only [s, ht1]
      · -- t < 1 means floor lands on i
        left
        have ht_lt_one : t < 1 := lt_of_le_of_ne htmem.1.2 ht1
        have hsn_eq : s * n = i.val + t := by simp only [s]; field_simp
        have hlo : (i.val : ℝ) ≤ s * n := by rw [hsn_eq]; linarith [htmem.1.1]
        have hhi : s * n < i.val + 1 := by rw [hsn_eq]; linarith
        have floorEq : ⌊s * n⌋ = i.val := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast hlo
          · exact_mod_cast hhi
        simp [floorEq, Int.toNat_natCast, Nat.mod_eq_of_lt i.isLt]
    rcases this with onSegment | atEdge
    simp only [onSegment]
    simp
    have : (s * ↑n - ↑↑i) = t := by
      simp only [s]
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      field_simp
      ring
    rw[this]
    exact htmem.right
    have : ⌊s * ↑n⌋.toNat % n = ↑i + 1 := by
      rw [atEdge]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      -- Simplify (i + 1) / n * n = i + 1
      rw [div_mul_cancel₀ _ hn_ne]
      -- ⌊i + 1⌋ = i + 1 since it's a nat
      have heq : (↑↑i + 1 : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by simp
      rw [heq, Int.floor_natCast, Int.toNat_natCast]
      -- (i + 1) % n = i + 1 since i + 1 < n
      have hi_lt : i.val + 1 < n := by
        have h : s < 1 := hs_lt_one
        rw [atEdge, div_lt_one hn_pos] at h
        exact_mod_cast h
      exact Nat.mod_eq_of_lt hi_lt
    simp only [this]
    simp
    have : s * ↑n = i + 1 := by
      rw [atEdge]
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      field_simp
    simp only [this]
    simp
    rw[← htmem.right]
    have t1 : t = 1 := by
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      have hs_eq : (i.val + t : ℝ) / n = s := rfl
      rw [atEdge] at hs_eq
      field_simp at hs_eq
      linarith
    simp only [t1]
    unfold Polygon.edgePath
    simp
    congr 1
    apply Fin.ext
    simp only [Fin.val_add]
    have hi_lt : i.val + 1 < n := by
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      have h : s < 1 := hs_lt_one
      rw [atEdge, div_lt_one hn_pos] at h
      exact_mod_cast h
    simp only [Fin.val_one']
    have h1_lt : 1 < n := by omega
    rw [Nat.mod_eq_of_lt h1_lt]
    exact (Nat.mod_eq_of_lt hi_lt).symm

theorem boundary_isSimpleClosedCurve : IsSimpleClosedCurve poly.toPolygon.boundary :=
  ⟨poly.circleMap, poly.circleMap_continuous, poly.circleMap_injective, poly.circleMap_range⟩

noncomputable def jordanDecomp (poly : SimpleEuclideanPolygon n) :
    JordanDecomposition poly.toPolygon.boundary :=
  jordan_curve_theorem (γ := poly.toPolygon.boundary) (boundary_isSimpleClosedCurve poly)


end SimplePolygon
