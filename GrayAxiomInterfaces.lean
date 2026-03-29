import GrayNumber
import GrayOperations
import Mathlib.Tactic

/-!
# Grey Theory Axiom Interfaces

This module packages the semantic interfaces that are intended to be migrated
out of `GrayAxioms.lean` first.

The file contains no project research axioms. It only records gray-system-facing
interfaces together with a few nontrivial derived lemmas, so that later PRs can
move the interface layer independently of the research-layer axioms.

Round1 baseline includes this interface module for A1-A4 and A6-facing contracts.
-/

/--
Gray-system-facing interface for the A1-A4 layer.

This keeps the subject at `GrayNumber` level (instead of only a set-function view)
and records the required operations/constants semantically.
-/
-- [AxiomTrack] round1=include(A1-A4-interface); role=base-interface
class IsGrayA1A4
  (grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber)
  (white : GrayNumber)
  (fullSpace : GrayNumber) : Prop where
  /-- A1: greyness range on gray numbers. -/
  range : ∀ g : GrayNumber, 0 ≤ g.greyness ∧ g.greyness ≤ 1
  /-- A2: white element has greyness `0`. -/
  white_zero : white.greyness = 0
  /-- A3: universe element has greyness `1`. -/
  fullSpace_one : fullSpace.greyness = 1
  /-- A4 (monotone-style union/intersection bounds). -/
  union_lower : ∀ g1 g2 : GrayNumber,
    max g1.greyness g2.greyness ≤ (grayUnion g1 g2).greyness
  inter_upper : ∀ g1 g2 : GrayNumber,
    (grayInter g1 g2).greyness ≤ min g1.greyness g2.greyness

/-- A1 as a standalone proposition: greyness range on all gray numbers. -/
def grayAxiom1_range : Prop :=
  ∀ g : GrayNumber, 0 ≤ g.greyness ∧ g.greyness ≤ 1

/-- A2 as a standalone proposition: white element has greyness `0`. -/
def grayAxiom2_white_zero (white : GrayNumber) : Prop :=
  white.greyness = 0

/-- A3 as a standalone proposition: universe element has greyness `1`. -/
def grayAxiom3_fullSpace_one (fullSpace : GrayNumber) : Prop :=
  fullSpace.greyness = 1

/-- A4 as a standalone proposition: union/intersection greyness bounds. -/
def grayAxiom4_union_inter_bounds
    (grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber) : Prop :=
  (∀ g1 g2 : GrayNumber,
    max g1.greyness g2.greyness ≤ (grayUnion g1 g2).greyness) ∧
  (∀ g1 g2 : GrayNumber,
    (grayInter g1 g2).greyness ≤ min g1.greyness g2.greyness)

/--
A5 as a standalone proposition: add/sub greyness is a convex combination.

This mirrors the current repository split where A5 is represented by two
constraints in `GrayOperationAxioms.lean` and one compositional interface here.
-/
def grayAxiom5_add_sub_composite : Prop :=
  ∀ g1 g2 : GrayNumber, ∃ w1 w2 : ℝ,
    0 ≤ w1 ∧ 0 ≤ w2 ∧ w1 + w2 = 1 ∧
    (gray_add g1 g2).greyness = w1 * g1.greyness + w2 * g2.greyness ∧
    (gray_sub g1 g2).greyness = w1 * g1.greyness + w2 * g2.greyness

/--
BookAxiomSet-style aggregate class for A1-A5 over current gray interfaces.
-/
class GrayA1A5Set
  (grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber)
  (white : GrayNumber)
  (fullSpace : GrayNumber) : Prop where
  axiom1 : grayAxiom1_range
  axiom2 : grayAxiom2_white_zero white
  axiom3 : grayAxiom3_fullSpace_one fullSpace
  axiom4 : grayAxiom4_union_inter_bounds grayUnion grayInter
  axiom5 : grayAxiom5_add_sub_composite

/--
Minimal operation-level interface for replacing the research axiom
`greyness_non_decreasing` in downstream lemmas.
-/
class IsGraySystemOp (op : GrayNumber → GrayNumber → GrayNumber) : Prop where
  greyness_nondec : ∀ g1 g2 : GrayNumber,
    max g1.greyness g2.greyness ≤ (op g1 g2).greyness

namespace IsGrayA1A4

theorem greyness_nonneg
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    (g : GrayNumber) : 0 ≤ g.greyness :=
  (IsGrayA1A4.range (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace) g).1

theorem greyness_le_one
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    (g : GrayNumber) : g.greyness ≤ 1 :=
  (IsGrayA1A4.range (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace) g).2

theorem union_ge_left
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    (g1 g2 : GrayNumber) : g1.greyness ≤ (grayUnion g1 g2).greyness := by
  exact le_trans (le_max_left _ _)
    (IsGrayA1A4.union_lower (grayUnion := grayUnion) (grayInter := grayInter)
      (white := white) (fullSpace := fullSpace) g1 g2)

theorem union_ge_right
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    (g1 g2 : GrayNumber) : g2.greyness ≤ (grayUnion g1 g2).greyness := by
  exact le_trans (le_max_right _ _)
    (IsGrayA1A4.union_lower (grayUnion := grayUnion) (grayInter := grayInter)
      (white := white) (fullSpace := fullSpace) g1 g2)

theorem inter_le_left
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    (g1 g2 : GrayNumber) : (grayInter g1 g2).greyness ≤ g1.greyness := by
  exact le_trans
    (IsGrayA1A4.inter_upper (grayUnion := grayUnion) (grayInter := grayInter)
      (white := white) (fullSpace := fullSpace) g1 g2)
    (min_le_left _ _)

theorem inter_le_right
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    (g1 g2 : GrayNumber) : (grayInter g1 g2).greyness ≤ g2.greyness := by
  exact le_trans
    (IsGrayA1A4.inter_upper (grayUnion := grayUnion) (grayInter := grayInter)
      (white := white) (fullSpace := fullSpace) g1 g2)
    (min_le_right _ _)

end IsGrayA1A4

namespace IsGraySystemOp

theorem greyness_ge_left
    {op : GrayNumber → GrayNumber → GrayNumber}
    [hOp : IsGraySystemOp op]
    (g1 g2 : GrayNumber) : g1.greyness ≤ (op g1 g2).greyness := by
  exact le_trans (le_max_left _ _) (hOp.greyness_nondec g1 g2)

theorem greyness_ge_right
    {op : GrayNumber → GrayNumber → GrayNumber}
    [hOp : IsGraySystemOp op]
    (g1 g2 : GrayNumber) : g2.greyness ≤ (op g1 g2).greyness := by
  exact le_trans (le_max_right _ _) (hOp.greyness_nondec g1 g2)

end IsGraySystemOp

/--
Semantic interface corresponding to the operation-side axioms (A5-A6 style)
over `GrayNumber`.

This is intentionally split into two interfaces so each part can be reviewed and
upstreamed independently.
-/
class IsGrayAddSubGreynessComposite : Prop where
  add_sub_greyness_formula :
    ∀ g1 g2 : GrayNumber, ∃ w1 w2 : ℝ,
      0 ≤ w1 ∧ 0 ≤ w2 ∧ w1 + w2 = 1 ∧
      (gray_add g1 g2).greyness = w1 * g1.greyness + w2 * g2.greyness ∧
      (gray_sub g1 g2).greyness = w1 * g1.greyness + w2 * g2.greyness

class IsGrayMulDivGreynessNondec : Prop where
  mul_greyness_nondec :
    ∀ g1 g2 : GrayNumber,
      max g1.greyness g2.greyness ≤ (gray_mul g1 g2).greyness
  div_greyness_nondec :
    ∀ g1 g2 : GrayNumber, ∀ h : g2.kernel ≠ 0,
      max g1.greyness g2.greyness ≤ (gray_div g1 g2 h).greyness

class IsGrayA5A6 : Prop extends IsGrayAddSubGreynessComposite, IsGrayMulDivGreynessNondec

-- [AxiomTrack] round1=include(A6-interface); role=base-interface

theorem grayAxiom1_from_space
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace] :
    grayAxiom1_range := by
  intro g
  exact IsGrayA1A4.range
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace) g

theorem grayAxiom2_from_space
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace] :
    grayAxiom2_white_zero white :=
  IsGrayA1A4.white_zero
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace)

theorem grayAxiom3_from_space
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace] :
    grayAxiom3_fullSpace_one fullSpace :=
  IsGrayA1A4.fullSpace_one
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace)

theorem grayAxiom4_from_space
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace] :
    grayAxiom4_union_inter_bounds grayUnion grayInter := by
  refine ⟨?_, ?_⟩
  · intro g1 g2
    exact IsGrayA1A4.union_lower
      (grayUnion := grayUnion) (grayInter := grayInter)
      (white := white) (fullSpace := fullSpace) g1 g2
  · intro g1 g2
    exact IsGrayA1A4.inter_upper
      (grayUnion := grayUnion) (grayInter := grayInter)
      (white := white) (fullSpace := fullSpace) g1 g2

theorem grayAxiom5_from_space
    [hA5 : IsGrayAddSubGreynessComposite] :
    grayAxiom5_add_sub_composite :=
  hA5.add_sub_greyness_formula

instance instGrayA1A5SetOfInterfaces
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [IsGrayA1A4 grayUnion grayInter white fullSpace]
    [IsGrayAddSubGreynessComposite] :
    GrayA1A5Set grayUnion grayInter white fullSpace where
  axiom1 := grayAxiom1_from_space
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace)
  axiom2 := grayAxiom2_from_space
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace)
  axiom3 := grayAxiom3_from_space
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace)
  axiom4 := grayAxiom4_from_space
    (grayUnion := grayUnion) (grayInter := grayInter)
    (white := white) (fullSpace := fullSpace)
  axiom5 := grayAxiom5_from_space

theorem grayAxiom1_holds
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [h : GrayA1A5Set grayUnion grayInter white fullSpace] :
    grayAxiom1_range :=
  h.axiom1

theorem grayAxiom2_holds
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [h : GrayA1A5Set grayUnion grayInter white fullSpace] :
    grayAxiom2_white_zero white :=
  h.axiom2

theorem grayAxiom3_holds
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [h : GrayA1A5Set grayUnion grayInter white fullSpace] :
    grayAxiom3_fullSpace_one fullSpace :=
  h.axiom3

theorem grayAxiom4_holds
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [h : GrayA1A5Set grayUnion grayInter white fullSpace] :
    grayAxiom4_union_inter_bounds grayUnion grayInter :=
  h.axiom4

theorem grayAxiom5_holds
    {grayUnion grayInter : GrayNumber → GrayNumber → GrayNumber}
    {white fullSpace : GrayNumber}
    [h : GrayA1A5Set grayUnion grayInter white fullSpace] :
    grayAxiom5_add_sub_composite :=
  h.axiom5

/-- Interface for weakening buffer families `W x n`. -/
class IsWeakeningBufferFamily (W : (ℕ → ℝ) → ℕ → (ℕ → ℝ)) : Prop where
  weakening : ∀ x n k, k ≤ n → W x n k ≤ x k

/-- Interface for strengthening buffer families `S x n`. -/
class IsStrengtheningBufferFamily (S : (ℕ → ℝ) → ℕ → (ℕ → ℝ)) : Prop where
  strengthening : ∀ x n k, k ≤ n → x k ≤ S x n k

/-- Interface for weighted weakening families `W x ω n`. -/
class IsWeightedWeakeningBufferFamily
    (W : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (ℕ → ℝ)) : Prop where
  weakening : ∀ x ω n, (∀ k ≤ n, 0 < ω k) → ∀ k ≤ n, W x ω n k ≤ x k

/-- Interface for weighted strengthening families `S x ω n`. -/
class IsWeightedStrengtheningBufferFamily
    (S : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (ℕ → ℝ)) : Prop where
  strengthening : ∀ x ω n, (∀ k ≤ n, 0 < ω k) → ∀ k ≤ n, x k ≤ S x ω n k

/-- Sign-parametric interface for generalized buffer families `G x ω n α`. -/
class IsGeneralizedBufferBySign
    (G : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ → (ℕ → ℝ)) : Prop where
  negative_weaken : ∀ x ω n α, (∀ k ≤ n, 0 < ω k) → α < 0 → ∀ k ≤ n, G x ω n α k ≤ x k
  positive_strengthen : ∀ x ω n α, (∀ k ≤ n, 0 < ω k) → 0 < α → ∀ k ≤ n, x k ≤ G x ω n α k

/-- Interface for AWBO/WAWBO/GFBO special-case identities. -/
class IsBufferSpecialization
    (A : (ℕ → ℝ) → ℕ → (ℕ → ℝ))
    (W : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (ℕ → ℝ))
    (G : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ → (ℕ → ℝ)) : Prop where
  awbo_eq_wawbo_unit : ∀ x n, A x n = W x (fun _ => 1) n
  wawbo_eq_gfbo_negone :
    ∀ x ω n,
      (∀ k ≤ n, x k ≠ 0) →
      (∀ k ≤ n, W x ω n k ≠ 0) →
      W x ω n = G x ω n (-1)

/-- Interface for WASBO/GFBO special-case identity at `α = 1`. -/
class IsStrengtheningBufferSpecialization
  (S : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (ℕ → ℝ))
  (G : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ → (ℕ → ℝ)) : Prop where
  wasbo_eq_gfbo_one : ∀ x ω n, S x ω n = G x ω n 1

namespace IsWeakeningBufferFamily

theorem pointwise_le
  {W : (ℕ → ℝ) → ℕ → (ℕ → ℝ)}
    [hW : IsWeakeningBufferFamily W]
  (x : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    W x n k ≤ x k :=
  hW.weakening x n k hk

end IsWeakeningBufferFamily

namespace IsStrengtheningBufferFamily

theorem pointwise_ge
  {S : (ℕ → ℝ) → ℕ → (ℕ → ℝ)}
    [hS : IsStrengtheningBufferFamily S]
  (x : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    x k ≤ S x n k :=
  hS.strengthening x n k hk

end IsStrengtheningBufferFamily

namespace IsGeneralizedBufferBySign

theorem negative_pointwise_weaken
    {G : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ → (ℕ → ℝ)}
    [hG : IsGeneralizedBufferBySign G]
    (x ω : ℕ → ℝ) (n : ℕ) (α : ℝ)
    (hω : ∀ k ≤ n, 0 < ω k) (hα : α < 0)
    (k : ℕ) (hk : k ≤ n) :
    G x ω n α k ≤ x k :=
  hG.negative_weaken x ω n α hω hα k hk

theorem positive_pointwise_strengthen
    {G : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ → (ℕ → ℝ)}
    [hG : IsGeneralizedBufferBySign G]
    (x ω : ℕ → ℝ) (n : ℕ) (α : ℝ)
    (hω : ∀ k ≤ n, 0 < ω k) (hα : 0 < α)
    (k : ℕ) (hk : k ≤ n) :
    x k ≤ G x ω n α k :=
  hG.positive_strengthen x ω n α hω hα k hk

end IsGeneralizedBufferBySign

namespace IsGrayMulDivGreynessNondec

variable [hA56 : IsGrayMulDivGreynessNondec]

theorem mul_ge_left (g1 g2 : GrayNumber) :
    g1.greyness ≤ (gray_mul g1 g2).greyness := by
  exact le_trans (le_max_left _ _) (hA56.mul_greyness_nondec g1 g2)

theorem mul_ge_right (g1 g2 : GrayNumber) :
    g2.greyness ≤ (gray_mul g1 g2).greyness := by
  exact le_trans (le_max_right _ _) (hA56.mul_greyness_nondec g1 g2)

theorem div_ge_left (g1 g2 : GrayNumber) (h : g2.kernel ≠ 0) :
    g1.greyness ≤ (gray_div g1 g2 h).greyness := by
  exact le_trans (le_max_left _ _) (hA56.div_greyness_nondec g1 g2 h)

theorem div_ge_right (g1 g2 : GrayNumber) (h : g2.kernel ≠ 0) :
    g2.greyness ≤ (gray_div g1 g2 h).greyness := by
  exact le_trans (le_max_right _ _) (hA56.div_greyness_nondec g1 g2 h)

end IsGrayMulDivGreynessNondec

namespace IsGrayAddSubGreynessComposite

theorem add_greyness_le_one
    [hA56 : IsGrayAddSubGreynessComposite] (g1 g2 : GrayNumber) :
    (gray_add g1 g2).greyness ≤ 1 := by
  rcases hA56.add_sub_greyness_formula g1 g2 with ⟨w1, w2, hw1, hw2, hsum, hadd, _⟩
  have hw1_le : w1 * g1.greyness ≤ w1 := by
    nlinarith [hw1, g1.greyness_le_one]
  have hw2_le : w2 * g2.greyness ≤ w2 := by
    nlinarith [hw2, g2.greyness_le_one]
  have hsum_le : w1 * g1.greyness + w2 * g2.greyness ≤ 1 := by
    have : w1 * g1.greyness + w2 * g2.greyness ≤ w1 + w2 := by
      linarith
    linarith [this, hsum]
  linarith [hadd, hsum_le]

theorem add_greyness_nonneg
    [hA56 : IsGrayAddSubGreynessComposite] (g1 g2 : GrayNumber) :
    0 ≤ (gray_add g1 g2).greyness := by
  rcases hA56.add_sub_greyness_formula g1 g2 with ⟨w1, w2, hw1, hw2, _hsum, hadd, _⟩
  have hw1_term_nonneg : 0 ≤ w1 * g1.greyness := by
    exact mul_nonneg hw1 g1.greyness_nonneg
  have hw2_term_nonneg : 0 ≤ w2 * g2.greyness := by
    exact mul_nonneg hw2 g2.greyness_nonneg
  have hsum_nonneg : 0 ≤ w1 * g1.greyness + w2 * g2.greyness :=
    add_nonneg hw1_term_nonneg hw2_term_nonneg
  linarith [hadd, hsum_nonneg]

theorem sub_greyness_le_one
    [hA56 : IsGrayAddSubGreynessComposite] (g1 g2 : GrayNumber) :
    (gray_sub g1 g2).greyness ≤ 1 := by
  rcases hA56.add_sub_greyness_formula g1 g2 with ⟨w1, w2, hw1, hw2, hsum, _, hsub⟩
  have hw1_le : w1 * g1.greyness ≤ w1 := by
    nlinarith [hw1, g1.greyness_le_one]
  have hw2_le : w2 * g2.greyness ≤ w2 := by
    nlinarith [hw2, g2.greyness_le_one]
  have hsum_le : w1 * g1.greyness + w2 * g2.greyness ≤ 1 := by
    have : w1 * g1.greyness + w2 * g2.greyness ≤ w1 + w2 := by
      linarith
    linarith [this, hsum]
  linarith [hsub, hsum_le]

theorem sub_greyness_nonneg
    [hA56 : IsGrayAddSubGreynessComposite] (g1 g2 : GrayNumber) :
    0 ≤ (gray_sub g1 g2).greyness := by
  rcases hA56.add_sub_greyness_formula g1 g2 with ⟨w1, w2, hw1, hw2, _hsum, _, hsub⟩
  have hw1_term_nonneg : 0 ≤ w1 * g1.greyness := by
    exact mul_nonneg hw1 g1.greyness_nonneg
  have hw2_term_nonneg : 0 ≤ w2 * g2.greyness := by
    exact mul_nonneg hw2 g2.greyness_nonneg
  have hsum_nonneg : 0 ≤ w1 * g1.greyness + w2 * g2.greyness :=
    add_nonneg hw1_term_nonneg hw2_term_nonneg
  linarith [hsub, hsum_nonneg]
end IsGrayAddSubGreynessComposite
