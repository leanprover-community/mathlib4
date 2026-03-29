import GrayNumber
import GrayAxiomInterfaces

/-!
# Grey Theory Operation Axioms

This module contains the research-layer axioms used by the general grey-number
operations. A5-A6 foundational constraints are included in the Round1 baseline.
-/

-- ==============================================================================
-- 研究层公理：一般灰数加法的灰度约束
-- Included in Round1 as foundational A5 constraints.
-- ==============================================================================

-- [AxiomTrack] round1=include(A5-part1); role=base-axiom
axiom general_gray_add_nonneg (g1 g2 : GrayNumber) :
  (let sum_kernel := g1.kernel + g2.kernel
   let w1 := if sum_kernel = 0 then 0.5 else g1.kernel / sum_kernel
   let w2 := if sum_kernel = 0 then 0.5 else g2.kernel / sum_kernel
   0 ≤ w1 * g1.greyness + w2 * g2.greyness)

-- [AxiomTrack] round1=include(A5-part2); role=base-axiom
axiom general_gray_add_le_one (g1 g2 : GrayNumber) :
  (let sum_kernel := g1.kernel + g2.kernel
   let w1 := if sum_kernel = 0 then 0.5 else g1.kernel / sum_kernel
   let w2 := if sum_kernel = 0 then 0.5 else g2.kernel / sum_kernel
   w1 * g1.greyness + w2 * g2.greyness ≤ 1)

-- ==============================================================================
-- 研究层公理：一般灰数乘除的灰度不递减约束（A6）
-- Included in Round1 as foundational A6 constraints.
-- ==============================================================================

-- [AxiomTrack] round1=include(A6-mul); role=base-axiom
axiom general_gray_mul_nondec (g1 g2 : GrayNumber) :
  max g1.greyness g2.greyness ≤ (gray_mul g1 g2).greyness

-- [AxiomTrack] round1=include(A6-div); role=base-axiom
axiom general_gray_div_nondec (g1 g2 : GrayNumber) (h : g2.kernel ≠ 0) :
  max g1.greyness g2.greyness ≤ (gray_div g1 g2 h).greyness

/-- Export A6 as a reusable interface instance for downstream lemmas. -/
instance instIsGrayMulDivGreynessNondecOfA6 : IsGrayMulDivGreynessNondec where
  mul_greyness_nondec := general_gray_mul_nondec
  div_greyness_nondec := general_gray_div_nondec
