import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The Gamma function is meromorphic
-/

public section

open Set Complex

lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

lemma MeromorphicOn.Gamma : MeromorphicOn Gamma univ :=
  MeromorphicNFOn.Gamma.meromorphicOn
