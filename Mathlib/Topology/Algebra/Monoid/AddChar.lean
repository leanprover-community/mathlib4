import Mathlib.Topology.Separation.Hausdorff

/-!
# Additive characters of topological monoids
-/

public section

lemma DenseRange.addChar_eq_of_eval_one_eq {A M : Type*} [TopologicalSpace A] [AddMonoidWithOne A]
    [Monoid M] [TopologicalSpace M] [T2Space M] (hdr : DenseRange ((↑) : ℕ → A))
    {κ₁ κ₂ : AddChar A M} (hκ₁ : Continuous κ₁) (hκ₂ : Continuous κ₂) (h : κ₁ 1 = κ₂ 1) :
    κ₁ = κ₂ := by
  refine DFunLike.coe_injective <| hdr.equalizer hκ₁ hκ₂ (funext fun n ↦ ?_)
  simp only [Function.comp_apply, ← nsmul_one, h, AddChar.map_nsmul_eq_pow]
