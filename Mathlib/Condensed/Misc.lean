import Mathlib.Topology.LocallyConstant.Basic

@[simps! apply toEquiv]
def _root_.Homeomorph.sigmaCongrLeft {α₁ α₂ : Type*} {β : α₁ → Type*} [∀ a, TopologicalSpace (β a)]
    (f : α₁ ≃ α₂) : (a : α₁) × β a ≃ₜ (a : α₂) × β (f.symm a) where
  toEquiv := Equiv.sigmaCongrLeft' f
  continuous_toFun := by
    apply continuous_sigma
    rw [f.forall_congr_left']
    intro i
    simp only [Equiv.sigmaCongrLeft', Equiv.sigmaCongrLeft, Equiv.symm_symm_apply,
      Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk]
    convert continuous_sigmaMk (ι := α₂) (σ := fun a ↦ β (f.symm a))
    all_goals simp
  continuous_invFun := by
    apply continuous_sigma
    rw [f.symm.forall_congr_left']
    intro i
    exact continuous_sigmaMk

def homeoSigma {X Y : Type*} [TopologicalSpace X] (f : LocallyConstant X Y)
    (p : Y → Prop) (h : ∀ x, p (f x)) :
    (Σ (y : {y // p y}), f ⁻¹' {y.val}) ≃ₜ X where
  toEquiv := Equiv.sigmaSubtypeFiberEquiv f p h
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    have : (Equiv.sigmaSubtypeFiberEquiv f p h).invFun ⁻¹' U =
        (Equiv.sigmaSubtypeFiberEquiv f p h).toFun '' U := by ext; simp
    rw [this]
    refine (?_ : IsOpenMap _) U hU
    rw [isOpenMap_sigma]
    exact fun i ↦ IsOpen.isOpenMap_subtype_val (f.2.isOpen_fiber _)
