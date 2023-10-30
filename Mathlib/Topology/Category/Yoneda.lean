import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.Topology.Category.TopCat.Basic

universe w w' v u

namespace QuotientMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)} (hf : QuotientMap f) (g : C(X, Z)) (h : ∀ a b, f a = f b → g a = g b)

noncomputable
def homeomorph : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

noncomputable
def descend : C(Y, Z) where
  toFun := by
    refine ((fun i ↦ Quotient.liftOn' i g ?_) : Quotient (Setoid.ker f) → Z) ∘ hf.homeomorph.symm
    intro a b (hab : f _ = f _)
    exact h a b hab
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

theorem descend_comp : False := sorry -- `QuotientMap.descend` makes the triangle commute.

end QuotientMap

open CategoryTheory Opposite Limits

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w})
    (Y : Type w') [TopologicalSpace Y]

namespace ContinuousMap

def yoneda : C ⥤ Type (max w w') where
  obj X := C(Y, F.obj X)
  map f g := ContinuousMap.comp (F.map f) g

def coyoneda : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f g := ContinuousMap.comp g (F.map f.unop)

end ContinuousMap

variable (X : Type v) [TopologicalSpace X] (G : C ⥤ TopCat.{u})
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], HasPullback π π]
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], EffectiveEpi (pullback.fst (f := π) (g := π))]
    (hq : ∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], QuotientMap (G.map π))

open ContinuousMap

theorem EqualizerConditionCoyoneda : EqualizerCondition (coyoneda G X) := by
  intro Z B π _ _
  refine ⟨fun a b h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · simp only [ContinuousMap.coyoneda, unop_op, Quiver.Hom.unop_op, Set.coe_setOf, MapToEqualizer,
      Set.mem_setOf_eq, Subtype.mk.injEq, comp, ContinuousMap.mk.injEq] at h
    simp only [ContinuousMap.coyoneda, unop_op]
    ext x
    obtain ⟨y, hy⟩ := (hq Z B π).surjective x
    rw [← hy]
    exact congr_fun h y
  · simp only [ContinuousMap.coyoneda, comp, unop_op, Quiver.Hom.unop_op, Set.mem_setOf_eq,
      ContinuousMap.mk.injEq] at ha
    simp only [ContinuousMap.coyoneda, comp, unop_op, Quiver.Hom.unop_op, Set.coe_setOf,
      MapToEqualizer, Set.mem_setOf_eq, Subtype.mk.injEq]
    simp only [ContinuousMap.coyoneda, unop_op] at a
    refine ⟨(hq Z B π).descend a ?_, ?_⟩
    · intro x y hxy
      -- We need `G` to preserve pullbacks, and then apply `ha` to the element `⟨(x,y), hxy⟩` of the
      -- explicit pullback in `TopCat`.
      sorry
    · sorry -- this is `descend_comp`
