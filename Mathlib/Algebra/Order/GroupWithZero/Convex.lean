import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Embedding
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Algebra.Order.Archimedean.Class

variable {α β : Type*} [CommGroup α] [LinearOrder α] [CommGroup β] [LinearOrder β]


@[to_additive] def IsConvexSubgroup (H : Subgroup α) : Prop :=
  ∀ ⦃a b : α⦄, (a ≤ b) → (b ≤ 1) → a ∈ H → b ∈ H

structure ConvexAddSubgroup (α) [AddCommGroup α] [LinearOrder α] extends AddSubgroup α where
  convex : IsConvexAddSubgroup toAddSubgroup

variable (α) in
@[to_additive (attr := ext)] structure ConvexSubgroup extends Subgroup α where
  convex : IsConvexSubgroup toSubgroup

section

variable [IsOrderedMonoid α]

@[to_additive] lemma IsConvexSubgroup.iff_mem_and_mem_of_mul_mem (H : Subgroup α) :
    IsConvexSubgroup H ↔ ∀ ⦃a b : α⦄, a ≤ 1 → b ≤ 1 → a * b ∈ H → a ∈ H ∧ b ∈ H where
  mp convex a _ ale0 ble1 h :=
    ⟨convex ((mul_le_iff_le_one_right' a).mpr ble1) ale0 h,
      convex  ((mul_le_iff_le_one_left').mpr ale0) ble1 h⟩
  mpr h a b aleb ble1 ainH :=
    (h (mul_inv_le_one_iff_le.mpr aleb) ble1 <|
      (inv_mul_cancel_right a b).symm ▸ ainH).right

lemma IsConvexSubgroup.iff_mem_of_le_of_le (H : Subgroup α) :
    IsConvexSubgroup H ↔ ∀ a b c : α , a ≤ b → b ≤ c → a ∈ H → c ∈ H → b ∈ H where
  mp convex a b c aleb blec h1 h2 := by
    have  h : a * c⁻¹ ∈ H := by
      apply MulMemClass.mul_mem h1 ; exact inv_mem_iff.mpr h2
    rw [Eq.symm (inv_mul_cancel_right b c)]
    exact (Subgroup.mul_mem_cancel_right H h2).mpr
      (convex ((mul_le_mul_iff_right c⁻¹).mpr aleb) (mul_inv_le_one_iff_le.mpr blec) h)
  mpr h a b aleb ble1 ainH := by
    specialize h a b 1
    apply h aleb ble1 ainH (Subgroup.one_mem H)

end

variable (α) in
@[to_additive] noncomputable def LinearOrderedCommGroup.height : ℕ∞ :=
  .card (ConvexSubgroup α)

@[to_additive]
lemma isConvexSubgroup_ker (f : α →*o β) : IsConvexSubgroup f.ker :=
  fun a b aleb ble1 fa1 ↦ le_antisymm (by simpa using f.monotone' ble1) <| by
    rw [← fa1]; exact f.monotone' aleb

@[to_additive] instance : SetLike (ConvexSubgroup α) α where
  coe G := G.toSubgroup
  coe_injective' _ := by aesop

@[to_additive] instance : SubgroupClass (ConvexSubgroup α) α where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem
  inv_mem {s} := s.inv_mem

section

variable [IsOrderedMonoid α]

@[to_additive] protected lemma ConvexSubgroup.le_total
    (H : ConvexSubgroup (α := α)) (G : ConvexSubgroup (α := α)) :
    H ≤ G ∨ G ≤ H := by
  by_contra!
  simp_rw [SetLike.not_le_iff_exists] at this
  have ⟨⟨a, aH, aG⟩, ⟨b, bG, bH⟩⟩ := this
  wlog ha : a ≤ 1 generalizing a
  · exact this a⁻¹ (by simp [aH]) (by simp [aG])
      (Left.inv_le_one_iff.mpr (le_of_not_ge ha))
  wlog hb : b ≤ 1 generalizing b
  · exact this b⁻¹ (by simp [bG]) (by simp [bH])
      (Left.inv_le_one_iff.mpr (le_of_not_ge hb))
  obtain le | le := le_total a b
  · exact bH (H.convex le hb aH)
  · exact aG (G.convex le ha bG)

noncomputable instance : LinearOrder (ConvexSubgroup α) where
  le_total := ConvexSubgroup.le_total
  toDecidableLE := Classical.decRel _

-- TODO: CompleteLinearOrder
-- completeLatticeOfInf

variable (G : ConvexSubgroup α)

@[to_additive]
instance : HasQuotient α (ConvexSubgroup α) where
  quotient' G := α ⧸ G.toSubgroup

@[to_additive]
instance : CommGroup (α ⧸ G) := inferInstanceAs <| CommGroup (α ⧸ G.toSubgroup)

@[to_additive] noncomputable instance : LinearOrder (α ⧸ G) where
  le x y := ∀ a : α, ⟦a⟧ = x → ∃ b : α, ⟦b⟧ = y ∧ a ≤ b
  le_refl x a ha := ⟨a, ha, le_rfl⟩
  le_trans x y z h₁ h₂ a := by
    rintro rfl
    obtain ⟨b, rfl, hab⟩ := h₁ a rfl
    obtain ⟨c, rfl, hbc⟩ := h₂ b rfl
    exact ⟨c, rfl, hab.trans hbc⟩
  le_antisymm x y h₁ h₂ := by
    obtain ⟨b, rfl, hab⟩ := h₁ _ x.out_eq
    obtain ⟨a, rfl, hba⟩ := h₂ _ rfl
    exact QuotientGroup.eq.mpr <| G.convex (mul_le_mul_left' hab a⁻¹) (by simpa)
      (QuotientGroup.eq.mp ⟦a⟧.out_eq.symm)
  le_total a b := by
    by_contra!
    obtain ⟨⟨a, rfl, hba⟩, ⟨b, rfl, hab⟩⟩ := this
    exact lt_irrefl _ <| (hab _ rfl).trans (hba _ rfl)
  toDecidableLE := Classical.decRel _

protected lemma QuotientGroup.mul_le_mul_left (x y z : α ⧸ G) (le : x ≤ y) :
    z * x ≤ z * y := by
  intro ca hca
  obtain ⟨b, rfl, hb⟩ := le _ x.out_eq
  exact ⟨ca * x.out⁻¹ * b, by simp [hca], by simpa [mul_assoc]⟩

instance : IsOrderedMonoid (α ⧸ G) where
  mul_le_mul_left _ _ le _ := QuotientGroup.mul_le_mul_left _ _ _ _ le
  mul_le_mul_right _ _ le z := by
    simp_rw [← mul_comm z]; exact QuotientGroup.mul_le_mul_left _ _ _ _ le


--TODO Show the heigth is zero iff Gamma is the trivial group
#check (α ⧸ G)

def QuotientGroup.mkOrderedMonoidHom : α →*o α ⧸ G where
  __ := QuotientGroup.mk' G.toSubgroup
  monotone' a b le a' eq := ⟨a' * a⁻¹ * b, by simp [eq], by simp [mul_assoc, le]⟩

lemma quotientmap_ismonotone : Monotone (β :=  α ⧸ G) (⟦·⟧) :=
  (QuotientGroup.mkOrderedMonoidHom _).monotone'

--lemma aux: MulArchimedean (α) ↔ Unique (FiniteArchimedeanClass (Additive α)) := by sorry

lemma ht1 :  LinearOrderedCommGroup.height α = 1 ↔ MulArchimedean (α) := by sorry
lemma ht1':  LinearOrderedCommGroup.height α = 1 ↔ (∃ (f : α →*o NNRealˣ ), Function.Injective f.toFun ) := by sorry

lemma isHeightht1.tfae : List.TFAE [
  LinearOrderedCommGroup.height α = 1,
  MulArchimedean (α),
  (∃ (f : α →*o NNRealˣ ), Function.Injective f.toFun )] := by
  tfae_have 1 → 2 := by sorry
  tfae_have 2 → 1 := by sorry
  tfae_have 3 → 1 := by sorry
  tfae_have 1 → 3 := by sorry
  tfae_finish

--def orderIsoFiniteArchimedeanClass :
 --   ConvexSubgroup α ≃o LowerSet (FiniteMulArchimedeanClass α) where

end

variable (H : Type) [LinearOrderedCommGroupWithZero H]
