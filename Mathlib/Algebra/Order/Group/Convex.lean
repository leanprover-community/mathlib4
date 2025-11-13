/-
Copyright (c) 2025 Judith Ludwig and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Junyan Xu
-/
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
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Birkhoff

/-! # Convex subgroups of a linearly ordered abelian group -/

variable {α β : Type*} [CommGroup α] [LinearOrder α] [CommGroup β] [LinearOrder β]

@[to_additive] def IsConvexSubgroup (H : Subgroup α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → b ≤ 1 → a ∈ H → b ∈ H

structure ConvexAddSubgroup (α) [AddCommGroup α] [LinearOrder α] extends AddSubgroup α where
  convex : IsConvexAddSubgroup toAddSubgroup

variable (α) in
@[to_additive (attr := ext)] structure ConvexSubgroup extends Subgroup α where
  convex : IsConvexSubgroup toSubgroup

section

variable [IsOrderedMonoid α]

@[to_additive] lemma IsConvexSubgroup.iff_mem_and_mem_of_mul_mem {H : Subgroup α} :
    IsConvexSubgroup H ↔ ∀ ⦃a b : α⦄, a ≤ 1 → b ≤ 1 → a * b ∈ H → a ∈ H ∧ b ∈ H where
  mp convex a _ ale0 ble1 h :=
    ⟨convex ((mul_le_iff_le_one_right' a).mpr ble1) ale0 h,
      convex ((mul_le_iff_le_one_left').mpr ale0) ble1 h⟩
  mpr h a b aleb ble1 ainH :=
    (h (mul_inv_le_one_iff_le.mpr aleb) ble1 <| (inv_mul_cancel_right a b).symm ▸ ainH).right

@[to_additive] lemma IsConvexSubgroup.iff_ordConnected {H : Subgroup α} :
    IsConvexSubgroup H ↔ (H : Set α).OrdConnected where
  mp convex := by
    refine ⟨fun a ha c hc b binIcc ↦ ?_⟩
    rw [← inv_mul_cancel_right b c]
    exact (H.mul_mem_cancel_right hc).mpr <| convex ((mul_le_mul_iff_right c⁻¹).mpr binIcc.1)
      (mul_inv_le_one_iff_le.mpr binIcc.2) <| H.mul_mem ha (inv_mem hc)
  mpr h a b aleb ble1 ainH := h.out' ainH H.one_mem ⟨aleb, ble1⟩

end

@[to_additive] lemma isConvexSubgroup_ker (f : α →*o β) : IsConvexSubgroup f.ker :=
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

@[to_additive] noncomputable instance : LinearOrder (ConvexSubgroup α) where
  le_total G H := by
    by_contra!
    simp_rw [SetLike.not_le_iff_exists] at this
    have ⟨⟨a, aG, aH⟩, ⟨b, bH, bG⟩⟩ := this
    wlog ha : a ≤ 1 generalizing a
    · exact this a⁻¹ (by simp [aG]) (by simp [aH]) (Left.inv_le_one_iff.mpr (le_of_not_ge ha))
    wlog hb : b ≤ 1 generalizing b
    · exact this b⁻¹ (by simp [bH]) (by simp [bG]) (Left.inv_le_one_iff.mpr (le_of_not_ge hb))
    obtain le | le := le_total a b
    exacts [bG (G.convex le hb aG), aH (H.convex le ha bH)]
  toDecidableLE := Classical.decRel _

-- TODO: CompleteLinearOrder
-- Function.Injective.completeLattice

variable (G : ConvexSubgroup α)

@[to_additive] instance : HasQuotient α (ConvexSubgroup α) where
  quotient' G := α ⧸ G.toSubgroup

@[to_additive] instance : CommGroup (α ⧸ G) := inferInstanceAs <| CommGroup (α ⧸ G.toSubgroup)

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

@[to_additive] private lemma QuotientGroup.mul_le_mul_left (x y z : α ⧸ G) (le : x ≤ y) :
    z * x ≤ z * y := by
  intro ca hca
  obtain ⟨b, rfl, hb⟩ := le _ x.out_eq
  exact ⟨ca * x.out⁻¹ * b, by simp [hca], by simpa [mul_assoc]⟩

@[to_additive] instance : IsOrderedMonoid (α ⧸ G) where
  mul_le_mul_left _ _ le _ := QuotientGroup.mul_le_mul_left _ _ _ _ le
  mul_le_mul_right _ _ le z := by
    simp_rw [← mul_comm z]; exact QuotientGroup.mul_le_mul_left _ _ _ _ le

@[to_additive] def QuotientGroup.mkOrderedMonoidHom : α →*o α ⧸ G where
  __ := QuotientGroup.mk' G.toSubgroup
  monotone' a b le a' eq := ⟨a' * a⁻¹ * b, by simp [eq], by simp [mul_assoc, le]⟩

-- remove this?
@[to_additive] lemma QuotientGroup.monotone_mk : Monotone (β :=  α ⧸ G) (⟦·⟧) :=
  (QuotientGroup.mkOrderedMonoidHom _).monotone'

section ToBeMoved

@[to_additive (attr := simp)]
theorem Subgroup.mabs_mem_iff {G : Subgroup α} {a : α} : |a|ₘ ∈ G ↔ a ∈ G := by
  obtain ⟨h, -⟩ | ⟨h, -⟩ := mabs_cases a <;> simp [h]

@[to_additive] theorem FiniteMulArchimedeanClass.min_le_mk_mul (a b : α) (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a * b ≠ 1) : min (mk a ha) (mk b hb) ≤ mk (a * b) hab :=
  MulArchimedeanClass.min_le_mk_mul a b

@[to_additive] theorem FiniteMulArchimedeanClass.mk_inv (a : α) (ha : a ≠ 1) :
    mk a⁻¹ (by simp [ha]) = mk a ha :=
  Subtype.ext (MulArchimedeanClass.mk_inv a)

@[to_additive] theorem ConvexSubgroup.mem_of_finiteMulArchimedeanClass_mk_le
    (G : ConvexSubgroup α) {a b : α} {ha1 : a ≠ 1} {hb1 : b ≠ 1}
    (le : FiniteMulArchimedeanClass.mk a ha1 ≤ .mk b hb1)
    (haG : a ∈ G) : b ∈ G := by
  rw [FiniteMulArchimedeanClass.mk_le_mk, MulArchimedeanClass.mk_le_mk] at le
  have ⟨n, le⟩ := le
  refine G.toSubgroup.mabs_mem_iff.mp ?_
  exact (IsConvexSubgroup.iff_ordConnected.mp G.convex).1 G.one_mem (G.pow_mem (by simpa) _)
    ⟨one_le_mabs _, le⟩

noncomputable def UpperSet.orderIsoWithTopOfFinite {α} [LinearOrder α] [Finite α] :
    UpperSet α ≃o WithTop α :=
  WithTop.subtypeOrderIso.symm.trans <| .withTopCongr <| .trans
    (.setCongr {⊤}ᶜ (setOf InfIrred) <| by ext; simp) <| .symm .infIrredUpperSet

end ToBeMoved

/-- The (convex) subgroup of a linearly ordered group consisting of all elements lying
in an upper set of `FiniteMulArchimedeanClass`es. -/
@[to_additive UpperSet.finiteArchimedeanClassToAddSubgroup
/-- The (convex) subgroup of a linearly ordered additive group consisting of all elements
lying in an upper set of `FiniteArchimedeanClass`es. -/]
def UpperSet.finiteMulArchimedeanClassToSubgroup
    (s : UpperSet (FiniteMulArchimedeanClass α)) : Subgroup α where
  carrier := {a | ∀ h : a ≠ 1, .mk a h ∈ s}
  mul_mem' {a b} ha hb hab := by
    obtain rfl | ha1 := eq_or_ne a 1
    · simp_rw [one_mul] at hab ⊢; exact hb hab
    obtain rfl | hb1 := eq_or_ne b 1
    · simp_rw [mul_one] at hab ⊢; exact ha hab
    apply s.upper (FiniteMulArchimedeanClass.min_le_mk_mul a b ha1 hb1 hab)
    obtain eq | eq := min_choice (FiniteMulArchimedeanClass.mk a ha1)
      (FiniteMulArchimedeanClass.mk b hb1) <;> rw [eq]
    exacts [ha ha1, hb hb1]
  one_mem' ha := (ha rfl).elim
  inv_mem' {a} ha ha1 := by rw [FiniteMulArchimedeanClass.mk_inv a (by simpa using ha1)]; exact ha _

/-- The convex subgroups of a linearly ordered group are in bijection with upper sets of
`FiniteMulArchimedeanClass`es. -/
@[to_additive /-- The convex subgroups of a linearly ordered additive group are in bijection with
upper sets of `FiniteArchimedeanClass`es. -/] def ConvexSubgroup.equivUpperSet :
    ConvexSubgroup α ≃ UpperSet (FiniteMulArchimedeanClass α) where
  toFun G := .mk {x | ∃ a : α, ∃ ha : a ≠ 1, a ∈ G ∧ x = .mk a ha} fun x y le ↦ by
    rintro ⟨a, ha1, haG, rfl⟩
    revert y
    refine FiniteMulArchimedeanClass.ind fun b hb1 le ↦ ?_
    exact ⟨b, hb1, G.toSubgroup.mabs_mem_iff.mp <| by
      simpa using G.mem_of_finiteMulArchimedeanClass_mk_le le haG, rfl⟩
  invFun s := .mk s.finiteMulArchimedeanClassToSubgroup fun a b hab b_le ha b_ne ↦
    s.upper (MulArchimedeanClass.mk_monotoneOn (hab.trans b_le) b_le hab)
      (ha (hab.trans_lt (b_le.lt_of_ne b_ne)).ne)
  left_inv G := by
    refine SetLike.ext fun a ↦ ⟨fun h ↦ ?_, fun h ha ↦ ⟨a, ha, h, rfl⟩⟩
    obtain rfl | ha1 := eq_or_ne a 1; · simp
    have ⟨b, hb1, hbG, eq⟩ := h ha1
    exact G.mem_of_finiteMulArchimedeanClass_mk_le eq.ge hbG
  right_inv s := UpperSet.ext <| Set.ext <| FiniteMulArchimedeanClass.ind fun a ha1 ↦
    ⟨fun ⟨b, hb1, hbs, eq⟩ ↦ by simpa only [eq] using hbs hb1, fun h ↦ ⟨a, ha1, fun _ ↦ h, rfl⟩⟩

/-- The convex subgroups of a linearly ordered group are in order-reversing bijection
with upper sets of `FiniteMulArchimedeanClass`es. -/
@[to_additive /-- The convex subgroups of a linearly ordered additive group are in order-reversing
bijection with upper sets of `FiniteArchimedeanClass`es. -/]
def ConvexSubgroup.orderIsoUpperSet :
    ConvexSubgroup α ≃o (UpperSet (FiniteMulArchimedeanClass α))ᵒᵈ :=
  (equivUpperSet.trans OrderDual.toDual).toOrderIso
    (fun _G _H le _x ⟨a, ha1, haH, eq⟩ ↦ ⟨a, ha1, le haH, eq⟩)
    fun _s _t le _a hat ha1 ↦ le (hat ha1)

lemma mulArchimedean_iff_subsingleton_finiteMulArchimedeanClass :
    MulArchimedean α ↔ Subsingleton (FiniteMulArchimedeanClass α) where
  mp _ := inferInstance
  mpr s := MulArchimedeanClass.mulArchimedean_of_mk_eq_mk
    fun a ha b hb ↦ congr_arg Subtype.val (s.elim (.mk a ha) (.mk b hb))

namespace LinearOrderedCommGroup

variable (α) in
@[to_additive] noncomputable def height : ℕ∞ := .card (ConvexSubgroup α) - 1

@[to_additive] theorem height_eq_card_subtype :
    height α = .card {G : ConvexSubgroup α // G.toSubgroup ≠ ⊥} := by
  sorry

theorem height_eq_zero_iff : LinearOrderedCommGroup.height α = 0 ↔ Subsingleton α := by
  sorry

end LinearOrderedCommGroup

lemma finite_finiteMulArchimedeanClass_iff_convexSubgroup :
    Finite (FiniteMulArchimedeanClass α) ↔ Finite (ConvexSubgroup α) := by
  rw [ConvexSubgroup.equivUpperSet.finite_iff]
  constructor <;> intro
  · rw [UpperSet.orderIsoWithTopOfFinite.toEquiv.finite_iff, WithTop]; infer_instance
  · exact .of_injective _ (OrderEmbedding.infIrredUpperSet.toEmbedding.trans (.subtype _)).injective

lemma height_eq_card_finiteMulArchimedeanClass :
    LinearOrderedCommGroup.height α = ENat.card (FiniteMulArchimedeanClass α) := by
  rw [LinearOrderedCommGroup.height]
  by_cases fin : Finite (FiniteMulArchimedeanClass α)
  · simp_rw [ENat.card_congr <| ConvexSubgroup.equivUpperSet.trans
      UpperSet.orderIsoWithTopOfFinite.toEquiv, ENat.card, WithTop, ← Nat.cast_card,
      Finite.card_option, Nat.cast_add, map_add, map_natCast]
    rfl
  · have := finite_finiteMulArchimedeanClass_iff_convexSubgroup.not.mp fin
    rw [not_finite_iff_infinite] at fin this
    simp_rw [ENat.card_eq_top_of_infinite]
    rfl

lemma mulArchimedean_iff_height_le_one :
    MulArchimedean α ↔ LinearOrderedCommGroup.height α ≤ 1 := by
  rw [height_eq_card_finiteMulArchimedeanClass, ENat.card_le_one_iff_subsingleton,
    mulArchimedean_iff_subsingleton_finiteMulArchimedeanClass]

lemma mulArchimedean_iff_exists_orderMonoidHom : MulArchimedean α ↔
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f where
  mp _ := have ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective (Additive α)
    ⟨⟨⟨⟨f, f.map_zero⟩, f.map_add⟩, f.monotone'⟩, hf⟩
  mpr := fun ⟨f, hf⟩ ↦ .comap f.toMonoidHom (f.monotone'.strictMono_of_injective hf)

lemma MulArchimedean.tfae : List.TFAE
  [ MulArchimedean α,
    LinearOrderedCommGroup.height α ≤ 1,
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f] := by
  tfae_have 1 ↔ 2 := mulArchimedean_iff_height_le_one
  tfae_have 1 ↔ 3 := mulArchimedean_iff_exists_orderMonoidHom
  tfae_finish

end
