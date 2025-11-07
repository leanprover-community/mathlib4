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

@[to_additive] lemma IsConvexSubgroup.iff_mem_and_mem_of_mul_mem {H : Subgroup α} :
    IsConvexSubgroup H ↔ ∀ ⦃a b : α⦄, a ≤ 1 → b ≤ 1 → a * b ∈ H → a ∈ H ∧ b ∈ H where
  mp convex a _ ale0 ble1 h :=
    ⟨convex ((mul_le_iff_le_one_right' a).mpr ble1) ale0 h,
      convex  ((mul_le_iff_le_one_left').mpr ale0) ble1 h⟩
  mpr h a b aleb ble1 ainH :=
    (h (mul_inv_le_one_iff_le.mpr aleb) ble1 <|
      (inv_mul_cancel_right a b).symm ▸ ainH).right

lemma IsConvexSubgroup.iff_mem_of_le_of_le {H : Subgroup α} :
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

lemma IsConvexSubgroup.iff_isOrdConnected {H : Subgroup α} :
    IsConvexSubgroup H ↔ Set.OrdConnected (H : Set α) where
    mp convex := by
      refine ⟨fun a ha c hc b binIcc ↦ ?_⟩
      rw [← (inv_mul_cancel_right b c)]
      exact (H.mul_mem_cancel_right hc).mpr
        (convex ((mul_le_mul_iff_right c⁻¹).mpr binIcc.1) (mul_inv_le_one_iff_le.mpr binIcc.2) <|
        H.mul_mem ha (inv_mem hc))
    mpr h a b aleb ble1 ainH := h.out' ainH H.one_mem ⟨aleb, ble1⟩

end

variable (α) in
@[to_additive] noncomputable def LinearOrderedCommGroup.height : ℕ∞ :=
  .card (ConvexSubgroup α) - 1 --{G : ConvexSubgroup α // G.toSubgroup ≠ ⊥}

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

def QuotientGroup.mkOrderedMonoidHom : α →*o α ⧸ G where
  __ := QuotientGroup.mk' G.toSubgroup
  monotone' a b le a' eq := ⟨a' * a⁻¹ * b, by simp [eq], by simp [mul_assoc, le]⟩

lemma quotientMk_ismonotone : Monotone (β :=  α ⧸ G) (⟦·⟧) :=
  (QuotientGroup.mkOrderedMonoidHom _).monotone'

@[simp] theorem Subgroup.mabs_mem_iff {G : Subgroup α} {a : α} : |a|ₘ ∈ G ↔ a ∈ G := by
  obtain ⟨h, -⟩ | ⟨h, -⟩ := mabs_cases a <;> simp [h]

theorem FiniteMulArchimedeanClass.min_le_mk_mul (a b : α) (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a * b ≠ 1) : min (mk a ha) (mk b hb) ≤ mk (a * b) hab :=
  MulArchimedeanClass.min_le_mk_mul a b

theorem FiniteMulArchimedeanClass.mk_inv (a : α) (ha : a ≠ 1) :
    mk a⁻¹ (by simp [ha]) = mk a ha :=
  Subtype.ext (MulArchimedeanClass.mk_inv a)

theorem ConvexSubgroup.mem_of_finiteMulArchimedeanClass_mk_le (G : ConvexSubgroup α)
    {a b : α} {ha1 : a ≠ 1} {hb1 : b ≠ 1}
    (le : FiniteMulArchimedeanClass.mk a ha1 ≤ FiniteMulArchimedeanClass.mk b hb1)
    (haG : a ∈ G) : b ∈ G := by
  rw [FiniteMulArchimedeanClass.mk_le_mk, MulArchimedeanClass.mk_le_mk] at le
  have ⟨n, le⟩ := le
  refine G.toSubgroup.mabs_mem_iff.mp ?_
  exact IsConvexSubgroup.iff_mem_of_le_of_le.mp G.convex 1 _ _ (one_le_mabs _) le G.one_mem
    (G.pow_mem (by simpa) _)

def UpperSet.finiteMulArchimedeanClassToSubgroup (s : UpperSet (FiniteMulArchimedeanClass α)) :
    Subgroup α where
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
  inv_mem' {a} ha ha1 := by
    rw [FiniteMulArchimedeanClass.mk_inv a (by simpa using ha1)]
    exact ha _

variable (α) in
def equivFiniteArchimedeanClass :
    ConvexSubgroup α ≃ UpperSet (FiniteMulArchimedeanClass α) where
  toFun G := ⟨{x | ∃ a : α, ∃ ha : a ≠ 1, a ∈ G ∧ x = .mk a ha}, fun x y le ↦ by
    rintro ⟨a, ha1, haG, rfl⟩
    revert y
    apply FiniteMulArchimedeanClass.ind
    intro b hb1 le
    have := G.mem_of_finiteMulArchimedeanClass_mk_le le haG
    exact ⟨b, hb1, G.toSubgroup.mabs_mem_iff.mp (by simpa), rfl⟩⟩
  invFun s := ⟨s.finiteMulArchimedeanClassToSubgroup, fun a b hab b_le ha b_ne ↦ by
    refine s.upper ?_ (ha (hab.trans_lt (b_le.lt_of_ne b_ne)).ne)
    exact MulArchimedeanClass.mk_monotoneOn (hab.trans b_le) b_le hab⟩
  left_inv G := by
    ext a
    constructor <;> intro h
    · obtain rfl | ha1 := eq_or_ne a 1; · simp
      have ⟨b, hb1, hbG, eq⟩ := h ha1
      exact G.mem_of_finiteMulArchimedeanClass_mk_le eq.ge hbG
    exact fun ha ↦ ⟨a, ha, h, rfl⟩
  right_inv s := by
    ext1; apply Set.ext
    apply FiniteMulArchimedeanClass.ind
    intro a ha1
    constructor <;> intro h
    · have ⟨b, hb1, hbs, eq⟩ := h
      rw [eq]
      exact hbs hb1
    exact ⟨a, ha1, fun _ ↦ h, rfl⟩

variable (α) in
def orderIsoFiniteArchimedeanClass :
    (ConvexSubgroup α)ᵒᵈ ≃o UpperSet (FiniteMulArchimedeanClass α) :=
  (OrderDual.ofDual.trans <| equivFiniteArchimedeanClass α).toOrderIso
    (fun _G _H le _x ⟨a, ha1, haH, eq⟩ ↦ ⟨a, ha1, le haH, eq⟩)
    fun _s _t le _a hat ha1 ↦ le (hat ha1)

theorem FiniteMulArchimedean_of_mk_eq_mk (h : ∀ a (ha : a ≠ 1), ∀ (b : α) (hb : b ≠ 1),
    FiniteMulArchimedeanClass.mk a ha = FiniteMulArchimedeanClass.mk b hb) : MulArchimedean α := by
  apply MulArchimedeanClass.mulArchimedean_of_mk_eq_mk
  intros a ha b hb
  specialize h a ha b hb
  exact congrArg Subtype.val h

lemma mulArchimedean_iff_subsingleton_finiteMulArchimedeanClass :
    MulArchimedean α ↔ Subsingleton (FiniteMulArchimedeanClass α) := by
  constructor
  · exact fun a ↦ FiniteMulArchimedeanClass.instSubsingletonOfMulArchimedean
  · intro s
    apply FiniteMulArchimedean_of_mk_eq_mk
    intros a ha b hb
    apply Subsingleton.allEq

theorem height_eq_zero_iff : LinearOrderedCommGroup.height α = 0 ↔ Subsingleton α := by
  sorry

def UpperSet.equivWithTopOfFinite (α) [LinearOrder α] [Finite α] :
    UpperSet α ≃o WithTop α where
  toFun s := s.1.toFinite.toFinset.min
  invFun i := i.recTopCoe ⊤ .Ici
  left_inv s := by
    let a' := s.1.toFinite.toFinset.min

    sorry
    ext a; simp
  right_inv i := i.recTopCoe (by simp) fun i ↦ (Finset.min_le (by simp)).antisymm (by simp)
  map_rel_iff' := _

/- instance : Nonempty (ConvexSubgroup α) :=
  ⟨⊥, fun _a _b hab hb1 ha1 ↦ hb1.antisymm (ha1.ge.trans hab)⟩ -/

private lemma height_eq_card_finiteMulArchimedeanClass' [Finite (FiniteMulArchimedeanClass α)] :
    LinearOrderedCommGroup.height α = ENat.card (FiniteMulArchimedeanClass α) := by
  set fα := FiniteMulArchimedeanClass α
  have := Fintype.ofFinite fα
  rw [LinearOrderedCommGroup.height, ENat.card_congr (equivFiniteArchimedeanClass α)]
  rw [← ENat.card_congr (UpperSet.map (Fintype.orderIsoFinOfCardEq fα rfl)).toEquiv]
  rw [ENat.card_congr (UpperSet.finEquiv _).toEquiv, ENat.card, Cardinal.mk_fin]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one,
    ENat.card_eq_coe_fintype_card]
  rfl

lemma finite_finiteMulArchimedeanClass_iff_convexSubgroup :
    Finite (FiniteMulArchimedeanClass α) ↔ Finite (ConvexSubgroup α) := by
  constructor
  · intro h
    have := ENat.card_lt_top.mpr h
    rw [← ENat.card_lt_top]
    rw [← height_eq_card_finiteMulArchimedeanClass', LinearOrderedCommGroup.height] at this
    contrapose! this
    rw [top_le_iff] at this ⊢
    rw [this]
    rfl
  rw [(equivFiniteArchimedeanClass α).finite_iff]
  exact fun _ ↦ .of_injective _
    (OrderEmbedding.infIrredUpperSet.toEmbedding.trans (.subtype _)).injective

lemma height_eq_card_finiteMulArchimedeanClass :
    LinearOrderedCommGroup.height α = ENat.card (FiniteMulArchimedeanClass α) := by
  rw [LinearOrderedCommGroup.height]
  by_cases fin : Finite (FiniteMulArchimedeanClass α)
  · exact height_eq_card_finiteMulArchimedeanClass'
  have := finite_finiteMulArchimedeanClass_iff_convexSubgroup.not.mp fin
  rw [not_finite_iff_infinite] at fin this
  simp_rw [ENat.card_eq_top_of_infinite]
  rfl

lemma mulArchimedean_iff_height_le_one : MulArchimedean α ↔ LinearOrderedCommGroup.height α ≤ 1 := by
  rw [height_eq_card_finiteMulArchimedeanClass, ENat.card_le_one_iff_subsingleton]
  rw [mulArchimedean_iff_subsingleton_finiteMulArchimedeanClass]

lemma mulArchimedean_iff_exists_orderMonoidHom : MulArchimedean α ↔
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f := by
  constructor
  · intro
    have ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective (Additive α)
    exact ⟨⟨⟨⟨f, f.map_zero⟩, f.map_add⟩, f.monotone'⟩, hf⟩
  exact fun ⟨f, hf⟩ ↦ .comap f.toMonoidHom (f.monotone'.strictMono_of_injective hf)

lemma MulArchimedean.tfae : List.TFAE [
    MulArchimedean α,
    LinearOrderedCommGroup.height α ≤ 1,
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f] := by
  tfae_have 1 ↔ 2 := mulArchimedean_iff_height_le_one
  tfae_have 1 ↔ 3 := mulArchimedean_iff_exists_orderMonoidHom
  tfae_finish

end
