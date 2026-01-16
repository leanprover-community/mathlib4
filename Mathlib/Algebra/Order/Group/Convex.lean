/-
Copyright (c) 2025 Judith Ludwig and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Data.Finite.Card
public import Mathlib.Data.Real.Embedding
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.Birkhoff
public import Mathlib.Order.Quotient

/-! # Convex subgroups of a linearly ordered abelian group -/

@[expose] public section

variable {α β : Type*} [CommGroup α] [LinearOrder α] [CommGroup β] [LinearOrder β]

/-- A subgroup `H` of a linearly ordered abelian group is convex, if for any `a ≤ b ≤ 1`,
`a ∈ H` implies `b ∈ H`. -/
@[to_additive /-- A subgroup `H` of a linearly ordered additive abelian group is convex,
if for any `a ≤ b ≤ 0`, `a ∈ H` implies `b ∈ H`. -/]
def IsConvexSubgroup (H : Subgroup α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → b ≤ 1 → a ∈ H → b ∈ H

/-- The type of convex subgroups of a linearly ordered additive abelian group. -/
structure ConvexAddSubgroup (α) [AddCommGroup α] [LinearOrder α] extends AddSubgroup α where
  convex : IsConvexAddSubgroup toAddSubgroup

variable (α) in
/-- The type of convex subgroups of a linearly ordered abelian group. -/
@[to_additive (attr := ext)] structure ConvexSubgroup extends Subgroup α where
  convex : IsConvexSubgroup toSubgroup

@[to_additive] lemma ConvexSubgroup.toSubgroup_injective :
    Function.Injective (ConvexSubgroup.toSubgroup : ConvexSubgroup α → Subgroup α) :=
  fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp

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

/-- The kernel of a morphism of totally ordered abelian groups is convex. -/
@[to_additive] lemma isConvexSubgroup_ker (f : α →*o β) : IsConvexSubgroup f.ker :=
  fun a b aleb ble1 fa1 ↦ le_antisymm (by simpa using f.monotone' ble1) <| by
    rw [← fa1]; exact f.monotone' aleb

@[to_additive] instance : SetLike (ConvexSubgroup α) α where
  coe G := G.toSubgroup
  coe_injective' _ := by aesop

@[to_additive (attr := simp)] theorem ConvexSubgroup.carrier_eq_coe (G : ConvexSubgroup α) :
    G.carrier = G := rfl

@[to_additive] instance : SubgroupClass (ConvexSubgroup α) α where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem
  inv_mem {s} := s.inv_mem

@[to_additive] instance : Top (ConvexSubgroup α) where
  top := .mk ⊤ fun _ _ _ _ _ ↦ ⟨⟩

@[to_additive] instance : Bot (ConvexSubgroup α) where
  bot := .mk ⊥ fun _a _b hab hb1 ha ↦ hb1.antisymm (ha.ge.trans hab)

@[to_additive] instance [Subsingleton α] : Subsingleton (ConvexSubgroup α) where
  allEq _ _ := by ext a; simp [Subsingleton.elim a 1]

@[to_additive] instance : Nonempty (ConvexSubgroup α) := ⟨⊤⟩

@[to_additive] instance [Nontrivial α] : Nontrivial (ConvexSubgroup α) where
  exists_pair_ne := ⟨⊤, ⊥, have ⟨_, ne⟩ := exists_ne (1 : α); ne_of_mem_of_not_mem' trivial ne⟩

namespace ConvexSubgroup

variable [IsOrderedMonoid α] (G H : ConvexSubgroup α)

/-- Convex subgroups are linearly ordered by inclusion. -/
@[to_additive] noncomputable instance : LinearOrder (ConvexSubgroup α) :=
  have total (G H : ConvexSubgroup α) : G ≤ H ∨ H ≤ G := by
    by_contra!
    simp_rw [SetLike.not_le_iff_exists] at this
    have ⟨⟨a, aG, aH⟩, ⟨b, bH, bG⟩⟩ := this
    wlog ha : a ≤ 1 generalizing a
    · exact this a⁻¹ (by simp [aG]) (by simp [aH]) (Left.inv_le_one_iff.mpr (le_of_not_ge ha))
    wlog hb : b ≤ 1 generalizing b
    · exact this b⁻¹ (by simp [bH]) (by simp [bG]) (Left.inv_le_one_iff.mpr (le_of_not_ge hb))
    obtain le | le := le_total a b
    exacts [bG (G.convex le hb aG), aH (H.convex le ha bH)]
  have union_eq (G H : ConvexSubgroup α) : let _ := Classical.dec
      (G : Set α) ∪ H = (if G ≤ H then H else G) :=
    (em (G ≤ H)).elim (by simp [·]) fun h ↦ by simpa [h] using (total G H).resolve_left h
  { le_total := total
    toDecidableLE := Classical.decRel _
    max G H :=
    { carrier := G ∪ H
      mul_mem' := by rw [union_eq]; exact mul_mem
      one_mem' := by simp
      inv_mem' := by simp
      convex := by simp_rw [union_eq]; exact ConvexSubgroup.convex _ }
    max_def G H := SetLike.ext' (union_eq G H)
    min G H := .mk (G.toSubgroup ⊓ H.toSubgroup)
      fun _a _b hab hb1 ha ↦ ⟨G.convex hab hb1 ha.1, H.convex hab hb1 ha.2⟩
    min_def G H := toSubgroup_injective <| (em (G ≤ H)).elim
      (by simpa [·]) fun h ↦ by simpa [h] using (total G H).resolve_left h }

theorem coe_max : max G H = (G : Set α) ∪ H := rfl
theorem coe_min : min G H = (G : Set α) ∩ H := rfl

@[to_additive] instance : SupSet (ConvexSubgroup α) where
  sSup s :=
  { carrier := {1} ∪ ⋃ G : s, G
    mul_mem' ha hb := by
      rw [Set.mem_union, Set.mem_iUnion] at ha hb ⊢
      obtain rfl | ⟨G, haG⟩ := ha; · simpa using hb
      obtain rfl | ⟨H, hbH⟩ := hb; · simpa using .inr ⟨G, G.2, haG⟩
      right
      obtain le | le := le_total G H
      exacts [⟨H, mul_mem (le haG) hbH⟩, ⟨G, mul_mem haG (le hbH)⟩]
    inv_mem' := by simp
    one_mem' := by simp
    convex a b hab hb1 := by
      rintro (rfl | ex)
      · exact .inl (hb1.antisymm hab)
      obtain ⟨G, haG⟩ := Set.mem_iUnion.mp ex
      exact .inr <| Set.mem_iUnion.mpr ⟨G, G.1.convex hab hb1 haG⟩ }

@[to_additive] instance : InfSet (ConvexSubgroup α) where
  sInf s := .mk (⨅ G : s, G.1.toSubgroup) fun a b hab hb1 ha ↦ by
    rw [Subgroup.mem_iInf] at ha ⊢
    exact fun G ↦ G.1.convex hab hb1 (ha G)

@[to_additive] noncomputable instance : CompleteLattice (ConvexSubgroup α) := by
  refine ConvexSubgroup.toSubgroup_injective.completeLattice _
    (fun G H ↦ le_antisymm ?_ ?_) (fun _ _ ↦ rfl)
    (fun s ↦ le_antisymm (fun a ha ↦ ?_) ?_) (fun _ ↦ iInf_subtype) rfl rfl
  · rintro a (ha | ha); exacts [G.mem_sup_left ha, G.mem_sup_right ha]
  · exact sup_le (le_max_left (a := G) (b := H)) (le_max_right (a := G) (b := H))
  · obtain rfl | ha := ha; · exact one_mem _
    have ⟨G, haG⟩ := Set.mem_iUnion.mp ha
    exact Subgroup.mem_iSup_of_mem G.1 (Subgroup.mem_iSup_of_mem G.2 haG)
  · exact iSup₂_le fun G hG a haG ↦ .inr (Set.mem_iUnion_of_mem ⟨G, hG⟩ haG)

@[to_additive] noncomputable instance : CompleteLinearOrder (ConvexSubgroup α) where
  __ : LinearOrder _ := inferInstance
  __ := LinearOrder.toBiheytingAlgebra _
  __ : CompleteLattice _ := inferInstance

@[to_additive] instance : HasQuotient α (ConvexSubgroup α) where
  quotient' G := α ⧸ G.toSubgroup

@[to_additive] instance : CommGroup (α ⧸ G) := inferInstanceAs <| CommGroup (α ⧸ G.toSubgroup)

@[to_additive] local instance (x : Quotient (QuotientGroup.leftRel G.toSubgroup)) :
    (Quotient.mk _ ⁻¹' {x}).OrdConnected where
  out' := by
    rintro ax rfl ay eq a ha
    exact QuotientGroup.eq.mpr (G.convex (a := ay⁻¹ * ax) (by have := ha.2; gcongr)
      (inv_mul_le_one_iff.mpr ha.1) <| QuotientGroup.eq.mp eq)

/-- The linear order on the quotient of a linearly ordered abelian group by a convex subgroup. -/
@[to_additive] noncomputable instance : LinearOrder (α ⧸ G) := by
  classical exact inferInstanceAs (LinearOrder (Quotient _))

@[to_additive] instance : IsOrderedMonoid (α ⧸ G) :=
  have {x y z : α ⧸ G} (le : x ≤ y) : z * x ≤ z * y := by
    rw [Quotient.le_iff_forall_left_exists] at le ⊢
    obtain ⟨b, rfl, hb⟩ := le _ x.out_eq
    exact fun ca hca ↦ ⟨ca * x.out⁻¹ * b, by simp [hca], by simpa [mul_assoc]⟩
  { mul_le_mul_left _ _ le z := by simpa only [← mul_comm z] using this le
    mul_le_mul_right _ _ le _ := this le }

/-- The quotient map by a convex subgroup as an ordered group homomorphism. -/
@[to_additive
/-- The quotient map by a convex subgroup as an ordered additive group homomorphism. -/]
def QuotientGroup.mkOrderedMonoidHom : α →*o α ⧸ G where
  __ := QuotientGroup.mk' G.toSubgroup
  monotone' _ _ le := Quotient.mk_le_mk.mpr (.inl le)

end ConvexSubgroup

variable [IsOrderedMonoid α]

open MulArchimedeanClass in
@[to_additive] theorem FiniteMulArchimedeanClass.isConvexSubgroup_subgroup
    (s : UpperSet (FiniteMulArchimedeanClass α)) : IsConvexSubgroup (subgroup s) :=
  fun _a _b hab b_le ha b_ne ↦
    s.upper (mk_monotoneOn (hab.trans b_le) b_le hab)
      (ha <| mk_eq_top_iff.not.mpr (hab.trans_lt (b_le.lt_of_ne <| mk_eq_top_iff.not.mp b_ne)).ne)

@[to_additive] theorem ConvexSubgroup.mem_of_finiteMulArchimedeanClass_mk_le
    {G : ConvexSubgroup α} {a b : α} {ha1 : a ≠ 1} {hb1 : b ≠ 1}
    (le : FiniteMulArchimedeanClass.mk a ha1 ≤ .mk b hb1)
    (haG : a ∈ G) : b ∈ G := by
  rw [FiniteMulArchimedeanClass.mk_le_mk, MulArchimedeanClass.mk_le_mk] at le
  have ⟨n, le⟩ := le
  exact mabs_mem_iff.mp <| (IsConvexSubgroup.iff_ordConnected.mp G.convex).1
    G.one_mem (G.pow_mem (by simpa) _) ⟨one_le_mabs _, le⟩

open MulArchimedeanClass in
/-- The convex subgroups of a linearly ordered group are in bijection with upper sets of
`FiniteMulArchimedeanClass`es. -/
@[to_additive /-- The convex subgroups of a linearly ordered additive group are in bijection with
upper sets of `FiniteArchimedeanClass`es. -/]
def ConvexSubgroup.equivUpperSet :
    ConvexSubgroup α ≃ UpperSet (FiniteMulArchimedeanClass α) where
  toFun G := .mk {x | ∃ a : α, ∃ ha : a ≠ 1, a ∈ G ∧ x = .mk a ha} fun x y le ↦ by
    rintro ⟨a, ha1, haG, rfl⟩
    revert y
    refine FiniteMulArchimedeanClass.ind fun b hb1 le ↦ ?_
    exact ⟨b, hb1, mabs_mem_iff.mp <| by
      simpa using G.mem_of_finiteMulArchimedeanClass_mk_le le haG, rfl⟩
  invFun s := .mk _ (FiniteMulArchimedeanClass.isConvexSubgroup_subgroup s)
  left_inv G := by
    refine SetLike.ext fun a ↦ ⟨fun h ↦ ?_, fun h ha ↦ ⟨a, mk_eq_top_iff.not.mp ha, h, rfl⟩⟩
    obtain rfl | ha1 := eq_or_ne a 1; · simp
    have ⟨b, hb1, hbG, eq⟩ := h (mk_eq_top_iff.not.mpr ha1)
    exact G.mem_of_finiteMulArchimedeanClass_mk_le (hb1 := ha1) eq.ge hbG
  right_inv s := UpperSet.ext <| Set.ext <| FiniteMulArchimedeanClass.ind fun a ha1 ↦
    ⟨fun ⟨b, hb1, hbs, eq⟩ ↦ by simpa only [eq] using hbs (mk_eq_top_iff.not.mpr hb1),
      fun h ↦ ⟨a, ha1, fun _ ↦ h, rfl⟩⟩

/-- The convex subgroups of a linearly ordered group are in order-reversing bijection
with upper sets of `FiniteMulArchimedeanClass`es. -/
@[to_additive /-- The convex subgroups of a linearly ordered additive group are in order-reversing
bijection with upper sets of `FiniteArchimedeanClass`es. -/]
def ConvexSubgroup.orderIsoUpperSet :
    ConvexSubgroup α ≃o (UpperSet (FiniteMulArchimedeanClass α))ᵒᵈ :=
  (equivUpperSet.trans OrderDual.toDual).toOrderIso
    (fun _G _H le _x ⟨a, ha1, haH, eq⟩ ↦ ⟨a, ha1, le haH, eq⟩)
    fun _s _t le _a hat ha1 ↦ le (hat ha1)

@[to_additive] lemma mulArchimedean_iff_subsingleton_finiteMulArchimedeanClass :
    MulArchimedean α ↔ Subsingleton (FiniteMulArchimedeanClass α) where
  mp _ := inferInstance
  mpr s := MulArchimedeanClass.mulArchimedean_of_mk_eq_mk
    fun a ha b hb ↦ congr_arg Subtype.val (s.elim (.mk a ha) (.mk b hb))

namespace LinearOrderedCommGroup

variable (α) in
/-- The height of a totally ordered abelian group is the number of non-trivial convex subgroups. -/
@[to_additive /-- The height of a totally ordered additive abelian group
is the number of non-trivial convex subgroups. -/]
noncomputable def height : ℕ∞ := .card {G : ConvexSubgroup α // G ≠ ⊥}

omit [IsOrderedMonoid α] in
@[to_additive] theorem height_eq_card_convexSubgroup_sub_one :
    height α = .card (ConvexSubgroup α) - 1 := by
  apply ENat.add_right_injective_of_ne_top ENat.one_ne_top
  convert congr_arg Cardinal.toENat (Cardinal.mk_sum_compl {(⊥ : ConvexSubgroup α)})
  · simp; rfl
  · exact add_tsub_cancel_of_le ((ENat.one_le_card_iff_nonempty _).mpr inferInstance)

@[to_additive] theorem height_eq_zero_iff : height α = 0 ↔ Subsingleton α := by
  rw [height, ENat.card_eq_zero_iff_empty]
  constructor <;> intro h
  · contrapose! h; simpa using exists_ne _
  · simpa [isEmpty_iff, eq_comm] using Subsingleton.elim _

end LinearOrderedCommGroup

@[to_additive finite_finiteArchimedeanClass_iff_convexAddSubgroup]
lemma finite_finiteMulArchimedeanClass_iff_convexSubgroup :
    Finite (FiniteMulArchimedeanClass α) ↔ Finite (ConvexSubgroup α) := by
  rw [ConvexSubgroup.equivUpperSet.finite_iff]
  constructor <;> intro
  · rw [OrderIso.upperSetWithTopOfFinite.toEquiv.finite_iff, WithTop]; infer_instance
  · exact .of_injective _ (OrderEmbedding.infIrredUpperSet.toEmbedding.trans (.subtype _)).injective

open LinearOrderedCommGroup

@[to_additive height_eq_card_finiteArchimedeanClass]
lemma height_eq_card_finiteMulArchimedeanClass :
    height α = ENat.card (FiniteMulArchimedeanClass α) := by
  rw [height_eq_card_convexSubgroup_sub_one]
  by_cases fin : Finite (FiniteMulArchimedeanClass α)
  · simp_rw [ENat.card_congr <| ConvexSubgroup.equivUpperSet.trans
      OrderIso.upperSetWithTopOfFinite.toEquiv, ENat.card, WithTop, ← Nat.cast_card,
      Finite.card_option, Nat.cast_add, map_add, map_natCast]
    rfl
  · have := finite_finiteMulArchimedeanClass_iff_convexSubgroup.not.mp fin
    rw [not_finite_iff_infinite] at fin this
    simp_rw [ENat.card_eq_top_of_infinite]
    rfl

@[to_additive archimedean_iff_height_le_one]
lemma mulArchimedean_iff_height_le_one : MulArchimedean α ↔ height α ≤ 1 := by
  rw [height_eq_card_finiteMulArchimedeanClass, ENat.card_le_one_iff_subsingleton,
    mulArchimedean_iff_subsingleton_finiteMulArchimedeanClass]

lemma archimedean_iff_exists_orderAddMonoidHom {α} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] : Archimedean α ↔ ∃ f : α →+o ℝ, Function.Injective f where
  mp _ := Archimedean.exists_orderAddMonoidHom_real_injective α
  mpr := fun ⟨f, hf⟩ ↦ .comap f.toAddMonoidHom (f.monotone'.strictMono_of_injective hf)

lemma mulArchimedean_iff_exists_orderMonoidHom :
    MulArchimedean α ↔ ∃ f : α →*o Multiplicative ℝ, Function.Injective f where
  mp _ := have ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective (Additive α)
    ⟨⟨⟨⟨f, f.map_zero⟩, f.map_add⟩, f.monotone'⟩, hf⟩
  mpr := fun ⟨f, hf⟩ ↦ .comap f.toMonoidHom (f.monotone'.strictMono_of_injective hf)

theorem MulArchimedean.tfae : List.TFAE
  [ MulArchimedean α,
    height α ≤ 1,
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f] := by
  tfae_have 1 ↔ 2 := mulArchimedean_iff_height_le_one
  tfae_have 1 ↔ 3 := mulArchimedean_iff_exists_orderMonoidHom
  tfae_finish

/-- Equivalent characterisations for height 1. (Bourbaki, Eléments de mathématique. Fasc. XXX.
Algèbre commutative. Chapitre 6: Valuations. §4 No5 proposition 8) -/
theorem MulArchimedean.tfae_of_nontrivial [Nontrivial α] : List.TFAE
  [ MulArchimedean α,
    height α = 1,
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f] := by
  convert MulArchimedean.tfae (α := α) using 3
  rw [le_iff_eq_or_lt, or_iff_left]
  rw [ENat.lt_one_iff_eq_zero, height_eq_zero_iff]
  exact not_subsingleton α
