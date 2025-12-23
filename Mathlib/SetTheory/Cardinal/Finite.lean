/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.ENat.Pow
public import Mathlib.Data.ULift
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
-/

@[expose] public section

-- assert_not_exists MonoidWithZero
assert_not_exists Field

open Cardinal Function

noncomputable section

variable {α β : Type*}

universe u v

namespace Nat

/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  letI := Classical.dec
  if h : Finite α then h.exists_equiv_fin.choose else 0

theorem card_eq_of_equiv_fin {n : ℕ} (e : α ≃ Fin n) : Nat.card α = n := by
  have := e.finite_iff.mpr inferInstance
  have ex : ∃ n : ℕ, Nonempty (α ≃ Fin n) := ⟨n, ⟨e⟩⟩
  simp only [Nat.card, this, ↓reduceDIte]
  generalize_proofs h
  let f := e.symm.trans h.choose_spec.some
  rw [Fin.equiv_iff_eq.mp ⟨f⟩]

theorem _root_.Finite.nonempty_equiv_fin_natCard [Finite α] : Nonempty (α ≃ Fin (Nat.card α)) := by
  simp only [Nat.card, ↓reduceDIte, *]
  generalize_proofs h
  exact h.choose_spec

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α := by
  rw [card_eq_of_equiv_fin (Fintype.equivFin α)]

/-- Because this theorem takes `Fintype α` as a non-instance argument, it can be used in particular
when `Fintype.card` ends up with different instance than the one found by inference -/
theorem _root_.Fintype.card_eq_nat_card {_ : Fintype α} : Fintype.card α = Nat.card α :=
  card_eq_fintype_card.symm

lemma card_eq_finsetCard (s : Finset α) : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]

lemma card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Nat.card { x // p x } = Finset.card s := by
  rw [← Fintype.subtype_card s H, Fintype.card_eq_nat_card]

@[simp] theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 :=
  card_eq_of_equiv_fin (Equiv.equivOfIsEmpty α (Fin 0))

@[simp] lemma card_eq_zero_of_infinite [h : Infinite α] : Nat.card α = 0 := by
  simp [Nat.card, h]

lemma cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α := by
  letI := Fintype.ofFinite α
  simp

lemma _root_.Set.Infinite.card_eq_zero {s : Set α} (hs : s.Infinite) : Nat.card s = 0 :=
  @card_eq_zero_of_infinite _ hs.to_subtype

lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  constructor
  · contrapose!
    rintro ⟨nonempty, finite⟩
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
    rw [Nat.card_eq_of_equiv_fin e]
    rintro rfl
    contrapose! nonempty
    rw [e.isEmpty_congr]
    infer_instance
  · rintro (empty | infinite)
    · simp
    · simp

lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [card_eq_zero, not_or]

lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [pos_iff_ne_zero, card_eq_zero]

@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α := (card_ne_zero.1 h).2

theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β := by
  cases finite_or_infinite α with
  | inl h1 =>
    have h2 := f.finite_iff.mp inferInstance
    obtain ⟨n1, ⟨e1⟩⟩ := h1.exists_equiv_fin
    obtain ⟨n2, ⟨e2⟩⟩ := h2.exists_equiv_fin
    rw [card_eq_of_equiv_fin e1, card_eq_of_equiv_fin e2, ← Fin.equiv_iff_eq]
    exact ⟨e1.symm.trans <| f.trans <| e2⟩
  | inr h =>
    have := f.infinite_iff.mp inferInstance
    rw [card_eq_zero_of_infinite, card_eq_zero_of_infinite]

lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α → β)
    (hf : Injective f) : Nat.card α ≤ Nat.card β := by
  have hα : Finite α := Finite.of_injective f hf
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  simp [Fintype.card_le_of_injective f hf]

lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α → β)
    (hf : Surjective f) : Nat.card β ≤ Nat.card α := by
  have hβ : Finite β := Finite.of_surjective f hf
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  simp [Fintype.card_le_of_surjective f hf]

theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)

protected theorem bijective_iff_injective_and_card [Finite β] (f : α → β) :
    Bijective f ↔ Injective f ∧ Nat.card α = Nat.card β := by
  rw [Bijective, and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff, ← Bijective,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_injective_and_card]

protected theorem bijective_iff_surjective_and_card [Finite α] (f : α → β) :
    Bijective f ↔ Surjective f ∧ Nat.card α = Nat.card β := by
  classical
  rw [_root_.and_comm, Bijective, and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff, ← Bijective, ← and_comm,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_surjective_and_card]

theorem _root_.Function.Injective.bijective_of_nat_card_le [Finite β] {f : α → β}
    (inj : Injective f) (hc : Nat.card β ≤ Nat.card α) : Bijective f :=
  (Nat.bijective_iff_injective_and_card f).mpr
    ⟨inj, hc.antisymm (card_le_card_of_injective f inj) |>.symm⟩

theorem _root_.Function.Surjective.bijective_of_nat_card_le [Finite α] {f : α → β}
    (surj : Surjective f) (hc : Nat.card α ≤ Nat.card β) : Bijective f :=
  (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨surj, hc.antisymm (card_le_card_of_surjective f surj)⟩

lemma card_fin (n : ℕ) : Nat.card (Fin n) = n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

section Set
open Set
variable {s t : Set α}

lemma card_mono (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t := by
  have : Finite t := Finite.to_subtype ht
  exact card_le_card_of_injective (inclusion h) (inclusion_injective h)

lemma card_image_le {f : α → β} (hs : s.Finite) : Nat.card (f '' s) ≤ Nat.card s :=
  have := hs.to_subtype
  card_le_card_of_surjective (imageFactorization f s) imageFactorization_surjective

lemma card_image_of_injOn {f : α → β} (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    have := fintypeImage s f
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]

lemma card_image_of_injective {f : α → β} (hf : Injective f) (s : Set α) :
    Nat.card (f '' s) = Nat.card s := card_image_of_injOn hf.injOn

lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
    Nat.card_congr (e.image s).symm

lemma card_preimage_of_injOn {f : α → β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by
  rw [← Nat.card_image_of_injOn hf, image_preimage_eq_iff.2 hsf]

lemma card_preimage_of_injective {f : α → β} {s : Set β} (hf : Injective f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := card_preimage_of_injOn hf.injOn hsf

lemma card_univ : Nat.card (univ : Set α) = Nat.card α :=
  card_congr (Equiv.Set.univ α)

lemma card_range_of_injective {f : α → β} (hf : Injective f) :
    Nat.card (range f) = Nat.card α := by
  rw [← Nat.card_preimage_of_injective hf le_rfl]
  simp [Nat.card_univ]

end Set

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`. -/
def equivFinOfCardPos {α : Type*} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]

@[simp]
theorem card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1 := by
  obtain ⟨a⟩ := ‹Nonempty α›
  exact card_of_subsingleton a

theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α := by
  refine ⟨fun h => ?_, fun ⟨_, _⟩ => card_unique⟩
  have : Finite α := finite_of_card_ne_zero <| by rw [h]; exact one_ne_zero
  obtain ⟨e⟩ := this.nonempty_equiv_fin_natCard
  rw [e.subsingleton_congr, e.nonempty_congr, h]
  constructor <;> infer_instance

theorem card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ ↦ ⟨a, fun x ↦ s.elim x a⟩, fun ⟨x, h⟩ ↦ ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩

theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α := by
  by_cases! h : Infinite α
  · rw [Nat.card_eq_zero_of_infinite]
    simp only [OfNat.zero_ne_ofNat, ne_eq, false_iff, not_exists, not_and]
    intro x y hxy huniv
    simp [← Set.infinite_univ_iff, ← huniv] at h
  letI := Fintype.ofFinite α
  classical
  rw [← Nat.card_univ, card_eq_card_toFinset, Set.toFinset_univ, Finset.card_eq_two]
  refine exists₂_congr fun x y => and_congr_right fun hxy => ?_
  rw [eq_comm, ← Finset.coe_eq_univ, Finset.coe_pair]

theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x := by
  simp_rw [card_eq_two_iff, Set.eq_univ_iff_forall, Set.mem_insert_iff, Set.mem_singleton_iff,
    ExistsUnique]
  constructor
  · rintro ⟨a, b, hne, h⟩
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, (or_iff_not_imp_left.2 <| hy ·)⟩

@[simp]
theorem card_subtype_true : Nat.card {_a : α // True} = Nat.card α :=
  card_congr <| Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]
theorem card_sum [Finite α] [Finite β] : Nat.card (α ⊕ β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  by_cases h : Nat.card (α × β) = 0
  · rw [card_eq_zero, infinite_prod, isEmpty_prod] at h
    obtain (_|_)|(⟨_, _⟩|⟨_, _⟩) := h <;> simp
  · rw [card_eq_zero, infinite_prod, isEmpty_prod] at h
    push_neg +distrib at h
    obtain ⟨⟨_, _⟩, _|_, _|_⟩ := h
    · simp
    · let := Fintype.ofFinite α
      let := Fintype.ofFinite β
      simp [Nat.card_eq_fintype_card]
    · simp
    · simp

@[simp]
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift

@[simp]
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift

theorem card_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  letI _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

universe w
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by
  lift c to ι → Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

theorem prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α → Cardinal.{v}) :
    #(Π i, (f i).out) = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    letI := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, mk_eq_one]
  · intro α hα h f
    rw [mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax.{v, u}, mk_out, Fintype.prod_option,
      lift_mul, ← h fun a => f (some a)]
    simp

@[elab_as_elim]
theorem induction_empty_option' {P : ∀ (α : Type u) [Fintype α], Prop}
    (of_equiv : ∀ (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›)
    (h_empty : P PEmpty) (h_option : ∀ (α) [Fintype α], P α → P (Option α)) (α : Type u)
    (h_fintype : Fintype α) : P α := by
  apply Fintype.induction_empty_option <;> assumption
theorem card_pi {β : α → Type*} [h : Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  classical
  induction α, h using induction_empty_option' with
  | @of_equiv γ δ _ e h1 =>
    letI := Fintype.ofEquiv _ e.symm
    specialize @h1 (fun b => β (e b))
    trans Nat.card ((a : γ) → β (e a))
    · rw [Nat.card_congr (Equiv.piCongrLeft β e)]
    convert h1
    convert (Equiv.prod_comp ?_ ?_).symm
  | h_empty => simp
  | h_option _ ih =>
    rw [card_congr Equiv.piOptionEquivProd, card_prod, ih, ← Fintype.prod_option (Nat.card <| β ·)]

theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

@[simp]
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n := by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

end Nat

namespace Set
variable {s : Set α}

lemma card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t := by
  rw [singleton_prod, Nat.card_image_of_injective (Prod.mk_right_injective a)]

lemma card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s := by
  rw [prod_singleton, Nat.card_image_of_injective (Prod.mk_left_injective b)]

theorem natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty := by
  simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

lemma natCard_graphOn (s : Set α) (f : α → β) : Nat.card (s.graphOn f) = Nat.card s := by
  rw [← Nat.card_image_of_injOn fst_injOn_graph, image_fst_graphOn]

end Set


namespace ENat

/-- `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`. -/
def card (α : Type*) : ℕ∞ :=
  toENat (mk α)

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α := by
  simp [card]

@[simp high]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ := by
  simp only [card, toENat_eq_top, aleph0_le_mk]

@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by simp [card, aleph0_le_mk_iff]

@[simp high] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by simp [card]

@[simp] theorem card_lt_top : card α < ⊤ ↔ Finite α := by simp [card, lt_aleph0_iff_finite]

@[simp]
theorem card_sum (α β : Type*) :
    card (α ⊕ β) = card α + card β := by
  simp only [card, mk_sum, map_add, toENat_lift]

theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β :=
  Cardinal.toENat_congr f

@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

lemma card_le_card_of_injective {α β : Type*} {f : α → β} (hf : Injective f) : card α ≤ card β := by
  rw [← card_ulift α, ← card_ulift β]
  exact Cardinal.gciENat.gc.monotone_u <| Cardinal.lift_mk_le_lift_mk_of_injective hf

@[simp]
theorem _root_.Cardinal.natCast_le_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n ≤ toENat c ↔ ↑n ≤ c := by
  rw [← toENat_nat n, toENat_le_iff_of_le_aleph0 (le_of_lt (nat_lt_aleph0 n))]

theorem _root_.Cardinal.toENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
    toENat c ≤ n ↔ c ≤ n := by simp

@[simp]
theorem _root_.Cardinal.natCast_eq_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n = toENat c ↔ ↑n = c := by
  rw [le_antisymm_iff, le_antisymm_iff, Cardinal.toENat_le_natCast_iff,
    Cardinal.natCast_le_toENat_iff]

theorem _root_.Cardinal.toENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
    Cardinal.toENat c = n ↔ c = n := by simp

@[simp]
theorem _root_.Cardinal.natCast_lt_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n < toENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toENat_le_natCast_iff]

@[simp]
theorem _root_.Cardinal.toENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
    toENat c < ↑n ↔ c < ↑n := by
  simp only [← not_le, Cardinal.natCast_le_toENat_iff]

theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  rw [← Cardinal.mk_eq_zero_iff]
  simp [card]

theorem card_ne_zero_iff_nonempty (α : Type*) : card α ≠ 0 ↔ Nonempty α := by
  simp [card_eq_zero_iff_empty]

theorem one_le_card_iff_nonempty (α : Type*) : 1 ≤ card α ↔ Nonempty α := by
  simp [one_le_iff_ne_zero, card_eq_zero_iff_empty]

@[simp] lemma card_pos [Nonempty α] : 0 < card α := by
  simpa [pos_iff_ne_zero, card_ne_zero_iff_nonempty]

theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  rw [← le_one_iff_subsingleton]
  simp [card]

@[simp] lemma card_le_one [Subsingleton α] : card α ≤ 1 := by simpa [card_le_one_iff_subsingleton]

lemma card_eq_one_iff_unique {α : Type*} : card α = 1 ↔ Nonempty (Unique α) := by
  rw [unique_iff_subsingleton_and_nonempty α, le_antisymm_iff]
  exact and_congr (card_le_one_iff_subsingleton α) (one_le_card_iff_nonempty α)

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toENat_iff]
  simp only [ENat.card, Nat.cast_one]

@[simp] lemma one_lt_card [Nontrivial α] : 1 < card α := by simpa [one_lt_card_iff_nontrivial]

@[simp]
theorem card_prod (α β : Type*) : card (α × β) = card α * card β := by
  simp [ENat.card]

@[simp]
lemma card_fun {α β : Type*} : card (α → β) = (card β) ^ card α := by
  classical
  rcases isEmpty_or_nonempty α with α_emp | α_emp
  · simp [(card_eq_zero_iff_empty α).2 α_emp]
  rcases finite_or_infinite α
  · rcases finite_or_infinite β
    · letI := Fintype.ofFinite α
      letI := Fintype.ofFinite β
      simp
    · simp only [card_eq_top_of_infinite]
      exact (top_epow (one_le_iff_ne_zero.1 ((one_le_card_iff_nonempty α).2 α_emp))).symm
  · rw [card_eq_top_of_infinite (α := α)]
    rcases lt_trichotomy (card β) 1 with b_0 | b_1 | b_2
    · rw [lt_one_iff_eq_zero, card_eq_zero_iff_empty] at b_0
      rw [(card_eq_zero_iff_empty β).2 b_0, zero_epow_top, card_eq_zero_iff_empty]
      simp [b_0]
    · rw [b_1, one_epow]
      apply le_antisymm
      · letI := (card_le_one_iff_subsingleton β).1 b_1.le
        exact (card_le_one_iff_subsingleton (α → β)).2 Pi.instSubsingleton
      · letI := (one_le_card_iff_nonempty β).1 b_1.ge
        exact (one_le_card_iff_nonempty (α → β)).2 Pi.instNonempty
    · rw [epow_top b_2, card_eq_top]
      rw [one_lt_card_iff_nontrivial β] at b_2
      exact Pi.infinite_of_left

end ENat
