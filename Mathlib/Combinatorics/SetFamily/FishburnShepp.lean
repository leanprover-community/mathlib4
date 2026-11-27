/-
Copyright (c) 2026 Skyler Niedzielski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skyler Niedzielski
-/
module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Fishburn-Shepp inequality

This file proves the Fishburn-Shepp inequality, also known as the XYZ inequality: if `x`, `y`, `z`
are elements of a finite partial order and `σ` is a uniformly random linear extension, then the
events `σ x < σ y` and `σ x < σ z` are positively correlated.

## Main declarations

* `Fintype.linearExtensions α`: the linear extensions of a finite partial order `α`, as the
  order-preserving bijections `α ≃ Fin (card α)`.
* `fishburn_shepp`: the Fishburn-Shepp inequality, in counting form.

## Proof

We follow Shepp's proof through the FKG inequality (see Alon-Spencer, *The Probabilistic Method*,
§6.4), made finite. Order-preserving maps `ω : α → Fin m` are encoded as
`(-ω x, i ↦ ω i - ω x)` in the distributive lattice `ℤ × (α → ℤ)`; their image is closed under
`⊓` and `⊔`, and the events `ω x < ω y` and `ω x < ω z` are up-sets there, so the four functions
theorem correlates them. Injective order-preserving maps `α → Fin m` correspond to pairs of a linear
extension and an `n`-subset of `Fin m`, where `n = card α`, while at most `n ^ 2 * m ^ (n - 1)` maps
are not injective. Letting `m` be large enough concludes.

## References

* [L. A. Shepp, *The XYZ conjecture and the FKG inequality*][Shepp1982]
* [P. C. Fishburn, *A correlational inequality for linear extensions of a poset*][Fishburn1984]
-/

public section

open Finset
open scoped FinsetFamily

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableLT α]

namespace Fintype

variable (α) in
/-- The linear extensions of a finite partial order `α`, as the order-preserving bijections
`α ≃ Fin (card α)`. -/
def linearExtensions : Finset (α ≃ Fin (card α)) := {σ | ∀ a b, a < b → σ a < σ b}

@[simp]
lemma mem_linearExtensions {σ : α ≃ Fin (card α)} :
    σ ∈ linearExtensions α ↔ StrictMono σ := by
  simp [linearExtensions, StrictMono]

end Fintype

namespace FishburnShepp

variable (α) in
/-- Auxiliary for `fishburn_shepp`: the maps `ω : α → Fin m` with `a < b → ω a < ω b`. -/
def strictMaps (m : ℕ) : Finset (α → Fin m) := {ω | ∀ a b, a < b → ω a < ω b}

lemma mem_strictMaps {m : ℕ} {ω : α → Fin m} :
    ω ∈ strictMaps α m ↔ ∀ a b, a < b → ω a < ω b := by
  simp [strictMaps]

omit [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableLT α] in
/-- Auxiliary for `fishburn_shepp`: Shepp's encoding of a map, relative to the base point `x`. -/
def enc (x : α) {m : ℕ} (ω : α → Fin m) : ℤ × (α → ℤ) :=
  (-((ω x : ℕ) : ℤ), fun i ↦ ((ω i : ℕ) : ℤ) - ((ω x : ℕ) : ℤ))

omit [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableLT α] in
lemma enc_injective (x : α) (m : ℕ) : Function.Injective (enc x (m := m)) := by
  intro ω₁ ω₂ h
  simp only [enc, Prod.mk.injEq, neg_inj, funext_iff] at h
  obtain ⟨h₀, h₁⟩ := h
  funext i
  have := h₁ i
  apply Fin.ext
  omega

lemma exists_of_int {m : ℕ} (v : α → ℤ) (hv₀ : ∀ i, 0 ≤ v i) (hvm : ∀ i, v i < m)
    (hv : ∀ a b, a < b → v a < v b) :
    ∃ ω ∈ strictMaps α m, ∀ i, ((ω i : ℕ) : ℤ) = v i := by
  refine ⟨fun i ↦ ⟨(v i).toNat, by have := hv₀ i; have := hvm i; omega⟩, ?_, fun i ↦ ?_⟩
  · rw [mem_strictMaps]
    intro a b hab
    have := hv a b hab
    have := hv₀ a
    rw [Fin.lt_def]
    dsimp only
    omega
  · dsimp only
    have := hv₀ i
    omega

lemma mem_image_enc {x : α} {m : ℕ} {p : ℤ × (α → ℤ)} :
    p ∈ (strictMaps α m).image (enc x) ↔
      ∃ v : α → ℤ, (∀ i, 0 ≤ v i) ∧ (∀ i, v i < m) ∧ (∀ a b, a < b → v a < v b) ∧
        p = (-v x, fun i ↦ v i - v x) := by
  constructor
  · intro hp
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hp
    rw [mem_strictMaps] at hω
    refine ⟨fun i ↦ ((ω i : ℕ) : ℤ), fun i ↦ by positivity,
      fun i ↦ by dsimp only; have := (ω i).isLt; omega, fun a b hab ↦ ?_, rfl⟩
    have := hω a b hab
    rw [Fin.lt_def] at this
    dsimp only
    omega
  · rintro ⟨v, hv₀, hvm, hv, rfl⟩
    obtain ⟨ω, hω, hωv⟩ := exists_of_int v hv₀ hvm hv
    exact Finset.mem_image.2 ⟨ω, hω, by simp only [enc, hωv]⟩

lemma sup_mem_image_enc {x : α} {m : ℕ} {p q : ℤ × (α → ℤ)}
    (hp : p ∈ (strictMaps α m).image (enc x)) (hq : q ∈ (strictMaps α m).image (enc x)) :
    p ⊔ q ∈ (strictMaps α m).image (enc x) := by
  obtain ⟨v, hv₀, hvm, hv, rfl⟩ := mem_image_enc.1 hp
  obtain ⟨w, hw₀, hwm, hw, rfl⟩ := mem_image_enc.1 hq
  refine mem_image_enc.2 ⟨fun i ↦ max (v i - v x) (w i - w x) + min (v x) (w x),
    fun i ↦ ?_, fun i ↦ ?_, fun a b hab ↦ ?_, ?_⟩
  · dsimp only; have := hv₀ i; have := hw₀ i; omega
  · dsimp only; have := hvm i; have := hwm i; omega
  · dsimp only; have := hv a b hab; have := hw a b hab; omega
  · ext i
    · simp only [Prod.fst_sup, sub_self, max_self, zero_add]
      omega
    · simp only [Prod.snd_sup, Pi.sup_apply, sub_self, max_self, zero_add]
      omega

lemma inf_mem_image_enc {x : α} {m : ℕ} {p q : ℤ × (α → ℤ)}
    (hp : p ∈ (strictMaps α m).image (enc x)) (hq : q ∈ (strictMaps α m).image (enc x)) :
    p ⊓ q ∈ (strictMaps α m).image (enc x) := by
  obtain ⟨v, hv₀, hvm, hv, rfl⟩ := mem_image_enc.1 hp
  obtain ⟨w, hw₀, hwm, hw, rfl⟩ := mem_image_enc.1 hq
  refine mem_image_enc.2 ⟨fun i ↦ min (v i - v x) (w i - w x) + max (v x) (w x),
    fun i ↦ ?_, fun i ↦ ?_, fun a b hab ↦ ?_, ?_⟩
  · dsimp only; have := hv₀ i; have := hw₀ i; omega
  · dsimp only; have := hvm i; have := hwm i; omega
  · dsimp only; have := hv a b hab; have := hw a b hab; omega
  · ext i
    · simp only [Prod.fst_inf, sub_self, min_self, zero_add]
      omega
    · simp only [Prod.snd_inf, Pi.inf_apply, sub_self, min_self, zero_add]
      omega

/-- **Shepp's correlation inequality** for order-preserving maps into `Fin m`: the events
`ω x < ω y` and `ω x < ω z` are positively correlated under the uniform measure on
`strictMaps α m`. -/
theorem card_mul_card_le_strictMaps (m : ℕ) (x y z : α) :
    #{ω ∈ strictMaps α m | ω x < ω y} * #{ω ∈ strictMaps α m | ω x < ω z} ≤
      #(strictMaps α m) * #{ω ∈ strictMaps α m | ω x < ω y ∧ ω x < ω z} := by
  set S := (strictMaps α m).image (enc x) with hS
  let f₁ : ℤ × (α → ℤ) → ℕ := fun p ↦ if 0 < p.2 y then 1 else 0
  let f₂ : ℤ × (α → ℤ) → ℕ := fun p ↦ if 0 < p.2 z then 1 else 0
  let f₃ : ℤ × (α → ℤ) → ℕ := fun _ ↦ 1
  let f₄ : ℤ × (α → ℤ) → ℕ := fun p ↦ if 0 < p.2 y ∧ 0 < p.2 z then 1 else 0
  have key := four_functions_theorem f₁ f₂ f₃ f₄ (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
    (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _) (fun a b ↦ by
      simp only [f₁, f₂, f₃, f₄, Prod.snd_sup, Pi.sup_apply, one_mul]
      split_ifs <;> simp_all) S S
  have hinf : S ⊼ S ⊆ S := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_infs.1 hp
    exact inf_mem_image_enc ha hb
  have hsup : S ⊻ S ⊆ S := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sups.1 hp
    exact sup_mem_image_enc ha hb
  have h₃ : ∑ p ∈ S ⊼ S, f₃ p ≤ ∑ p ∈ S, f₃ p :=
    Finset.sum_le_sum_of_subset_of_nonneg hinf fun _ _ _ ↦ Nat.zero_le _
  have h₄ : ∑ p ∈ S ⊻ S, f₄ p ≤ ∑ p ∈ S, f₄ p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsup fun _ _ _ ↦ Nat.zero_le _
  have key' := key.trans (Nat.mul_le_mul h₃ h₄)
  simp only [hS, Finset.sum_image (enc_injective x m).injOn, f₁, f₂, f₃, f₄, enc,
    Finset.sum_const, smul_eq_mul, mul_one] at key'
  simp only [Finset.card_filter]
  convert key' using 3 <;> simp only [sub_pos, Nat.cast_lt, Fin.lt_def]

omit [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableLT α] in
lemma orderIsoOfFin_symm_orderEmbOfFin {β : Type*} [LinearOrder β] {n : ℕ} {S T : Finset β}
    (hS : #S = n) (hT : #T = n) (hTS : T = S) (k : Fin n) (hx : S.orderEmbOfFin hS k ∈ T) :
    (T.orderIsoOfFin hT).symm ⟨S.orderEmbOfFin hS k, hx⟩ = k := by
  subst hTS
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext (Finset.coe_orderIsoOfFin_apply _ _ _).symm

/-- Injective order-preserving maps `α → Fin m` satisfying an order-invariant event `Q` are counted
by injective order-preserving maps `α → Fin (card α)` satisfying `Q`, times
`m.choose (card α)`. -/
theorem card_inj_strictMaps (m : ℕ) (Q : (α → α → Prop) → Prop) [DecidablePred Q] :
    #{ω ∈ strictMaps α m | Function.Injective ω ∧ Q (fun a b ↦ ω a < ω b)} =
      #{f ∈ strictMaps α (Fintype.card α) | Function.Injective f ∧ Q (fun a b ↦ f a < f b)} *
        m.choose (Fintype.card α) := by
  set n := Fintype.card α with hn
  have hchoose : m.choose n = #(powersetCard n (univ : Finset (Fin m))) := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [hchoose, ← card_product]
  symm
  refine card_bij'
    (fun p hp a ↦ p.2.orderEmbOfFin (mem_powersetCard.1 (mem_product.1 hp).2).2 (p.1 a))
    (fun ω hω ↦ (fun a ↦ ((univ.image ω).orderIsoOfFin (by
        rw [card_image_of_injective _ (mem_filter.1 hω).2.1, card_univ])).symm
          ⟨ω a, mem_image_of_mem _ (mem_univ _)⟩, univ.image ω)) ?_ ?_ ?_ ?_
  · rintro ⟨f, S⟩ hp
    obtain ⟨hf, hS⟩ := mem_product.1 hp
    obtain ⟨hf, hfi, hfQ⟩ := mem_filter.1 hf
    rw [mem_strictMaps] at hf
    refine mem_filter.2 ⟨mem_strictMaps.2 fun a b hab ↦ ?_, ?_, ?_⟩
    · exact (S.orderEmbOfFin _).strictMono (hf a b hab)
    · exact (S.orderEmbOfFin _).injective.comp hfi
    · simpa only [OrderEmbedding.lt_iff_lt] using hfQ
  · intro ω hω
    obtain ⟨hω, hωi, hωQ⟩ := mem_filter.1 hω
    rw [mem_strictMaps] at hω
    refine mem_product.2 ⟨mem_filter.2 ⟨mem_strictMaps.2 fun a b hab ↦ ?_, ?_, ?_⟩, ?_⟩
    · simp only [OrderIso.lt_iff_lt, Subtype.mk_lt_mk]
      exact hω a b hab
    · intro a b hab
      exact hωi (by simpa using hab)
    · simpa only [OrderIso.lt_iff_lt, Subtype.mk_lt_mk] using hωQ
    · rw [mem_powersetCard]
      exact ⟨subset_univ _, by rw [card_image_of_injective _ hωi, card_univ]⟩
  · rintro ⟨f, S⟩ hp
    obtain ⟨hf, hS⟩ := mem_product.1 hp
    obtain ⟨-, hfi, -⟩ := mem_filter.1 hf
    have hfs : Function.Surjective f :=
      ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, by simp [hn]⟩).2
    have himg : univ.image (fun a ↦ S.orderEmbOfFin (mem_powersetCard.1 hS).2 (f a)) = S := by
      change image ((S.orderEmbOfFin _) ∘ f) univ = S
      rw [← image_image, image_univ_of_surjective hfs, image_orderEmbOfFin_univ]
    ext1
    · funext a
      exact orderIsoOfFin_symm_orderEmbOfFin _ _ himg _ _
    · exact himg
  · intro ω hω
    funext a
    dsimp only
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

omit [PartialOrder α] [DecidableLT α] in
/-- At most `m ^ (card α - 1)` maps `α → Fin m` identify two given distinct points. -/
lemma card_eq_le (m : ℕ) {a b : α} (hab : a ≠ b) :
    #{ω : α → Fin m | ω a = ω b} ≤ m ^ (Fintype.card α - 1) := by
  have : #{ω : α → Fin m | ω a = ω b} ≤ Fintype.card ({c : α // c ≠ b} → Fin m) := by
    rw [← card_univ]
    refine card_le_card_of_injOn (fun ω c ↦ ω c) (fun _ _ ↦ mem_univ _) ?_
    intro ω₁ h₁ ω₂ h₂ h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
    funext c
    by_cases hc : c = b
    · subst hc
      rw [← h₁, ← h₂]
      exact congrFun h ⟨a, hab⟩
    · exact congrFun h ⟨c, hc⟩
  refine this.trans (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [PartialOrder α] [DecidableLT α] in
/-- At most `card α ^ 2 * m ^ (card α - 1)` maps `α → Fin m` are not injective. -/
theorem card_not_injective_le (m : ℕ) :
    #{ω : α → Fin m | ¬ Function.Injective ω} ≤
      Fintype.card α ^ 2 * m ^ (Fintype.card α - 1) := by
  have hsub : ({ω : α → Fin m | ¬ Function.Injective ω} : Finset _) ⊆
      ({p : α × α | p.1 ≠ p.2} : Finset (α × α)).biUnion
        fun p ↦ {ω : α → Fin m | ω p.1 = ω p.2} := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and, Function.Injective, not_forall] at hω
    obtain ⟨a, b, h, hab⟩ := hω
    exact mem_biUnion.2 ⟨(a, b), by simpa using hab, by simpa using h⟩
  refine (card_le_card hsub).trans <| card_biUnion_le.trans ?_
  calc ∑ p ∈ {p : α × α | p.1 ≠ p.2}, #{ω : α → Fin m | ω p.1 = ω p.2}
      ≤ ∑ _p ∈ {p : α × α | p.1 ≠ p.2}, m ^ (Fintype.card α - 1) :=
        sum_le_sum fun p hp ↦ card_eq_le m (mem_filter.1 hp).2
    _ ≤ ∑ _p : α × α, m ^ (Fintype.card α - 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ Nat.zero_le _
    _ = Fintype.card α ^ 2 * m ^ (Fintype.card α - 1) := by
        rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul, sq]

/-- `e * m.choose n ≤ #{ω ∈ strictMaps α m | Q} ≤ e * m.choose n + n ^ 2 * m ^ (n - 1)`, where
`e` counts the injective members of `strictMaps α n` satisfying `Q`. -/
theorem card_strictMaps_bounds (m : ℕ) (Q : (α → α → Prop) → Prop) [DecidablePred Q] :
    #{f ∈ strictMaps α (Fintype.card α) | Function.Injective f ∧ Q (fun a b ↦ f a < f b)} *
        m.choose (Fintype.card α) ≤ #{ω ∈ strictMaps α m | Q (fun a b ↦ ω a < ω b)} ∧
      #{ω ∈ strictMaps α m | Q (fun a b ↦ ω a < ω b)} ≤
        #{f ∈ strictMaps α (Fintype.card α) | Function.Injective f ∧ Q (fun a b ↦ f a < f b)} *
          m.choose (Fintype.card α) + Fintype.card α ^ 2 * m ^ (Fintype.card α - 1) := by
  rw [← card_inj_strictMaps]
  constructor
  · refine card_le_card fun ω hω ↦ ?_
    simp only [mem_filter] at hω ⊢
    exact ⟨hω.1, hω.2.2⟩
  · have hsplit : ({ω ∈ strictMaps α m | Q (fun a b ↦ ω a < ω b)} : Finset _) ⊆
        {ω ∈ strictMaps α m | Function.Injective ω ∧ Q (fun a b ↦ ω a < ω b)} ∪
          ({ω : α → Fin m | ¬ Function.Injective ω} : Finset (α → Fin m)) := by
      intro ω hω
      simp only [mem_filter, mem_union, mem_univ, true_and] at hω ⊢
      by_cases h : Function.Injective ω
      · exact Or.inl ⟨hω.1, h, hω.2⟩
      · exact Or.inr h
    exact (card_le_card hsplit).trans <| (card_union_le _ _).trans <|
      Nat.add_le_add_left (card_not_injective_le m) _

/-- Linear extensions are the injective members of `strictMaps α (card α)`. -/
lemma card_linearExtensions_filter (Q : (α → α → Prop) → Prop) [DecidablePred Q] :
    #{σ ∈ Fintype.linearExtensions α | Q (fun a b ↦ σ a < σ b)} =
      #{f ∈ strictMaps α (Fintype.card α) | Function.Injective f ∧ Q (fun a b ↦ f a < f b)} := by
  rw [← card_image_of_injective _ (DFunLike.coe_injective (F := α ≃ Fin (Fintype.card α)))]
  congr 1
  ext f
  simp only [mem_image, mem_filter, Fintype.mem_linearExtensions, mem_strictMaps]
  constructor
  · rintro ⟨σ, ⟨hσ, hQ⟩, rfl⟩
    exact ⟨fun a b hab ↦ hσ hab, σ.injective, hQ⟩
  · rintro ⟨hf, hfi, hQ⟩
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, by simp⟩
    exact ⟨Equiv.ofBijective f hbij, ⟨fun a b hab ↦ hf a b hab, hQ⟩, rfl⟩

/-- The arithmetic of the limit step in `fishburn_shepp`. -/
lemma limit_arith {e eA eB eAB C K F FA FB FAB M : ℕ}
    (hF : F ≤ e * C + K) (hFAB : FAB ≤ eAB * C + K) (hFA : eA * C ≤ FA) (hFB : eB * C ≤ FB)
    (hcorr : FA * FB ≤ F * FAB) (he : e ≤ M) (heAB : eAB ≤ M) (hK : 0 < K)
    (hC : (2 * M + 2) * K ≤ C) : eA * eB ≤ e * eAB := by
  by_contra! h
  have h1 : (eA * eB) * (C * C) ≤ (e * C + K) * (eAB * C + K) :=
    calc (eA * eB) * (C * C) = (eA * C) * (eB * C) := by ring
      _ ≤ FA * FB := Nat.mul_le_mul hFA hFB
      _ ≤ F * FAB := hcorr
      _ ≤ (e * C + K) * (eAB * C + K) := Nat.mul_le_mul hF hFAB
  have h2 : (e * eAB + 1) * (C * C) ≤ (eA * eB) * (C * C) := Nat.mul_le_mul_right _ h
  have h3 : K * C * (e + eAB) ≤ K * C * (2 * M) := Nat.mul_le_mul_left _ (by omega)
  have hKC : K ≤ C := le_trans (by nlinarith) hC
  have h4 : (2 * M + 2) * K * C ≤ C * C := Nat.mul_le_mul_right _ hC
  nlinarith

/-- Some `m > 0` makes `m.choose n` large compared with `n ^ 2 * m ^ (n - 1)`. -/
lemma exists_choose_large (n M : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 0 < m ∧ (2 * M + 2) * (n ^ 2 * m ^ (n - 1)) ≤ m.choose n := by
  set D := (2 * M + 2) * n ^ 2 * n.factorial * 2 ^ (n - 1) with hD
  set T := D + n with hT
  refine ⟨n + T, by omega, Nat.le_of_mul_le_mul_left ?_ n.factorial_pos⟩
  have hdesc : (T + 1) ^ n ≤ n.factorial * (n + T).choose n := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    calc (T + 1) ^ n = (n + T + 1 - n) ^ n := by congr 1; omega
      _ ≤ _ := Nat.pow_sub_le_descFactorial _ _
  have hm : (n + T) ^ (n - 1) ≤ 2 ^ (n - 1) * T ^ (n - 1) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) _
  have hTn : T ^ n = T * T ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  calc n.factorial * ((2 * M + 2) * (n ^ 2 * (n + T) ^ (n - 1)))
      ≤ n.factorial * ((2 * M + 2) * (n ^ 2 * (2 ^ (n - 1) * T ^ (n - 1)))) := by gcongr
    _ = D * T ^ (n - 1) := by rw [hD]; ring
    _ ≤ T * T ^ (n - 1) := Nat.mul_le_mul_right _ (by omega)
    _ = T ^ n := hTn.symm
    _ ≤ (T + 1) ^ n := Nat.pow_le_pow_left (by omega) _
    _ ≤ n.factorial * (n + T).choose n := hdesc

omit [PartialOrder α] [DecidableEq α] [DecidableLT α] in
lemma card_linearExtensions_le (s : Finset (α ≃ Fin (Fintype.card α))) :
    #s ≤ Fintype.card α ^ Fintype.card α := by
  classical
  calc #s ≤ #(univ : Finset (α ≃ Fin (Fintype.card α))) := card_le_univ _
    _ ≤ #(univ : Finset (α → Fin (Fintype.card α))) := by
        rw [card_univ, card_univ]
        exact Fintype.card_le_of_injective _ DFunLike.coe_injective
    _ = _ := by simp

end FishburnShepp

open FishburnShepp in
/-- The **Fishburn-Shepp inequality**, aka **XYZ inequality**: for `x`, `y`, `z` in a finite
partial order, the events `x < y` and `x < z` are positively correlated over its linear extensions:
`#{σ | σ x < σ y} * #{σ | σ x < σ z} ≤ #{σ} * #{σ | σ x < σ y ∧ σ x < σ z}`. -/
theorem fishburn_shepp (x y z : α) :
    #{σ ∈ Fintype.linearExtensions α | σ x < σ y} *
        #{σ ∈ Fintype.linearExtensions α | σ x < σ z} ≤
      #(Fintype.linearExtensions α) *
        #{σ ∈ Fintype.linearExtensions α | σ x < σ y ∧ σ x < σ z} := by
  classical
  set n := Fintype.card α
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨x⟩
  obtain ⟨m, hm, hC⟩ := exists_choose_large n (n ^ n) hn1
  have hK : 0 < n ^ 2 * m ^ (n - 1) := Nat.mul_pos (pow_pos (by omega) 2) (pow_pos hm _)
  have bT := card_strictMaps_bounds (α := α) m (fun _ ↦ True)
  have bA := card_strictMaps_bounds (α := α) m (fun r ↦ r x y)
  have bB := card_strictMaps_bounds (α := α) m (fun r ↦ r x z)
  have bAB := card_strictMaps_bounds (α := α) m (fun r ↦ r x y ∧ r x z)
  have eT := card_linearExtensions_filter (α := α) (fun _ ↦ True)
  have eA := card_linearExtensions_filter (α := α) (fun r ↦ r x y)
  have eB := card_linearExtensions_filter (α := α) (fun r ↦ r x z)
  have eAB := card_linearExtensions_filter (α := α) (fun r ↦ r x y ∧ r x z)
  rw [← eT] at bT
  rw [← eA] at bA
  rw [← eB] at bB
  rw [← eAB] at bAB
  simp only [filter_true] at bT
  refine limit_arith ?_ ?_ ?_ ?_ (card_mul_card_le_strictMaps m x y z)
    (card_linearExtensions_le _) (card_linearExtensions_le _) hK hC
  · convert bT.2
  · convert bAB.2
  · convert bA.1
  · convert bB.1
