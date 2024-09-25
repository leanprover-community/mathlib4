/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.Morphism

/-!
# Topological entropy of products
The topological entropy of product is the sum of the topological entropies.

TODO: Get the less easy bounds. Need some work on EReal :
-> something like iSup (f + a) = (iSup f) + a, and maybe, more generally,
  iSup (f + g) ≤ iSup f + iSup g.
-> there's maybe something clever to do using limsup + liminf ≤ limsup and so on to get lower bounds
on coverEntropySupUni, and so on. May be especially interesting for arbitrary products (get weaker
hypotheses for various formulae)

TODO: Extend it to finite/arbitrary products.
-/

namespace Dynamics

open Prod Set Uniformity UniformSpace

variable {X Y : Type*}

/-! ### Map swap -/

lemma coverEntropyInf_prod_swap [UniformSpace X] [UniformSpace Y] (S : X → X) (T : Y → Y)
    (F : Set X) (G : Set Y) :
    coverEntropyInf (map T S) (G ×ˢ F) = coverEntropyInf (map S T) (F ×ˢ G) := by
  rw [← Set.image_swap_prod F G,
    coverEntropyInf_image instUniformSpaceProd (Function.Semiconj.swap_map S T) (F ×ˢ G)]
  congr
  rw [← UniformEquiv.coe_prodComm]
  exact UniformEquiv.comap_eq (@UniformEquiv.prodComm X Y _ _)

lemma coverEntropy_prod_swap [UniformSpace X] [UniformSpace Y] (S : X → X) (T : Y → Y)
    (F : Set X) (G : Set Y) :
    coverEntropy (map T S) (G ×ˢ F) = coverEntropy (map S T) (F ×ˢ G) := by
  rw [← Set.image_swap_prod F G,
    coverEntropy_image instUniformSpaceProd (Function.Semiconj.swap_map S T) (F ×ˢ G)]
  congr
  rw [← UniformEquiv.coe_prodComm]
  exact UniformEquiv.comap_eq (@UniformEquiv.prodComm X Y _ _)

/-! ### Entropy of products -/

lemma isDynCoverOf_prod {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y} {U : Set (X × X)}
    {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y} (hS : IsDynCoverOf S F U n s)
    (hT : IsDynCoverOf T G V n t) :
    IsDynCoverOf (map S T) (F ×ˢ G) (entourageProd U V) n (s ×ˢ t) := by
  rw [IsDynCoverOf, dynEntourage_entourageProd S T U V n]
  intro p p_FG
  specialize hS p_FG.1
  specialize hT p_FG.2
  simp only [mem_iUnion, exists_prop] at hS hT
  rcases hS with ⟨x, x_s, p_x⟩
  rcases hT with ⟨y, y_t, p_y⟩
  rw [Set.mem_iUnion₂]
  use (x, y), Set.mem_prod.2 ⟨x_s, y_t⟩
  simp only [ball_entourageProd, mem_prod]
  exact ⟨p_x, p_y⟩

lemma isDynNetOf_prod {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y} {U : Set (X × X)}
    {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y} (hS : IsDynNetOf S F U n s)
    (hT : IsDynNetOf T G V n t) :
    IsDynNetOf (map S T) (F ×ˢ G) (entourageProd U V) n (s ×ˢ t) := by
  apply And.intro (Set.prod_mono hS.1 hT.1)
  rw [dynEntourage_entourageProd S T U V n]
  simp only [ball_entourageProd]
  exact PairwiseDisjoint.prod hS.2 hT.2

lemma coverMincard_prod_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) (U : Set (X × X))
    (V : Set (Y × Y)) (n : ℕ) :
    coverMincard (map S T) (F ×ˢ G) (entourageProd U V) n ≤
    coverMincard S F U n * coverMincard T G V n := by
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · simp
  rcases G.eq_empty_or_nonempty with rfl | G_nemp
  · simp
  rcases eq_top_or_lt_top (coverMincard S F U n) with (h₁ | h₁)
  · rw [h₁]
    apply le_top.trans_eq (Eq.symm _)
    rw [WithTop.top_mul]
    exact ENat.one_le_iff_ne_zero.1 ((one_le_coverMincard_iff T G V n).2 G_nemp)
  rcases eq_top_or_lt_top (coverMincard T G V n) with (h₂ | h₂)
  · rw [h₂]
    apply le_top.trans_eq (Eq.symm _)
    rw [WithTop.mul_top]
    exact ENat.one_le_iff_ne_zero.1 ((one_le_coverMincard_iff S F U n).2 F_nemp)
  rcases (coverMincard_finite_iff S F U n).1 h₁ with ⟨s, s_cover, s_card⟩
  rcases (coverMincard_finite_iff T G V n).1 h₂ with ⟨t, t_cover, t_card⟩
  rw [← s_card, ← t_card, ← Nat.cast_mul, ← Finset.card_product s t]
  apply IsDynCoverOf.coverMincard_le_card
  rw [Finset.coe_product]
  exact isDynCoverOf_prod s_cover t_cover

lemma le_netMaxcard_prod (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) (U : Set (X × X))
    (V : Set (Y × Y)) (n : ℕ) :
    netMaxcard S F U n * netMaxcard T G V n
    ≤ netMaxcard (map S T) (F ×ˢ G) (entourageProd U V) n := by
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · simp
  rcases G.eq_empty_or_nonempty with rfl | G_nemp
  · simp
  rcases eq_top_or_lt_top (netMaxcard S F U n) with h₁ | h₁
  · refine le_top.trans_eq ((netMaxcard_infinite_iff _ _ _ n).2 fun k ↦ ?_).symm
    rw [netMaxcard, iSup_subtype', iSup_eq_top] at h₁
    specialize h₁ k (ENat.coe_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h₁
    rcases h₁ with ⟨s, s_net, s_card⟩
    rcases G_nemp with ⟨y, y_G⟩
    use s ×ˢ ({y} : Finset Y)
    rw [Finset.coe_product]
    apply And.intro (isDynNetOf_prod s_net _) _
    · rw [Finset.coe_singleton]
      exact isDynNetOf_singleton T V n y_G
    · rw [Finset.card_product s ({y} : Finset Y), Finset.card_singleton y, mul_one]
      exact s_card.le
  rcases eq_top_or_lt_top (netMaxcard T G V n) with h₂ | h₂
  · refine le_top.trans_eq ((netMaxcard_infinite_iff _ _ _ n).2 fun k ↦ ?_).symm
    rw [netMaxcard, iSup_subtype', iSup_eq_top] at h₂
    specialize h₂ k (ENat.coe_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h₂
    rcases h₂ with ⟨t, t_net, t_card⟩
    rcases F_nemp with ⟨x, x_F⟩
    use ({x} : Finset X) ×ˢ t
    rw [Finset.coe_product]
    apply And.intro (isDynNetOf_prod _ t_net) _
    · rw [Finset.coe_singleton]
      exact isDynNetOf_singleton S U n x_F
    · rw [Finset.card_product ({x} : Finset X) t, Finset.card_singleton x, one_mul]
      exact t_card.le
  rcases (netMaxcard_finite_iff S F U n).1 h₁ with ⟨s, s_cover, s_card⟩
  rcases (netMaxcard_finite_iff T G V n).1 h₂ with ⟨t, t_cover, t_card⟩
  rw [← s_card, ← t_card, ← Nat.cast_mul, ← Finset.card_product s t]
  apply IsDynNetOf.card_le_netMaxcard
  rw [Finset.coe_product]
  exact isDynNetOf_prod s_cover t_cover

open ENNReal EReal Filter

lemma coverEntropyEnt_prod_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    coverEntropyEnt (map S T) (F ×ˢ G) (entourageProd U V)
    ≤ (coverEntropyEnt S F U) + (coverEntropyEnt T G V) := by
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · simp
  rcases G.eq_empty_or_nonempty with rfl | G_nemp
  · simp
  apply le_trans _ <| limsup_add_le_add_limsup
    (Or.inl <| ne_of_gt <| bot_lt_zero.trans_le (coverEntropyEnt_nonneg S F_nemp U))
    (Or.inr <| ne_of_gt <| bot_lt_zero.trans_le (coverEntropyEnt_nonneg T G_nemp V))
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  simp only [Pi.add_apply]
  rw [← div_right_distrib_of_nonneg (log_coverMincard_nonneg S F_nemp U n)
    (log_coverMincard_nonneg T G_nemp V n), ← ENNReal.log_mul_add, ← ENat.toENNReal_mul]
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_le.2 (coverMincard_prod_le S T F G U V n))

lemma le_netEntropyInfEnt_prod (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    (netEntropyInfEnt S F U) + (netEntropyInfEnt T G V)
    ≤ netEntropyInfEnt (map S T) (F ×ˢ G) (entourageProd U V) := by
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · simp
  rcases G.eq_empty_or_nonempty with rfl | G_nemp
  · simp
  refine add_liminf_le_liminf_add.trans ((liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_))
  simp only [Pi.add_apply]
  rw [← div_right_distrib_of_nonneg (log_netMaxcard_nonneg S F_nemp U n)
    (log_netMaxcard_nonneg T G_nemp V n), ← log_mul_add, ← ENat.toENNReal_mul]
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_le.2 (le_netMaxcard_prod S T F G U V n))

variable [UniformSpace X] [UniformSpace Y]

lemma coverEntropy_prod_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) :
    coverEntropy (map S T) (F ×ˢ G) ≤ (coverEntropy S F) + (coverEntropy T G) := by
  refine iSup₂_le (fun W W_uni ↦ ?_)
  rcases entourageProd_subset W_uni with ⟨U, U_uni, V, V_uni, UV_W⟩
  apply (coverEntropyEnt_antitone (map S T) (F ×ˢ G) UV_W).trans
  apply (coverEntropyEnt_prod_le S T F G U V).trans
  apply add_le_add (coverEntropyEnt_le_coverEntropy S F U_uni)
  exact coverEntropyEnt_le_coverEntropy T G V_uni

end Dynamics

#lint
