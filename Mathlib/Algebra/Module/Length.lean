/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Module.Submodule.JordanHolder
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Artinian
import Mathlib.Order.KrullDimension

/-!

# Module Length

for an `R`-module `M`, if it has a composition series `0 ⋖ ... ⋖ M`, then its length is defined by
the length of this composition series, otherwise its length is said to be infinite. By Jordan-Hölder
theorem this is well defined.

Some authors also define the length of `M` to be the length of longest `N₀ < N₁ < ... < Nₖ`. In this
file, we show that two definitions are in fact equal.

-/

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M]

section defs

variable (R M)

/-- A module with finite length is a module with a composition series starting with 0 and ending
  with itself. -/
class FiniteLengthModule where
  /-- A finite length module admits a composition series `s`. -/
  compositionSeries : CompositionSeries (Submodule R M)
  /-- the leftest element is the 0 submodule -/
  head_eq : compositionSeries.head = ⊥
  /-- the rightest element is the whole thing -/
  last_eq : compositionSeries.last = ⊤

/-- A module with finite length is a module with a composition series starting with 0 and ending
  with itself. -/
class IsFiniteLengthModule : Prop where
  /-- A module with finite length is a module with a composition series starting with 0 and ending
  with itself. -/
  finite : Nonempty (FiniteLengthModule R M)

variable [∀ (M : Type _) [AddCommGroup M] [Module R M], Decidable $ IsFiniteLengthModule R M]


/-- the length of a module `M` is infinite if `M` does not have a composition series of the form
  `0 ⋖ M₁ ⋖ ... ⋖ Mₙ ⋖ M`, and is the length of its composition series. By Jordan-Hölder theorem,
  this definition is well defined for all tis composition series has the same length. -/
noncomputable def moduleLength : WithTop ℕ :=
  if h : IsFiniteLengthModule R M
  then h.finite.some.compositionSeries.length
  else ⊤

variable {R M}

lemma _root_.CompositionSeries.moduleLength_eq_length
    (s : CompositionSeries (Submodule R M)) (s0 : s.head = ⊥) (slast : s.last = ⊤) :
    moduleLength R M = s.length := by
  delta moduleLength
  split_ifs with h
  · refine WithTop.coe_eq_coe.mpr $ (CompositionSeries.jordan_holder _ _ ?_ ?_).length_eq
    · rw [show s.bot = _ from s0, show h.finite.some.compositionSeries.bot = _ from
        h.finite.some.head_eq]
    · rw [show s.top = _ from slast, show h.finite.some.compositionSeries.top = _ from
        h.finite.some.last_eq]
  · exact (h ⟨_, s0, slast⟩).elim

lemma moduleLength_lt_of_proper_submodule [h : FiniteLengthModule R M]
    (N : Submodule R M) (hN : N < ⊤) : moduleLength R N < moduleLength R M := by
  obtain ⟨x, x0, xlast, xlen⟩ :=
    h.compositionSeries.exists_compositionSeries_with_smaller_length_of_lt_top
    N hN h.head_eq h.last_eq
  rw [x.moduleLength_eq_length x0 xlast, h.compositionSeries.moduleLength_eq_length
    h.head_eq h.last_eq]
  exact WithTop.coe_lt_coe.mpr xlen

/-- transport a composition series across a linear equivalence -/
@[simps!]
def _root_.CompositionSeries.congr (s : CompositionSeries (Submodule R M))
    {M' : Type _} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    CompositionSeries (Submodule R M') :=
  s.map _ (Submodule.map e) $ λ x y (h : x ⋖ y) ↦ by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩; exact ⟨a, h.1.1 ha, rfl⟩
    · have H := h.1.2
      contrapose! H
      rintro b hb
      obtain ⟨a, ha, ha'⟩ := H $ show e b ∈ y.map e from ⟨b, hb, rfl⟩
      simp only [EmbeddingLike.apply_eq_iff_eq] at ha'
      rwa [← ha']
    · intro z hz r
      refine h.2 (c := Submodule.map e.symm z) ⟨λ a ha ↦ ⟨e a, hz.1 ⟨_, ha, rfl⟩, e.3 _⟩, ?_⟩
        ⟨?_, ?_⟩
      · obtain ⟨m, hm1, hm2⟩ := SetLike.not_le_iff_exists.mp hz.2
        obtain ⟨n, -, rfl⟩ := r.1 hm1
        contrapose! hm2
        specialize hm2 $ show n ∈ _ from ⟨e n, hm1, e.3 _⟩
        exact ⟨_, hm2, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb1, rfl⟩ := r.1 ha
        rwa [show e.symm (e b) = b from e.3 b]
      · have r' := r.2
        contrapose! r'
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb, rfl⟩ := r' ha
        rwa [show e (e.symm b) = b from e.4 _]

/-- finite length modules are preserved under linear isomorphisms -/
def finiteLengthModule_congr {M' : Type _} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') [h : FiniteLengthModule R M] : FiniteLengthModule R M' where
  compositionSeries := h.compositionSeries.congr e
  head_eq := by
    rw [CompositionSeries.congr, RelSeries.head, RelSeries.map]
    simp only [Function.comp_apply]
    rw [show h.compositionSeries 0 = _ from h.head_eq, Submodule.map_bot]
  last_eq := by
    rw [CompositionSeries.congr, RelSeries.last, RelSeries.map]
    simp only [Function.comp_apply]
    rw [show h.compositionSeries _ = _ from h.last_eq, Submodule.map_top, LinearMap.range_eq_top]
    exact e.toEquiv.surjective

lemma isFiniteLengthModule_congr {M' : Type _} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') [h : IsFiniteLengthModule R M] : IsFiniteLengthModule R M' where
  finite := ⟨finiteLengthModule_congr e (h := h.finite.some)⟩

lemma moduleLength_congr
    {M' : Type _} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    moduleLength R M = moduleLength R M' := by
  by_cases H : IsFiniteLengthModule R M
  · rw [H.finite.some.compositionSeries.moduleLength_eq_length,
      (finiteLengthModule_congr (h := H.finite.some) e).compositionSeries.moduleLength_eq_length]
    rfl
    · exact (finiteLengthModule_congr (h := H.finite.some) e).head_eq
    · exact (finiteLengthModule_congr (h := H.finite.some) e).last_eq
    · exact H.finite.some.head_eq
    · exact H.finite.some.last_eq
  · have H' : ¬ IsFiniteLengthModule R M'
    · contrapose! H; apply isFiniteLengthModule_congr e.symm
    delta moduleLength
    rw [dif_neg H, dif_neg H']

lemma moduleLength_strictMono [h : FiniteLengthModule R M]
    (N1 N2 : Submodule R M) (hN : N1 < N2) :
    moduleLength R N1 < moduleLength R N2 := by
  by_cases hN2 : N2 = ⊤
  · subst hN2
    rw [show moduleLength R (⊤ : Submodule R M) = moduleLength R M from
      (moduleLength_congr Submodule.topEquiv.symm).symm]
    exact moduleLength_lt_of_proper_submodule N1 hN
  · replace hN2 : N2 < ⊤
    · rwa [lt_top_iff_ne_top]
    obtain ⟨s2, s20, s2last, -⟩ :=
      h.compositionSeries.exists_compositionSeries_with_smaller_length_of_lt_top N2 hN2
        h.head_eq h.last_eq
    have lt' : LinearMap.range (Submodule.ofLe $ le_of_lt hN) < ⊤
    · obtain ⟨x, hx1, hx2⟩ := (SetLike.lt_iff_le_and_exists.mp hN).2
      rw [lt_top_iff_ne_top]
      intros r
      have mem1 : (⟨x, hx1⟩ : N2) ∈ (⊤ : Submodule R N2) := ⟨⟩
      rw [←r, LinearMap.mem_range] at mem1
      obtain ⟨⟨y, hy1⟩, hy2⟩ := mem1
      rw [Subtype.ext_iff, Subtype.coe_mk] at hy2
      simp only [Submodule.coe_ofLe] at hy2
      refine hx2 ?_
      rw [←hy2]
      exact hy1
    obtain ⟨s1, s10, s1last, s1_len⟩ := s2.exists_compositionSeries_with_smaller_length_of_lt_top
      (LinearMap.range (Submodule.ofLe $ le_of_lt hN)) lt' s20 s2last
    rw [s2.moduleLength_eq_length s20 s2last, show moduleLength R N1 =
      moduleLength R (LinearMap.range (Submodule.ofLe $ le_of_lt hN)) from ?_,
      s1.moduleLength_eq_length s10 s1last]
    · exact WithTop.coe_lt_coe.mpr s1_len
    · refine (moduleLength_congr ?_).symm
      rw [Submodule.range_ofLe]
      exact Submodule.comapSubtypeEquivOfLe (le_of_lt hN)

lemma IsFiniteLengthModule_iff_moduleLength_finite :
    IsFiniteLengthModule R M ↔ ∃ (n : ℕ), moduleLength R M = n := by
  fconstructor
  · rintro h
    delta moduleLength
    rw [dif_pos h]
    refine ⟨_, rfl⟩
  · contrapose!
    intro r
    delta moduleLength
    rw [dif_neg r]
    exact λ n ↦ by norm_num

noncomputable instance [h : FiniteLengthModule R M] (N : Submodule R M) :
    FiniteLengthModule R N where
  compositionSeries := h.compositionSeries.ofInterList N
  head_eq := h.compositionSeries.ofInterList_head_eq_bot_of_head_eq_bot N h.head_eq
  last_eq := h.compositionSeries.ofInterList_last_eq_top_of_last_eq_top N h.last_eq

instance [h : FiniteLengthModule R M] : IsFiniteLengthModule R M := ⟨⟨h⟩⟩

noncomputable instance (priority := 100) [h : IsFiniteLengthModule R M] : FiniteLengthModule R M :=
  h.finite.some

lemma moduleLength_eq_coe [h : FiniteLengthModule R M] :
    moduleLength R M = h.compositionSeries.length :=
  h.compositionSeries.moduleLength_eq_length h.head_eq h.last_eq

end defs

namespace LTSeries

private lemma lt_compositionSeries_length_aux
    (x : LTSeries (Submodule R M)) (hx : x.last = ⊤)
    (s : CompositionSeries (Submodule R M)) (s0 : s.head = ⊥) (slast : s.last = ⊤) :
    x.length ≤ s.length := by
  have : FiniteLengthModule R M := ⟨s, s0, slast⟩
  classical
  by_cases x_len : x.length = 0
  · rw [x_len]; norm_num
  replace x_len : 0 < x.length
  · contrapose! x_len; exact Nat.eq_zero_of_le_zero x_len
  have : ∀ (i : Fin x.length), moduleLength R (x i.castSucc) < moduleLength R (x i.succ)
  · intro i
    refine moduleLength_strictMono _ _ (x.strictMono $ Fin.castSucc_lt_succ _)
  have aux1 : ∀ (i : Fin x.length), i ≤ moduleLength R (x i.castSucc)
  · -- haveI : fact (0 < x.len) := ⟨x_len⟩,
    rintro ⟨i, hi⟩
    induction i with | zero => ?_ | succ i ih => ?_
    · simp only [Nat.zero_eq, WithTop.coe_zero, Fin.castSucc_mk, Fin.mk_zero, zero_le]
    · specialize this ⟨i, (lt_add_one _).trans hi⟩
      specialize ih ((lt_add_one _).trans hi)
      simp only [Fin.castSucc_mk, moduleLength_eq_coe] at ih this ⊢
      have ineq0 := WithTop.coe_lt_coe.mp $ lt_of_le_of_lt ih this
      refine WithTop.coe_le_coe.mpr ineq0
  specialize aux1 ⟨x.length - 1, Nat.sub_lt x_len $ by linarith⟩
  have aux2 := lt_of_le_of_lt aux1 (moduleLength_lt_of_proper_submodule _ ?_)
  pick_goal 2
  · rw [← hx]
    refine x.strictMono ?_
    convert Fin.castSucc_lt_succ _ using 1
    exact Fin.ext (Nat.succ_pred_eq_of_pos x_len).symm
  rw [s.moduleLength_eq_length s0 slast] at aux2
  replace aux2 : _ - 1 < s.length := WithTop.coe_lt_coe.mp aux2
  exact Nat.le_of_pred_lt aux2

lemma length_le_compositionSeries
    (x : LTSeries (Submodule R M))
    (s : CompositionSeries (Submodule R M)) (s0 : s.head = ⊥) (slast : s.last = ⊤) :
    x.length ≤ s.length := by
  by_cases H : x.last = ⊤
  · apply x.lt_compositionSeries_length_aux H s s0 slast
  · let x' : LTSeries _ := x.snoc ⊤ (lt_top_iff_ne_top.mpr H)
    refine le_trans (le_of_lt (lt_add_one _ : x.length < x'.length)) (?_ : x'.length ≤ _)
    refine x'.lt_compositionSeries_length_aux (RelSeries.snoc_last _ _ _) s s0 slast

end LTSeries

variable [∀ (M : Type _) [AddCommGroup M] [Module R M], Decidable $ IsFiniteLengthModule R M]

lemma moduleLength_eq_krullDim_Submodules [h : FiniteLengthModule R M] :
  moduleLength R M = krullDim (Submodule R M) :=
le_antisymm (le_iSup_iff.mpr $ λ m hm ↦ moduleLength_eq_coe (h := h) ▸
  hm (h.compositionSeries.OfLE $ λ _ _ h ↦ h.1)) $ iSup_le $ λ i ↦ by
    refine WithBot.coe_le_coe.mpr $ moduleLength_eq_coe (h := h) ▸ WithTop.coe_le_coe.mpr ?_
    exact i.length_le_compositionSeries _ h.head_eq h.last_eq

section Noetherian_and_Artinian

variable (R M)

lemma isNoetherian_of_finiteLength [h : FiniteLengthModule R M] :
    IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded]
  refine RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨λ a ↦ ?_⟩
  let p : LTSeries (Submodule R M) := LTSeries.mk (h.compositionSeries.length + 1)
    (λ x ↦ a x) λ i j h ↦ by rw [← gt_iff_lt]; erw [a.2]; exact h
  have : h.compositionSeries.length + 1 ≤ h.compositionSeries.length :=
    p.length_le_compositionSeries _ h.head_eq h.last_eq
  norm_num at this

lemma isArtinian_of_finiteLength [h : FiniteLengthModule R M] :
    IsArtinian R M where
  wellFounded_submodule_lt' := RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨λ a ↦ by
    let p : LTSeries (Submodule R M) := LTSeries.mk (h.compositionSeries.length + 1)
      (λ x ↦ a (h.compositionSeries.length + 1 - x))
      (λ i j (h : i.1 < j.1) ↦ by
        erw [a.2]
        exact Nat.sub_lt_sub_left (lt_of_lt_of_le h $ Nat.le_of_lt_succ j.2) h)
    have : h.compositionSeries.length + 1 ≤ h.compositionSeries.length :=
      p.length_le_compositionSeries _ h.head_eq h.last_eq
    norm_num at this⟩

end Noetherian_and_Artinian
