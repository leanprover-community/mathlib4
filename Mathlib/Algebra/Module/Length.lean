/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Module.Submodule.JordanHolder
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Artinian
import Mathlib.Order.KrullDimension
import Mathlib.Algebra.BigOperators.Order

/-!

# Module Length

for an `R`-module `M`, if it has a composition series `0 ⋖ ... ⋖ M`, then its length is defined by
the length of this composition series, otherwise its length is said to be infinite. By Jordan-Hölder
theorem this is well defined.

Some authors also define the length of `M` to be the length of longest `N₀ < N₁ < ... < Nₖ`. In this
file, we show that two definitions are in fact equal.

-/

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

open Classical BigOperators

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

instance : FiniteLengthModule R PUnit where
  compositionSeries := RelSeries.singleton _ ⊤
  head_eq := by
    ext ⟨⟩
    change PUnit.unit ∈ ⊤ ↔ PUnit.unit ∈ ⊥
    simp
  last_eq := rfl

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

noncomputable instance [h : FiniteLengthModule R M] (N : Submodule R M) :
    FiniteLengthModule R N where
  compositionSeries := h.compositionSeries.ofInterList N
  head_eq := h.compositionSeries.ofInterList_head_eq_bot_of_head_eq_bot N h.head_eq
  last_eq := h.compositionSeries.ofInterList_last_eq_top_of_last_eq_top N h.last_eq

instance [h : FiniteLengthModule R M] : IsFiniteLengthModule R M := ⟨⟨h⟩⟩

noncomputable instance (priority := 100) [h : IsFiniteLengthModule R M] : FiniteLengthModule R M :=
  h.finite.some

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

lemma moduleLength_punit : moduleLength R PUnit = 0 := by
  let i : FiniteLengthModule R PUnit := inferInstance
  rw [i.compositionSeries.moduleLength_eq_length i.head_eq i.last_eq]
  rfl

lemma moduleLength_lt_of_proper_submodule [h : FiniteLengthModule R M]
    (N : Submodule R M) (hN : N < ⊤) : moduleLength R N < moduleLength R M := by
  obtain ⟨x, x0, xlast, xlen⟩ :=
    h.compositionSeries.exists_compositionSeries_with_smaller_length_of_lt_top
    N hN h.head_eq h.last_eq
  rw [x.moduleLength_eq_length x0 xlast, h.compositionSeries.moduleLength_eq_length
    h.head_eq h.last_eq]
  exact WithTop.coe_lt_coe.mpr xlen

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
    {M' : Type*} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
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
  · replace hN2 : N2 < ⊤ := lt_top_iff_ne_top |>.mpr hN2
    obtain ⟨s2, s20, s2last, -⟩ :=
      h.compositionSeries.exists_compositionSeries_with_smaller_length_of_lt_top N2 hN2
        h.head_eq h.last_eq
    have lt' : LinearMap.range (Submodule.inclusion $ le_of_lt hN) < ⊤
    · obtain ⟨x, hx1, hx2⟩ := (SetLike.lt_iff_le_and_exists.mp hN).2
      rw [lt_top_iff_ne_top]
      intros r
      have mem1 : (⟨x, hx1⟩ : N2) ∈ (⊤ : Submodule R N2) := ⟨⟩
      rw [← r, LinearMap.mem_range] at mem1
      obtain ⟨⟨y, hy1⟩, hy2⟩ := mem1
      rw [Subtype.ext_iff, Subtype.coe_mk] at hy2
      simp only [Submodule.coe_inclusion] at hy2
      refine hx2 ?_
      rw [← hy2]
      exact hy1
    obtain ⟨s1, s10, s1last, s1_len⟩ := s2.exists_compositionSeries_with_smaller_length_of_lt_top
      (LinearMap.range (Submodule.inclusion $ le_of_lt hN)) lt' s20 s2last
    rw [s2.moduleLength_eq_length s20 s2last, show moduleLength R N1 =
      moduleLength R (LinearMap.range (Submodule.inclusion $ le_of_lt hN)) from ?_,
      s1.moduleLength_eq_length s10 s1last]
    · exact WithTop.coe_lt_coe.mpr s1_len
    · refine (moduleLength_congr ?_).symm
      rw [Submodule.range_inclusion]
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

lemma IsFiniteLengthModule_iff_moduleLength_finite' :
    IsFiniteLengthModule R M ↔ moduleLength R M < ⊤ := by
  rw [IsFiniteLengthModule_iff_moduleLength_finite]
  fconstructor
  · rintro ⟨n, hn⟩
    rw [hn]
    exact WithTop.coe_lt_top _
  · intro h
    rw [WithTop.lt_iff_exists_coe] at h
    obtain ⟨n, hn, -⟩ := h
    exact ⟨n, hn⟩

lemma moduleLength_eq_coe [h : FiniteLengthModule R M] :
    moduleLength R M = h.compositionSeries.length :=
  h.compositionSeries.moduleLength_eq_length h.head_eq h.last_eq

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
  · rintro ⟨i, hi⟩
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

lemma moduleLength_eq_krullDim_Submodules [h : FiniteLengthModule R M] :
    moduleLength R M = krullDim (Submodule R M) :=
le_antisymm
  (le_iSup_iff.mpr fun m hm ↦ moduleLength_eq_coe (h := h) ▸ hm
    (h.compositionSeries.ofLE fun _ _ h ↦ h.1))
  (iSup_le fun i ↦ by
    refine WithBot.coe_le_coe.mpr $ moduleLength_eq_coe (h := h) ▸ WithTop.coe_le_coe.mpr ?_
    exact i.length_le_compositionSeries _ h.head_eq h.last_eq)

section Noetherian_and_Artinian

variable (R M)

instance isNoetherian_of_finiteLength [h : FiniteLengthModule R M] :
    IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded]
  refine RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨λ a ↦ ?_⟩
  let p : LTSeries (Submodule R M) := LTSeries.mk (h.compositionSeries.length + 1)
    (a ·) fun i j h ↦ by rw [← gt_iff_lt]; erw [a.2]; exact h
  have : h.compositionSeries.length + 1 ≤ h.compositionSeries.length :=
    p.length_le_compositionSeries _ h.head_eq h.last_eq
  norm_num at this

instance isArtinian_of_finiteLength [h : FiniteLengthModule R M] :
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

variable {R M}
variable [IsArtinian R M] (N : Submodule R M)

/-- for an artinian `R`-module `M`, there is a well defined successor function on its submodules.
`N ↦ N'` such that `N ⋖ N'`-/
noncomputable def _root_.Submodule.next : Submodule R M :=
let wf : WellFounded ((. < .) : Submodule R M → Submodule R M → Prop) :=
  (inferInstance : IsArtinian R M).1
wf.succ N

lemma _root_.Submodule.exists_of_ne_top (ne_top : N ≠ ⊤) : ∃ (x : Submodule R M), N < x := by
  obtain ⟨m, _, nm⟩ := SetLike.exists_of_lt (Ne.lt_top ne_top : N < ⊤)
  refine ⟨N ⊔ R ∙ m, SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, ⟨m, ?_, nm⟩⟩⟩
  exact (le_sup_right : (R ∙ m) ≤ _) (Submodule.mem_span_singleton_self _)

lemma _root_.Submodule.le_next : N ≤ N.next := by
  delta Submodule.next WellFounded.succ
  by_cases H : ∃ _, _
  · exact le_of_lt (WellFounded.lt_succ _ H)
  · dsimp only
    split_ifs with h
    · exact (H h).elim
    · rfl

lemma _root_.Submodule.lt_next_of_ne_top (ne_top : N ≠ ⊤) : N < N.next :=
  WellFounded.lt_succ _ (N.exists_of_ne_top ne_top)

lemma _root_.Submodule.eq_top_of_eq_next (eq_next : N = N.next) : N = ⊤ := by
  contrapose! eq_next
  exact ne_of_lt (N.lt_next_of_ne_top eq_next)

lemma _root_.Submodule.covby_next_of_ne_top (ne_top : N ≠ ⊤) : N ⋖ N.next := by
  classical
  rw [covby_iff_lt_and_eq_or_eq]
  refine ⟨N.lt_next_of_ne_top ne_top, λ x hx1 hx2 ↦ ?_⟩
  dsimp only [Submodule.next] at hx2 ⊢
  -- generalize_proofs h at hx2
  rw [le_iff_lt_or_eq] at hx2
  rcases hx2 with (hx2|rfl)
  · left
    refine le_antisymm ?_ hx1
    delta WellFounded.succ at hx2
    rw [dif_pos (N.exists_of_ne_top ne_top)] at hx2
    have : ¬ _ < _ := not_imp_not.mpr (WellFounded.not_lt_min _ _ _) (not_not.mpr hx2)
    rw [SetLike.lt_iff_le_and_exists, not_and_or] at this
    push_neg at this
    exact this.resolve_left (not_not.mpr hx1)
  · right; rfl

variable (R M)

/-- the `n`-th largest submodule, counting from `0`-th largest being `⊥`
  this is implemented as an order homomorphism -/
@[simps]
noncomputable def nthSubmodule : ℕ →o Submodule R M where
  toFun := λ n ↦ Submodule.next^[n] ⊥
  monotone' := λ m n h ↦ by
    apply Function.monotone_iterate_of_id_le
    · intro x; apply Submodule.le_next
    · assumption

lemma nthSubmodule_eventually_stabilize_of_isNoetherian [IsNoetherian R M] :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → nthSubmodule R M n = nthSubmodule R M m :=
(monotone_stabilizes_iff_noetherian).mpr (inferInstance : IsNoetherian R M) $
  nthSubmodule R M

variable  [IsNoetherian R M]

/-- the index of `⊤` appearing in `nthSubmodule`-/
noncomputable def indexOfTopSubmodule : ℕ :=
  Nat.find (nthSubmodule_eventually_stabilize_of_isNoetherian R M)

lemma nthSubmodule_stabilize_after_indexOfTopSubmodule_aux :
    ∀ (m : ℕ), indexOfTopSubmodule R M ≤ m →
      nthSubmodule R M (indexOfTopSubmodule R M) = nthSubmodule R M m :=
  Nat.find_spec (nthSubmodule_eventually_stabilize_of_isNoetherian R M)

lemma nthSubmodule_indexOfTopSubmodule_eq_top :
    nthSubmodule R M (indexOfTopSubmodule R M) = ⊤ := by
  apply Submodule.eq_top_of_eq_next
  rw [show (nthSubmodule R M (indexOfTopSubmodule R M)).next =
    (nthSubmodule R M (indexOfTopSubmodule R M + 1)) from _]
  · exact nthSubmodule_stabilize_after_indexOfTopSubmodule_aux R M _ $ le_of_lt $ lt_add_one _
  · rw [nthSubmodule_coe, nthSubmodule_coe, Function.iterate_succ', Function.comp_apply]

lemma nthSubmodule_stabilize_after_indexOfTopSubmodule :
    ∀ (m : ℕ), indexOfTopSubmodule R M ≤ m → nthSubmodule R M m = ⊤ := by
  intro m hm
  rw [← nthSubmodule_indexOfTopSubmodule_eq_top]
  symm
  apply nthSubmodule_stabilize_after_indexOfTopSubmodule_aux _ _ _ hm

lemma ne_top_of_lt_indexOfTopSubmodule (n : ℕ) (lt : n < indexOfTopSubmodule R M) :
    nthSubmodule R M n ≠ ⊤ := by
  have H := (Nat.lt_find_iff (nthSubmodule_eventually_stabilize_of_isNoetherian R M) n).mp lt n
    (le_refl _)
  push_neg at H
  obtain ⟨m, hm1, hm2⟩ := H
  intro rid
  have ineq1 : nthSubmodule R M n < nthSubmodule R M m
  · exact (le_iff_lt_or_eq.mp ((nthSubmodule R M).2 hm1)).resolve_right hm2
  rw [rid] at ineq1
  exact not_top_lt ineq1

/-- If an `R`-module `M` is both artinian and noetherian, then it has a composition series, hence a
module of finite length. -/
@[simps]
noncomputable def _root_.CompositionSeries.ofIsArtinianOfIsNoetherian :
    CompositionSeries (Submodule R M) where
  length := indexOfTopSubmodule R M
  toFun := nthSubmodule R M ∘ Fin.val
  step := λ i ↦ by
    simpa only [Function.comp_apply, Fin.coe_castSucc, nthSubmodule_coe, Fin.val_succ,
      Function.iterate_succ'] using Submodule.covby_next_of_ne_top _
      (ne_top_of_lt_indexOfTopSubmodule R M _ i.2)

lemma _root_.CompositionSeries.ofIsArtinianOfIsNoetherian_head_eq :
    (CompositionSeries.ofIsArtinianOfIsNoetherian R M).head = ⊥ := by
  simp only [RelSeries.head, CompositionSeries.ofIsArtinianOfIsNoetherian_toFun,
    Function.comp_apply, Fin.val_zero, nthSubmodule_coe, Function.iterate_zero, id_eq]

lemma _root_.CompositionSeries.ofIsArtinianOfIsNoetherian_last_eq :
    (CompositionSeries.ofIsArtinianOfIsNoetherian R M).last = ⊤ := by
  simpa only [RelSeries.last, CompositionSeries.ofIsArtinianOfIsNoetherian_length,
    CompositionSeries.ofIsArtinianOfIsNoetherian_toFun, Function.comp_apply, Fin.val_last,
    nthSubmodule_coe] using nthSubmodule_indexOfTopSubmodule_eq_top R M

noncomputable instance FiniteLengthModule.of_noetherian_of_artinian
    [IsArtinian R M] [IsNoetherian R M] : FiniteLengthModule R M where
  compositionSeries := _
  head_eq := CompositionSeries.ofIsArtinianOfIsNoetherian_head_eq R M
  last_eq := CompositionSeries.ofIsArtinianOfIsNoetherian_last_eq R M

instance [IsArtinian R M] [IsNoetherian R M] : IsFiniteLengthModule R M where
  finite := by
    classical
    exact ⟨_, CompositionSeries.ofIsArtinianOfIsNoetherian_head_eq R M,
      CompositionSeries.ofIsArtinianOfIsNoetherian_last_eq R M⟩

end Noetherian_and_Artinian

section additive

section submodule_quotient

variable {N : Submodule R M} (c : CompositionSeries (Submodule R (M ⧸ N)))
variable (d : CompositionSeries (Submodule R N))

/--
Give a composition series `p₀ ⋖ p₁ ⋖ ... ⋖  pₙ` of `M ⧸ N`, we can lift it to a composition series
of `M`.
-/
@[simps]
def CompositionSeries.liftQuotient : CompositionSeries (Submodule R M) where
  length := c.length
  toFun i := N.comapMkQRelIso (c i)
  step i := show (N.comapMkQRelIso (c _)).1 ⋖ (N.comapMkQRelIso (c _)).1 by
    obtain ⟨lt, H⟩ := (c.step i)
    refine ⟨N.comapMkQRelIso.lt_iff_lt.mpr lt, ?_⟩
    intro p h
    have p_le : N ≤ p
    · simp only [Submodule.comapMkQRelIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] at h
      intro m hm
      refine h.1 ?_
      simp only [Submodule.comap_coe, Set.mem_preimage, Submodule.mkQ_apply, SetLike.mem_coe]
      convert Submodule.zero_mem _
      simpa only [Submodule.Quotient.mk_eq_zero]
    specialize @H (N.comapMkQRelIso.symm ⟨p, p_le⟩) (by
      have := N.comapMkQRelIso.symm.strictMono
        (Subtype.mk_lt_mk.mpr h : N.comapMkQRelIso (c _) < ⟨p, p_le⟩)
      convert this using 1
      change _ = Submodule.map _ (Submodule.comap _ _)
      rw [Submodule.map_comap_eq_of_surjective]
      exact Submodule.mkQ_surjective N)
    contrapose! H
    convert N.comapMkQRelIso.symm.strictMono
      (Subtype.mk_lt_mk.mpr H : ⟨p, p_le⟩ < N.comapMkQRelIso (c _)) using 1
    change _ = Submodule.map _ (Submodule.comap _ _)
    rw [Submodule.map_comap_eq_of_surjective]
    exact Submodule.mkQ_surjective N

lemma CompositionSeries.liftQuotient_head :
  CompositionSeries.bot c.liftQuotient = N.comapMkQRelIso c.bot := rfl

lemma CompositionSeries.liftQuotient_last :
    CompositionSeries.top c.liftQuotient = N.comapMkQRelIso c.top := rfl

def CompositionSeries.liftSubmodule : CompositionSeries (Submodule R M) where
  length := d.length
  toFun i := Submodule.MapSubtype.relIso N (d i)
  step i := show Submodule.map _ _ ⋖ Submodule.map _ _ by
    obtain ⟨lt, H⟩ := d.step i
    refine ⟨Submodule.MapSubtype.relIso N |>.lt_iff_lt.mpr lt, ?_⟩
    contrapose! H
    obtain ⟨p, hp1, hp2⟩ := H
    have hp3 : p ≤ N
    · intro x hx
      have := hp2.1 hx
      simp only [Submodule.map_coe, Submodule.coeSubtype, Set.mem_image, SetLike.mem_coe,
        Subtype.exists, exists_and_right, exists_eq_right] at this
      obtain ⟨hx', -⟩ := this
      exact hx'
    have hp1' : Submodule.MapSubtype.relIso N (d i.castSucc) < ⟨p, hp3⟩ := hp1
    have hp2' : ⟨p, hp3⟩ < Submodule.MapSubtype.relIso N (d i.succ) := hp2
    have hp1' := Submodule.MapSubtype.relIso N |>.symm |>.lt_iff_lt |>.mpr hp1'
    have hp2' := Submodule.MapSubtype.relIso N |>.symm |>.lt_iff_lt |>.mpr hp2'
    simp only [OrderIso.symm_apply_apply] at hp1' hp2'
    exact ⟨Submodule.MapSubtype.relIso N |>.symm ⟨p, hp3⟩, hp1', hp2'⟩

lemma CompositionSeries.liftSubmodule_head :
    CompositionSeries.bot d.liftSubmodule = (Submodule.map N.subtype d.bot) := rfl

lemma CompositionSeries.liftSubmodule_last :
    CompositionSeries.top d.liftSubmodule = (Submodule.map N.subtype d.top) := rfl

variable (R M) in
noncomputable def FiniteLengthModule.submodule [finLen : FiniteLengthModule R M] :
    FiniteLengthModule R N where
  compositionSeries := finLen.compositionSeries.ofInterList N
  head_eq := finLen.compositionSeries.ofInterList_head_eq_bot_of_head_eq_bot N finLen.head_eq
  last_eq := finLen.compositionSeries.ofInterList_last_eq_top_of_last_eq_top N finLen.last_eq

variable (N) in
noncomputable def FiniteLengthModule.quotient [finLen : FiniteLengthModule R M] :
    FiniteLengthModule R (M ⧸ N) := by
  classical
  exact FiniteLengthModule.of_noetherian_of_artinian R (M ⧸ N)

variable (N) in
def FiniteLengthModule.of_quotient_of_submodule
      [quotFin : FiniteLengthModule R (M ⧸ N)] [subFin : FiniteLengthModule R N] :
    FiniteLengthModule R M where
  compositionSeries :=
    let c1 := quotFin.compositionSeries.liftQuotient
    let c2 := subFin.compositionSeries.liftSubmodule
    c2.append c1  <| by
      rw [CompositionSeries.liftQuotient_head, CompositionSeries.liftSubmodule_last]
      ext m
      simp only [Submodule.mem_map, Submodule.coeSubtype, Subtype.exists, exists_and_right,
        exists_eq_right, Submodule.comapMkQRelIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
        Submodule.mem_comap, Submodule.mkQ_apply]
      set x : Submodule R N := CompositionSeries.top compositionSeries
      set y : Submodule R (M ⧸ N) := CompositionSeries.bot compositionSeries
      have x_eq := show x = ⊤ from subFin.last_eq
      have y_eq := show y = ⊥ from quotFin.head_eq
      rw [x_eq, y_eq]
      simp only [Submodule.mem_top, exists_prop, and_true, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero]
  head_eq := by
    simp only [CompositionSeries.append, RelSeries.combine_head]
    show Submodule.map _ _ = ⊥
    rw [show RelSeries.toFun compositionSeries 0 = ⊥ from subFin.head_eq, Submodule.map_bot]
  last_eq := by
    simp only [CompositionSeries.append, RelSeries.combine_last]
    show Submodule.comap _ _ = ⊤
    erw [show RelSeries.toFun compositionSeries (Fin.last _) = ⊤ from quotFin.last_eq,
      Submodule.comap_top]

variable (N) in
lemma moduleLength.eq_length_submodule_add_length_quotient :
    moduleLength R M = moduleLength R N + moduleLength R (M ⧸ N) := by
  by_cases finiteLength : IsFiniteLengthModule R M
  · haveI inst1 : FiniteLengthModule R M := Classical.choice finiteLength.finite
    let finiteLength_submodule : FiniteLengthModule R N := FiniteLengthModule.submodule R M
    let finiteLength_quotient : FiniteLengthModule R (M ⧸ N) := FiniteLengthModule.quotient N
    let finiteLength : FiniteLengthModule R M :=
      FiniteLengthModule.of_quotient_of_submodule (N := N)
    rw [finiteLength.compositionSeries.moduleLength_eq_length
          finiteLength.head_eq finiteLength.last_eq,
      finiteLength_quotient.compositionSeries.moduleLength_eq_length
          finiteLength_quotient.head_eq finiteLength_quotient.last_eq,
      finiteLength_submodule.compositionSeries.moduleLength_eq_length
          finiteLength_submodule.head_eq finiteLength_submodule.last_eq]
    norm_cast
  · conv_lhs => delta moduleLength
    rw [dif_neg finiteLength]
    have inst1 : ¬ IsFiniteLengthModule R N ∨ ¬ IsFiniteLengthModule R (M ⧸ N)
    · contrapose! finiteLength
      haveI i1 := Classical.choice finiteLength.1.finite
      haveI i2 := Classical.choice finiteLength.2.finite
      exact ⟨⟨FiniteLengthModule.of_quotient_of_submodule (N := N)⟩⟩
    rcases inst1 with inst1 | inst1
    · conv_rhs => lhs; delta moduleLength
      rw [dif_neg inst1]
      rfl
    · conv_rhs => rhs; delta moduleLength
      rw [dif_neg inst1, add_comm]
      rfl

end submodule_quotient

section lt_series

variable (x : LTSeries (Submodule R M))

/-- if `x ≤ y` are both `R`-submodule of `M`, we can mathematically form their quotient but type
theoretically more complicated, so introduce a definition to use a notation. -/
private def quot {M : Type _} [AddCommGroup M] [Module R M] (x y : Submodule R M) : Type _ :=
  x ⧸ (Submodule.comap x.subtype y)
local infix:80 "⧸ₛ" => quot

instance {M : Type _} [AddCommGroup M] [Module R M] (x y : Submodule R M) :
    AddCommGroup (x ⧸ₛ y) := by
  delta quot; infer_instance

instance {M : Type _} [AddCommGroup M] [Module R M] (x y : Submodule R M) :
    Module R (x ⧸ₛ y) := by
  delta quot; infer_instance

abbrev LTSeries.cqf (i : Fin (x.length + 1)) :=
  x i ⧸ₛ x.head

def LTSeries.cqfToSucc (i : Fin x.length) :
    x.cqf i.castSucc →ₗ[R] x.cqf i.succ :=
  Submodule.mapQ _ _ (Submodule.inclusion <| le_of_lt <| x.step _) <| by
    rw [← Submodule.comap_comp]
    intro m hm
    simpa using hm

noncomputable def LTSeries.rangeCQFToSucc (i : Fin x.length) :
    LinearMap.range (x.cqfToSucc i) ≃ₗ[R] x.cqf i.castSucc :=
  LinearEquiv.symm <| LinearEquiv.ofInjective _ fun a b h ↦ by
    induction' a using Quotient.inductionOn' with a
    induction' b using Quotient.inductionOn' with b
    erw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
    rw [Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.eq]
    simpa only using h


noncomputable def LTSeries.cqfZeroEquiv : x.cqf 0 ≃ₗ[R] PUnit := by
  refine PUnit.linearEquivOfUnique (uniq := ?_)
  suffices H : Nonempty (Unique _)
  · exact Classical.choice H
  erw [Submodule.unique_quotient_iff_eq_top]
  simp only [Submodule.comap_subtype_eq_top]
  rfl

abbrev LTSeries.qf (i : Fin x.length) := x i.succ ⧸ₛ x i.castSucc

/--
xᵢ₊₁ ⧸ xᵢ = (xᵢ₊₁ ⧸ x₀) ⧸ (xᵢ ⧸ x₀)

-/
noncomputable def LTSeries.cdfSuccEquiv (i : Fin x.length) :
    x.qf i ≃ₗ[R]
    x.cqf i.succ ⧸ (Submodule.map (x.cqfToSucc i) ⊤ : Submodule R (x.cqf i.succ)) := by
  let x_i : Submodule R (x i.succ) :=
    Submodule.map (Submodule.inclusion <| le_of_lt <| x.step _ : x i.castSucc →ₗ[R] x i.succ) ⊤
  let x_0 : Submodule R (x i.succ) :=
    Submodule.map (Submodule.inclusion <| x.monotone <| Fin.zero_le _ : x.head →ₗ[R] x i.succ) ⊤

  let e := @Submodule.quotientQuotientEquivQuotient (R := R) (M := x i.succ)
    (T := x_i) (S := x_0) (fun m hm ↦ by
      simp only [Submodule.map_top, LinearMap.mem_range, Subtype.exists] at hm ⊢
      rcases hm with ⟨n, h1, rfl⟩
      exact ⟨n, x.monotone (Fin.zero_le _) h1, rfl⟩)
  refine ?_ ≪≫ₗ e.symm ≪≫ₗ ?_
  · refine Submodule.Quotient.equiv _ _ (LinearEquiv.refl R _) ?_
    ext m
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coeSubtype, LinearEquiv.refl_apply,
      exists_eq_right, Submodule.map_top, LinearMap.mem_range, Subtype.exists]
    fconstructor
    · intro h; exact ⟨m.1, h, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact hn
  · refine Submodule.Quotient.equiv _ _
      (Submodule.Quotient.equiv _ _ (LinearEquiv.refl R _) ?_) ?_
    · ext m
      simp only [Submodule.map_top, Submodule.mem_map, LinearMap.mem_range, Subtype.exists,
        LinearEquiv.refl_apply, exists_eq_right, Submodule.mem_comap, Submodule.coeSubtype]
      fconstructor
      · rintro ⟨n, hn, rfl⟩; exact hn
      · intro h; exact ⟨m.1, h, rfl⟩
    · ext m
      simp only [Submodule.Quotient.equiv_refl, Submodule.map_top, Submodule.mem_map,
        LinearMap.mem_range, Subtype.exists, Submodule.mkQ_apply]
      fconstructor
      · rintro ⟨_, ⟨n, hn, ⟨⟨n', h0, h1⟩, rfl⟩⟩, h2⟩
        refine ⟨Submodule.Quotient.mk ⟨n', h0⟩, ?_⟩
        erw [Submodule.mapQ_apply]
        rw [h1, ← h2]
        rfl
      · rintro ⟨(z : _ ⧸ _), rfl⟩
        induction' z using Quotient.inductionOn' with z
        refine ⟨_, ⟨z.1, (le_of_lt <| x.step _) z.2, ⟨z.1, z.2, rfl⟩, rfl⟩, ?_⟩
        erw [Submodule.mapQ_apply]
        rfl

lemma LTSeries.cqf_succ_length_eq (i : Fin x.length) :
    moduleLength R (x.cqf i.succ) =
    moduleLength R (x.cqf i.castSucc) + moduleLength R (x.qf i) := by
  rw [moduleLength_congr (x.cdfSuccEquiv i)]
  rw [moduleLength.eq_length_submodule_add_length_quotient
    (Submodule.map (x.cqfToSucc i) ⊤ : Submodule R (x.cqf i.succ))]
  congr 1
  refine moduleLength_congr ?_
  rw [Submodule.map_top]
  exact x.rangeCQFToSucc _

lemma LTSeries.cqf_length_eq_sum (i : Fin (x.length + 1)) :
    moduleLength R (x.cqf i) =
    ∑ j : Fin i.1, moduleLength R (x.qf ⟨j.1, by linarith [j.2, i.2]⟩) := by
  induction' i using Fin.induction with i ih
  · simp only [Fin.val_zero, Finset.univ_eq_empty, Int.Nat.cast_ofNat_Int, Nat.rawCast,
    Nat.cast_id, Int.ofNat_one, Int.rawCast, Int.cast_id, Int.ofNat_eq_coe, Int.ofNat_zero,
    eq_mp_eq_cast, id_eq, Fin.succ_mk, Fin.castSucc_mk, Finset.sum_empty]
    rw [moduleLength_congr x.cqfZeroEquiv, moduleLength_punit]
  · erw [Fin.sum_univ_castSucc, ← ih, x.cqf_succ_length_eq]
    congr

lemma LTSeries.cqf_finiteLength_iff_each_qf_finiteLength (i : Fin (x.length + 1)) :
    IsFiniteLengthModule R (x.cqf i) ↔
    ∀ (j : Fin i.1), IsFiniteLengthModule R (x.qf ⟨j.1, by linarith [j.2, i.2]⟩) := by
  simp_rw [IsFiniteLengthModule_iff_moduleLength_finite', cqf_length_eq_sum, WithTop.sum_lt_top_iff]
  simp

end lt_series

end additive
