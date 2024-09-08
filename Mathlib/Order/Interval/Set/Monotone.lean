/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.SuccPred.Archimedean

/-!
# Monotonicity on intervals

In this file we prove that `Set.Ici` etc are monotone/antitone functions. We also prove some lemmas
about functions monotone on intervals in `SuccOrder`s.
-/


open Set

section Ixx

variable {α β : Type*} [Preorder α] [Preorder β] {f g : α → β} {s : Set α}

theorem antitone_Ici : Antitone (Ici : α → Set α) := fun _ _ => Ici_subset_Ici.2

theorem monotone_Iic : Monotone (Iic : α → Set α) := fun _ _ => Iic_subset_Iic.2

theorem antitone_Ioi : Antitone (Ioi : α → Set α) := fun _ _ => Ioi_subset_Ioi

theorem monotone_Iio : Monotone (Iio : α → Set α) := fun _ _ => Iio_subset_Iio

protected theorem Monotone.Ici (hf : Monotone f) : Antitone fun x => Ici (f x) :=
  antitone_Ici.comp_monotone hf

protected theorem MonotoneOn.Ici (hf : MonotoneOn f s) : AntitoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_monotoneOn hf

protected theorem Antitone.Ici (hf : Antitone f) : Monotone fun x => Ici (f x) :=
  antitone_Ici.comp hf

protected theorem AntitoneOn.Ici (hf : AntitoneOn f s) : MonotoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_antitoneOn hf

protected theorem Monotone.Iic (hf : Monotone f) : Monotone fun x => Iic (f x) :=
  monotone_Iic.comp hf

protected theorem MonotoneOn.Iic (hf : MonotoneOn f s) : MonotoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_monotoneOn hf

protected theorem Antitone.Iic (hf : Antitone f) : Antitone fun x => Iic (f x) :=
  monotone_Iic.comp_antitone hf

protected theorem AntitoneOn.Iic (hf : AntitoneOn f s) : AntitoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_antitoneOn hf

protected theorem Monotone.Ioi (hf : Monotone f) : Antitone fun x => Ioi (f x) :=
  antitone_Ioi.comp_monotone hf

protected theorem MonotoneOn.Ioi (hf : MonotoneOn f s) : AntitoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_monotoneOn hf

protected theorem Antitone.Ioi (hf : Antitone f) : Monotone fun x => Ioi (f x) :=
  antitone_Ioi.comp hf

protected theorem AntitoneOn.Ioi (hf : AntitoneOn f s) : MonotoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_antitoneOn hf

protected theorem Monotone.Iio (hf : Monotone f) : Monotone fun x => Iio (f x) :=
  monotone_Iio.comp hf

protected theorem MonotoneOn.Iio (hf : MonotoneOn f s) : MonotoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_monotoneOn hf

protected theorem Antitone.Iio (hf : Antitone f) : Antitone fun x => Iio (f x) :=
  monotone_Iio.comp_antitone hf

protected theorem AntitoneOn.Iio (hf : AntitoneOn f s) : AntitoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_antitoneOn hf

protected theorem Monotone.Icc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic

protected theorem MonotoneOn.Icc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic

protected theorem Antitone.Icc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic

protected theorem AntitoneOn.Icc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic

protected theorem Monotone.Ico (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio

protected theorem MonotoneOn.Ico (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio

protected theorem Antitone.Ico (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio

protected theorem AntitoneOn.Ico (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio

protected theorem Monotone.Ioc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic

protected theorem MonotoneOn.Ioc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic

protected theorem Antitone.Ioc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic

protected theorem AntitoneOn.Ioc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic

protected theorem Monotone.Ioo (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio

protected theorem MonotoneOn.Ioo (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

protected theorem Antitone.Ioo (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio

protected theorem AntitoneOn.Ioo (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

end Ixx

section iUnion

variable {α β : Type*} [SemilatticeSup α] [LinearOrder β] {f g : α → β} {a b : β}

theorem iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hf : Antitone f) (hg : Monotone g)
    (ha : IsGLB (range f) a) (hb : IsLUB (range g) b) : ⋃ x, Ioo (f x) (g x) = Ioo a b :=
  calc
    ⋃ x, Ioo (f x) (g x) = (⋃ x, Ioi (f x)) ∩ ⋃ x, Iio (g x) :=
      iUnion_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a ∩ Iio b := congr_arg₂ (· ∩ ·) ha.iUnion_Ioi_eq hb.iUnion_Iio_eq

end iUnion

section SuccOrder

open Order

variable {α β : Type*} [PartialOrder α] [Preorder β] {ψ : α → β}

/-- A function `ψ` on a `SuccOrder` is strictly monotone before some `n` if for all `m` such that
`m < n`, we have `ψ m < ψ (succ m)`. -/
theorem strictMonoOn_Iic_of_lt_succ [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : ∀ m, m < n → ψ m < ψ (succ m)) : StrictMonoOn ψ (Set.Iic n) := by
  intro x hx y hy hxy
  obtain ⟨i, rfl⟩ := hxy.le.exists_succ_iterate
  induction' i with k ih
  · simp at hxy
  cases' k with k
  · exact hψ _ (lt_of_lt_of_le hxy hy)
  rw [Set.mem_Iic] at *
  simp only [Function.iterate_succ', Function.comp_apply] at ih hxy hy ⊢
  by_cases hmax : IsMax (succ^[k] x)
  · rw [succ_eq_iff_isMax.2 hmax] at hxy ⊢
    exact ih (le_trans (le_succ _) hy) hxy
  by_cases hmax' : IsMax (succ (succ^[k] x))
  · rw [succ_eq_iff_isMax.2 hmax'] at hxy ⊢
    exact ih (le_trans (le_succ _) hy) hxy
  refine
    lt_trans
      (ih (le_trans (le_succ _) hy)
        (lt_of_le_of_lt (le_succ_iterate k _) (lt_succ_iff_not_isMax.2 hmax)))
      ?_
  rw [← Function.comp_apply (f := succ), ← Function.iterate_succ']
  refine hψ _ (lt_of_lt_of_le ?_ hy)
  rwa [Function.iterate_succ', Function.comp_apply, lt_succ_iff_not_isMax]

theorem strictAntiOn_Iic_of_succ_lt [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : ∀ m, m < n → ψ (succ m) < ψ m) : StrictAntiOn ψ (Set.Iic n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij

theorem strictMonoOn_Ici_of_pred_lt [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : ∀ m, n < m → ψ (pred m) < ψ m) : StrictMonoOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

theorem strictAntiOn_Ici_of_lt_pred [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : ∀ m, n < m → ψ m < ψ (pred m)) : StrictAntiOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictAntiOn_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

end SuccOrder

section LinearOrder

open Order

variable {α : Type*} [LinearOrder α]

theorem StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArchimedean α] [OrderBot α] {n : α} {φ : α → α}
    (hφ : StrictMonoOn φ (Set.Iic n)) : ∀ m ≤ n, m ≤ φ m := by
  revert hφ
  refine
    Succ.rec_bot (fun n => StrictMonoOn φ (Set.Iic n) → ∀ m ≤ n, m ≤ φ m)
      (fun _ _ hm => hm.trans bot_le) ?_ _
  rintro k ih hφ m hm
  by_cases hk : IsMax k
  · rw [succ_eq_iff_isMax.2 hk] at hm
    exact ih (hφ.mono <| Iic_subset_Iic.2 (le_succ _)) _ hm
  obtain rfl | h := le_succ_iff_eq_or_le.1 hm
  · specialize ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) k le_rfl
    refine le_trans (succ_mono ih) (succ_le_of_lt (hφ (le_succ _) le_rfl ?_))
    rw [lt_succ_iff_eq_or_lt_of_not_isMax hk]
    exact Or.inl rfl
  · exact ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) _ h

theorem StrictMonoOn.Ici_le_id [PredOrder α] [IsPredArchimedean α] [OrderTop α] {n : α} {φ : α → α}
    (hφ : StrictMonoOn φ (Set.Ici n)) : ∀ m, n ≤ m → φ m ≤ m :=
  StrictMonoOn.Iic_id_le (α := αᵒᵈ) fun _ hi _ hj hij => hφ hj hi hij

end LinearOrder
