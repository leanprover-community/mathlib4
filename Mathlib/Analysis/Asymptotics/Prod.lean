/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Basic

/-!
# Asymptotic relations and product types

This file contains lemmas about asymptotic relations for product-valued functions and product
filters.

-/

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Filter

namespace Asymptotics

variable {α β E F E' F' G' : Type*}

variable [Norm E] [Norm F]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
variable {c c' : ℝ} {f : α → E} {g : α → F}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {l : Filter α}

/-! ### Product of functions (right) -/

theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_left _ _

theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_right _ _

theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.isBigO

theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.isBigO

theorem isBigO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_fst_prod (E' := E') (F' := F')

theorem isBigO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_snd_prod (E' := E') (F' := F')

section

variable (f' k')

theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)

theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO

theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le

theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)

theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO

theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le

end

section

variable {f : α × β → E} {g : α × β → F} {l' : Filter β}

protected theorem IsBigO.fiberwise_right :
    f =O[l ×ˢ l'] g → ∀ᶠ a in l, (f ⟨a, ·⟩) =O[l'] (g ⟨a, ·⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₁ fun _ ha ↦ ⟨c, mem_of_superset ht₂ fun _ hb ↦ ht ⟨ha, hb⟩⟩

protected theorem IsBigO.fiberwise_left :
    f =O[l ×ˢ l'] g → ∀ᶠ b in l', (f ⟨·, b⟩) =O[l] (g ⟨·, b⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₂ fun _ hb ↦ ⟨c, mem_of_superset ht₁ fun _ ha ↦ ht ⟨ha, hb⟩⟩

end

section

variable (l' : Filter β)

protected theorem IsBigO.comp_fst : f =O[l] g → (f ∘ Prod.fst) =O[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ ↦ ⟨c, _, hc, fun _ ↦ True, eventually_true l', fun {_} h {_} _ ↦ h⟩

protected theorem IsBigO.comp_snd : f =O[l] g → (f ∘ Prod.snd) =O[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ ↦ ⟨c, fun _ ↦ True, eventually_true l', _, hc, fun _ ↦ id⟩

protected theorem IsLittleO.comp_fst : f =o[l] g → (f ∘ Prod.fst) =o[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc ↦ ⟨_, h hc, fun _ ↦ True, eventually_true l', fun {_} h {_} _ ↦ h⟩

protected theorem IsLittleO.comp_snd : f =o[l] g → (f ∘ Prod.snd) =o[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc ↦ ⟨fun _ ↦ True, eventually_true l', _, h hc, fun _ ↦ id⟩

end

theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg] with x using max_le

theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')

theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
  (isBigOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c

theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
  (isBigOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c

theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO

theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod

theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod

@[simp]
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)

theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod

theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod

@[simp]
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
end Asymptotics
