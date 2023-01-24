/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex Kontorovich

! This file was ported from Lean 3 source module order.filter.pi
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Bases

/-!
# (Co)product of a family of filters

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `filter.pi (f : Π i, filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, filter.tendsto (function.eval i) (filter.pi f) (f i)`. It is defined as
  `Π i, filter.comap (function.eval i) (f i)`. This is a generalization of `filter.prod` to indexed
  products.

* `filter.Coprod (f : Π i, filter (α i))`: a generalization of `filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/


open Set Function

open Classical Filter

namespace Filter

variable {ι : Type _} {α : ι → Type _} {f f₁ f₂ : ∀ i, Filter (α i)} {s : ∀ i, Set (α i)}

section Pi

/-- The product of an indexed family of filters. -/
def pi (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (eval i) (f i)
#align filter.pi Filter.pi

instance pi.isCountablyGenerated [Countable ι] [∀ i, IsCountablyGenerated (f i)] :
    IsCountablyGenerated (pi f) :=
  Infi.isCountablyGenerated _
#align filter.pi.is_countably_generated Filter.pi.isCountablyGenerated

theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_infᵢ' i tendsto_comap
#align filter.tendsto_eval_pi Filter.tendsto_eval_pi

theorem tendsto_pi {β : Type _} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_infi, tendsto_comap_iff]
#align filter.tendsto_pi Filter.tendsto_pi

theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi
#align filter.le_pi Filter.le_pi

@[mono]
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  infᵢ_mono fun i => comap_mono <| h i
#align filter.pi_mono Filter.pi_mono

theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_infᵢ_of_mem i <| preimage_mem_comap hs
#align filter.mem_pi_of_mem Filter.mem_pi_of_mem

theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀ i ∈ I, s i ∈ f i) : I.pi s ∈ pi f :=
  by
  rw [pi_def, bInter_eq_Inter]
  refine' mem_infi_of_Inter hI (fun i => _) subset.rfl
  exact preimage_mem_comap (h i i.2)
#align filter.pi_mem_pi Filter.pi_mem_pi

theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s :=
  by
  constructor
  · simp only [pi, mem_infi', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, Inter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts
#align filter.mem_pi Filter.mem_pi

theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset
#align filter.mem_pi' Filter.mem_pi'

theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
    s i ∈ f i := by
  rcases mem_pi.1 h with ⟨I', I'f, t, htf, hts⟩
  refine' mem_of_superset (htf i) fun x hx => _
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg
  have : update g i x ∈ I'.pi t := by
    intro j hj
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi
#align filter.mem_of_pi_mem_pi Filter.mem_of_pi_mem_pi

@[simp]
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
  ⟨fun h i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩
#align filter.pi_mem_pi_iff Filter.pi_mem_pi_iff

theorem hasBasis_pi {ι' : ι → Type} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i :=
  by
  have : (pi f).HasBasis _ _ := has_basis_infi' fun i => (h i).comap (eval i : (∀ j, α j) → α i)
  convert this
  ext
  simp
#align filter.has_basis_pi Filter.hasBasis_pi

@[simp]
theorem pi_inf_principal_univ_pi_eq_bot : pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ :=
  by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt
    exact hts (fun i hi => hxt i) (mem_univ_pi.2 hxs)
  · simp only [inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi]with x using mt fun h => h i trivial
#align filter.pi_inf_principal_univ_pi_eq_bot Filter.pi_inf_principal_univ_pi_eq_bot

@[simp]
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ :=
  by
  rw [← univ_pi_piecewise I, pi_inf_principal_univ_pi_eq_bot]
  refine' exists_congr fun i => _
  by_cases hi : i ∈ I <;> simp [hi, (‹∀ i, ne_bot (f i)› i).Ne]
#align filter.pi_inf_principal_pi_eq_bot Filter.pi_inf_principal_pi_eq_bot

@[simp]
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ ∀ i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [ne_bot_iff]
#align filter.pi_inf_principal_univ_pi_ne_bot Filter.pi_inf_principal_univ_pi_neBot

@[simp]
theorem pi_inf_principal_pi_neBot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [ne_bot_iff]
#align filter.pi_inf_principal_pi_ne_bot Filter.pi_inf_principal_pi_neBot

instance PiInfPrincipalPi.neBot [h : ∀ i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono <|
    inf_le_inf_left _ <| principal_mono.2 fun x hx i hi => hx i trivial
#align filter.pi_inf_principal_pi.ne_bot Filter.PiInfPrincipalPi.neBot

@[simp]
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ
#align filter.pi_eq_bot Filter.pi_eq_bot

@[simp]
theorem pi_neBot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by simp [ne_bot_iff]
#align filter.pi_ne_bot Filter.pi_neBot

instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

@[simp]
theorem map_eval_pi (f : ∀ i, Filter (α i)) [∀ i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i :=
  by
  refine' le_antisymm (tendsto_eval_pi f i) fun s hs => _
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine' mem_of_superset (htf i) ((subset_eval_image_pi _ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i hi => htf i)
#align filter.map_eval_pi Filter.map_eval_pi

@[simp]
theorem pi_le_pi [∀ i, NeBot (f₁ i)] : pi f₁ ≤ pi f₂ ↔ ∀ i, f₁ i ≤ f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩
#align filter.pi_le_pi Filter.pi_le_pi

@[simp]
theorem pi_inj [∀ i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ :=
  by
  refine' ⟨fun h => _, congr_arg pi⟩
  have hle : f₁ ≤ f₂ := pi_le_pi.1 h.le
  haveI : ∀ i, ne_bot (f₂ i) := fun i => ne_bot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)
#align filter.pi_inj Filter.pi_inj

end Pi

/-! ### `n`-ary coproducts of filters -/


section CoprodCat

/- warning: filter.Coprod clashes with filter.coprod -> Filter.coprod
warning: filter.Coprod -> Filter.coprod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}}, (forall (i : ι), Filter.{u2} (α i)) -> (Filter.{max u1 u2} (forall (i : ι), α i))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}}, (Filter.{u1} ι) -> (Filter.{u2} α) -> (Filter.{max u2 u1} (Prod.{u1, u2} ι α))
Case conversion may be inaccurate. Consider using '#align filter.Coprod Filter.coprodₓ'. -/
/-- Coproduct of filters. -/
protected def coprod (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)
#align filter.Coprod Filter.coprod

/- warning: filter.mem_Coprod_iff clashes with filter.mem_coprod_iff -> Filter.mem_coprod_iff
warning: filter.mem_Coprod_iff -> Filter.mem_coprod_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : Set.{max u1 u2} (forall (i : ι), α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) s (Filter.coprod.{u1, u2} ι (fun (i : ι) => α i) f)) (forall (i : ι), Exists.{succ u2} (Set.{u2} (α i)) (fun (t₁ : Set.{u2} (α i)) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) t₁ (f i)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) t₁ (f i)) => HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (x : ι), α x)) (Set.hasSubset.{max u1 u2} (forall (x : ι), α x)) (Set.preimage.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) t₁) s)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {f : Set.{max u2 u1} (Prod.{u1, u2} ι α)} {s : Filter.{u1} ι} {g : Filter.{u2} α}, Iff (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} ι α)) (Filter.{max u2 u1} (Prod.{u1, u2} ι α)) (instMembershipSetFilter.{max u1 u2} (Prod.{u1, u2} ι α)) f (Filter.coprod.{u1, u2} ι α s g)) (And (Exists.{succ u1} (Set.{u1} ι) (fun (t₁ : Set.{u1} ι) => And (Membership.mem.{u1, u1} (Set.{u1} ι) (Filter.{u1} ι) (instMembershipSetFilter.{u1} ι) t₁ s) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} ι α)) (Set.instHasSubsetSet.{max u1 u2} (Prod.{u1, u2} ι α)) (Set.preimage.{max u2 u1, u1} (Prod.{u1, u2} ι α) ι (Prod.fst.{u1, u2} ι α) t₁) f))) (Exists.{succ u2} (Set.{u2} α) (fun (t₂ : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t₂ g) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} ι α)) (Set.instHasSubsetSet.{max u1 u2} (Prod.{u1, u2} ι α)) (Set.preimage.{max u2 u1, u2} (Prod.{u1, u2} ι α) α (Prod.snd.{u1, u2} ι α) t₂) f))))
Case conversion may be inaccurate. Consider using '#align filter.mem_Coprod_iff Filter.mem_coprod_iffₓ'. -/
theorem mem_coprod_iff {s : Set (∀ i, α i)} :
    s ∈ Filter.coprod f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by simp [Filter.coprod]
#align filter.mem_Coprod_iff Filter.mem_coprod_iff

/- warning: filter.compl_mem_Coprod clashes with filter.compl_mem_coprod -> Filter.compl_mem_coprod
warning: filter.compl_mem_Coprod -> Filter.compl_mem_coprod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : Set.{max u1 u2} (forall (i : ι), α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) (HasCompl.compl.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toHasCompl.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i))) s) (Filter.coprod.{u1, u2} ι (fun (i : ι) => α i) f)) (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) (HasCompl.compl.{u2} (Set.{u2} (α i)) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} (α i)) (Set.booleanAlgebra.{u2} (α i))) (Set.image.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) s)) (f i))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {f : Set.{max u2 u1} (Prod.{u1, u2} ι α)} {s : Filter.{u1} ι} {lb : Filter.{u2} α}, Iff (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} ι α)) (Filter.{max u2 u1} (Prod.{u1, u2} ι α)) (instMembershipSetFilter.{max u1 u2} (Prod.{u1, u2} ι α)) (HasCompl.compl.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} ι α)) (BooleanAlgebra.toHasCompl.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} ι α)) (Set.instBooleanAlgebraSet.{max u1 u2} (Prod.{u1, u2} ι α))) f) (Filter.coprod.{u1, u2} ι α s lb)) (And (Membership.mem.{u1, u1} (Set.{u1} ι) (Filter.{u1} ι) (instMembershipSetFilter.{u1} ι) (HasCompl.compl.{u1} (Set.{u1} ι) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} ι) (Set.instBooleanAlgebraSet.{u1} ι)) (Set.image.{max u2 u1, u1} (Prod.{u1, u2} ι α) ι (Prod.fst.{u1, u2} ι α) f)) s) (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (Set.image.{max u2 u1, u2} (Prod.{u1, u2} ι α) α (Prod.snd.{u1, u2} ι α) f)) lb))
Case conversion may be inaccurate. Consider using '#align filter.compl_mem_Coprod Filter.compl_mem_coprodₓ'. -/
theorem compl_mem_coprod {s : Set (∀ i, α i)} : sᶜ ∈ Filter.coprod f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i :=
  by simp only [Filter.coprod, mem_supr, compl_mem_comap]
#align filter.compl_mem_Coprod Filter.compl_mem_coprod

theorem coprod_neBot_iff' : NeBot (Filter.coprod f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) := by
  simp only [Filter.coprod, supr_ne_bot, ← exists_and_left, ← comap_eval_ne_bot_iff']
#align filter.Coprod_ne_bot_iff' Filter.coprod_neBot_iff'

/- warning: filter.Coprod_ne_bot_iff clashes with filter.coprod_ne_bot_iff -> Filter.coprod_neBot_iff
warning: filter.Coprod_ne_bot_iff -> Filter.coprod_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} [_inst_1 : forall (i : ι), Nonempty.{succ u2} (α i)], Iff (Filter.NeBot.{max u1 u2} (forall (i : ι), α i) (Filter.coprod.{u1, u2} ι (fun (i : ι) => α i) f)) (Exists.{succ u1} ι (fun (d : ι) => Filter.NeBot.{u2} (α d) (f d)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {f : Filter.{u2} ι} {_inst_1 : Filter.{u1} α}, Iff (Filter.NeBot.{max u2 u1} (Prod.{u2, u1} ι α) (Filter.coprod.{u2, u1} ι α f _inst_1)) (Or (And (Filter.NeBot.{u2} ι f) (Nonempty.{succ u1} α)) (And (Nonempty.{succ u2} ι) (Filter.NeBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_ne_bot_iff Filter.coprod_neBot_iffₓ'. -/
@[simp]
theorem coprod_neBot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprod f) ↔ ∃ d, NeBot (f d) := by
  simp [Coprod_ne_bot_iff', *]
#align filter.Coprod_ne_bot_iff Filter.coprod_neBot_iff

theorem coprod_eq_bot_iff' : Filter.coprod f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa [not_and_or, funext_iff] using not_congr Coprod_ne_bot_iff'
#align filter.Coprod_eq_bot_iff' Filter.coprod_eq_bot_iff'

@[simp]
theorem coprod_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprod f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using not_congr Coprod_ne_bot_iff
#align filter.Coprod_eq_bot_iff Filter.coprod_eq_bot_iff

@[simp]
theorem coprod_bot' : Filter.coprod (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprod_eq_bot_iff'.2 (Or.inr rfl)
#align filter.Coprod_bot' Filter.coprod_bot'

/- warning: filter.Coprod_bot clashes with filter.coprod_bot -> Filter.coprod_bot
warning: filter.Coprod_bot -> Filter.coprod_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.coprod.{u1, u2} ι (fun (_x : ι) => α _x) (fun (_x : ι) => Bot.bot.{u2} (Filter.{u2} (α _x)) (CompleteLattice.toHasBot.{u2} (Filter.{u2} (α _x)) (Filter.completeLattice.{u2} (α _x))))) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} (l : Filter.{u2} ι), Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} ι α)) (Filter.coprod.{u2, u1} ι α l (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Filter.comap.{max u1 u2, u2} (Prod.{u2, u1} ι α) ι (Prod.fst.{u2, u1} ι α) l)
Case conversion may be inaccurate. Consider using '#align filter.Coprod_bot Filter.coprod_botₓ'. -/
@[simp]
theorem coprod_bot : Filter.coprod (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  Coprod_bot'
#align filter.Coprod_bot Filter.coprod_bot

theorem NeBot.coprod [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprod f) :=
  coprod_neBot_iff.2 ⟨i, h⟩
#align filter.ne_bot.Coprod Filter.NeBot.coprod

@[instance]
theorem coprod_neBot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i))
    [H : ∀ i, NeBot (f i)] : NeBot (Filter.coprod f) :=
  (H (Classical.arbitrary ι)).coprod
#align filter.Coprod_ne_bot Filter.coprod_neBot

/- warning: filter.Coprod_mono clashes with filter.coprod_mono -> Filter.coprod_mono
warning: filter.Coprod_mono -> Filter.coprod_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)}, (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.partialOrder.{u2} (α i)))) (f₁ i) (f₂ i)) -> (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.partialOrder.{max u1 u2} (forall (i : ι), α i)))) (Filter.coprod.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.coprod.{u1, u2} ι (fun (i : ι) => α i) f₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {f₁ : Filter.{u2} ι} {f₂ : Filter.{u2} ι} {hf : Filter.{u1} α} {g₂ : Filter.{u1} α}, (LE.le.{u2} (Filter.{u2} ι) (Preorder.toLE.{u2} (Filter.{u2} ι) (PartialOrder.toPreorder.{u2} (Filter.{u2} ι) (Filter.instPartialOrderFilter.{u2} ι))) f₁ f₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) hf g₂) -> (LE.le.{max u2 u1} (Filter.{max u1 u2} (Prod.{u2, u1} ι α)) (Preorder.toLE.{max u2 u1} (Filter.{max u1 u2} (Prod.{u2, u1} ι α)) (PartialOrder.toPreorder.{max u2 u1} (Filter.{max u1 u2} (Prod.{u2, u1} ι α)) (Filter.instPartialOrderFilter.{max u2 u1} (Prod.{u2, u1} ι α)))) (Filter.coprod.{u2, u1} ι α f₁ hf) (Filter.coprod.{u2, u1} ι α f₂ g₂))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_mono Filter.coprod_monoₓ'. -/
@[mono]
theorem coprod_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprod f₁ ≤ Filter.coprod f₂ :=
  supᵢ_mono fun i => comap_mono (hf i)
#align filter.Coprod_mono Filter.coprod_mono

variable {β : ι → Type _} {m : ∀ i, α i → β i}

theorem map_pi_map_coprod_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprod f) ≤
      Filter.coprod fun i => map (m i) (f i) :=
  by
  simp only [le_def, mem_map, mem_Coprod_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x ∈ t }, H, fun x hx => hH hx⟩
#align filter.map_pi_map_Coprod_le Filter.map_pi_map_coprod_le

theorem Tendsto.pi_map_coprod {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprod f) (Filter.coprod g) :=
  map_pi_map_coprod_le.trans (coprod_mono h)
#align filter.tendsto.pi_map_Coprod Filter.Tendsto.pi_map_coprod

end CoprodCat

end Filter

