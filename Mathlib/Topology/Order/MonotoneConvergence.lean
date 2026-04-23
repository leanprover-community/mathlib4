/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Monotone
import Mathlib.Init
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `IsLUB`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `Prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

@[expose] public section

open Filter Set Function
open scoped Topology

variable {α β : Type*}

/-- We say that `α` is a `SupConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → ∞` (formally, at the filter `Filter.atTop`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atTop_isLUB`.

This property holds for linear orders with order topology as well as their products. -/
class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    ∀ (a : α) (s : Set α), IsLUB s a → Tendsto ((↑) : s → α) atTop (𝓝 a)

/-- We say that `α` is an `InfConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `Filter.atBot`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atBot_isGLB`.

This property holds for linear orders with order topology as well as their products. -/
class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞` -/
  tendsto_coe_atBot_isGLB :
    ∀ (a : α) (s : Set α), IsGLB s a → Tendsto ((↑) : s → α) atBot (𝓝 a)

instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ :=
  ⟨‹InfConvergenceClass α›.1⟩

instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ :=
  ⟨‹SupConvergenceClass α›.1⟩

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    exact (eventually_ge_atTop c).mono fun x hx => bc.trans_le hx
  · exact Eventually.of_forall fun x => (ha.1 x.2).trans_lt hb

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α :=
  show InfConvergenceClass αᵒᵈᵒᵈ from OrderDual.infConvergenceClass

section

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_anti.dual_left ha using 1

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_mono.dual ha.dual using 1

theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by convert tendsto_atBot_isLUB h_anti.dual ha.dual using 1

end IsGLB

section CiSup

variable [ConditionallyCompletePartialOrderSup α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
    exact tendsto_atTop_isLUB h_mono <|
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by convert tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1

end CiSup

section CiInf

variable [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by convert tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1

theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by convert tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

end iInf

end

instance Prod.supConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [SupConvergenceClass α] [SupConvergenceClass β] : SupConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod, ← range_restrict, ← range_restrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.restrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.restrict s) h.2
  exact A.prodMk_nhds B

instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) :=
  show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

instance Pi.supConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_restrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).restrict _) (h i)

instance Pi.infConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) :=
  show InfConvergenceClass (∀ i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

instance Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι → α) :=
  supConvergenceClass

instance Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι → α) :=
  Pi.infConvergenceClass

theorem tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H

@[deprecated (since := "2026-01-22")] alias tendsto_of_monotone := tendsto_atTop_of_monotone

theorem tendsto_atTop_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atTop atBot ∨ ∃ l, Tendsto f atTop (𝓝 l) :=
  tendsto_atTop_of_monotone (α := αᵒᵈ) h_mono

@[deprecated (since := "2026-01-22")] alias tendsto_of_antitone := tendsto_atTop_of_antitone

theorem tendsto_atBot_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atBot atBot ∨ ∃ l, Tendsto f atBot (𝓝 l) :=
  tendsto_atTop_of_monotone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

theorem tendsto_atBot_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atBot atTop ∨ ∃ l, Tendsto f atBot (𝓝 l) :=
  tendsto_atTop_of_antitone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual

theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

theorem tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMinOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Antitone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) :=
  tendsto_iff_tendsto_subseq_of_monotone (α := αᵒᵈ) hf hg

/-! The next family of results, such as `isLUB_of_tendsto_atTop` and `iSup_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `Filter.atTop`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`IsLUB.isLUB_of_tendsto`, `IsGLB.isGLB_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/

theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual.ge_of_tendsto ha b

theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual_right.ge_of_tendsto ha b

theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  hf.dual_right.le_of_tendsto ha b

theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a :=
  isLUB_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) hf.dual ha

theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a :=
  isLUB_of_tendsto_atTop (α := α) (β := βᵒᵈ) hf.dual_left ha

theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a :=
  isGLB_of_tendsto_atBot (α := α) (β := βᵒᵈ) hf.dual_left ha

theorem iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) → iSup f = a :=
  tendsto_nhds_unique (tendsto_atTop_iSup hf)

theorem iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) → iInf f = a :=
  tendsto_nhds_unique (tendsto_atTop_iInf hf)

theorem iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_monotone hf.dual hφ

theorem iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_antitone hf.dual hφ
