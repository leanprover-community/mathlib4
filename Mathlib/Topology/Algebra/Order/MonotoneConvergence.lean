/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic

#align_import topology.algebra.order.monotone_convergence from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

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


open Filter Set Function

open Filter Topology Classical

variable {α β : Type*}

/-- We say that `α` is a `SupConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `Set.range f`. Then `f x` tends to `𝓝 a`
 as `x → ∞` (formally, at the filter `Filter.atTop`). We require this for `ι = (s : Set α)`,
`f = CoeTC.coe` in the definition, then prove it for any `f` in `tendsto_atTop_isLUB`.

This property holds for linear orders with order topology as well as their products. -/
class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    ∀ (a : α) (s : Set α), IsLUB s a → Tendsto (CoeTC.coe : s → α) atTop (𝓝 a)
#align Sup_convergence_class SupConvergenceClass

/-- We say that `α` is an `InfConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `Filter.atBot`). We require this for `ι = (s : Set α)`,
`f = CoeTC.coe` in the definition, then prove it for any `f` in `tendsto_atBot_isGLB`.

This property holds for linear orders with order topology as well as their products. -/
class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞`-/
  tendsto_coe_atBot_isGLB :
    ∀ (a : α) (s : Set α), IsGLB s a → Tendsto (CoeTC.coe : s → α) atBot (𝓝 a)
#align Inf_convergence_class InfConvergenceClass

instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ :=
  ⟨‹InfConvergenceClass α›.1⟩
#align order_dual.Sup_convergence_class OrderDual.supConvergenceClass

instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ :=
  ⟨‹SupConvergenceClass α›.1⟩
#align order_dual.Inf_convergence_class OrderDual.infConvergenceClass

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α := by
  refine' ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => _, fun b hb => _⟩⟩
  -- ⊢ ∀ᶠ (b_1 : ↑s) in atTop, b < CoeTC.coe b_1
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    -- ⊢ ∀ᶠ (b_1 : ↑s) in atTop, b < CoeTC.coe b_1
    lift c to s using hcs
    -- ⊢ ∀ᶠ (b_1 : ↑s) in atTop, b < CoeTC.coe b_1
    refine' (eventually_ge_atTop c).mono fun x hx => bc.trans_le hx
    -- 🎉 no goals
  · exact eventually_of_forall fun x => (ha.1 x.2).trans_lt hb
    -- 🎉 no goals
#align linear_order.Sup_convergence_class LinearOrder.supConvergenceClass

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α :=
  show InfConvergenceClass αᵒᵈᵒᵈ from OrderDual.infConvergenceClass
#align linear_order.Inf_convergence_class LinearOrder.infConvergenceClass

section

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices : Tendsto (rangeFactorization f) atTop atTop
  -- ⊢ Tendsto f atTop (𝓝 a)
  exact (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  -- ⊢ Tendsto (rangeFactorization f) atTop atTop
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge
  -- 🎉 no goals
#align tendsto_at_top_is_lub tendsto_atTop_isLUB

theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_anti.dual_left ha using 1
                                -- 🎉 no goals
#align tendsto_at_bot_is_lub tendsto_atBot_isLUB

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_mono.dual ha.dual using 1
                                -- 🎉 no goals
#align tendsto_at_bot_is_glb tendsto_atBot_isGLB

theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by convert tendsto_atBot_isLUB h_anti.dual ha.dual using 1
                                -- 🎉 no goals
#align tendsto_at_top_is_glb tendsto_atTop_isGLB

end IsGLB

section CiSup

variable [ConditionallyCompleteLattice α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  cases isEmpty_or_nonempty ι
  -- ⊢ Tendsto f atTop (𝓝 (⨆ (i : ι), f i))
  exacts [tendsto_of_isEmpty, tendsto_atTop_isLUB h_mono (isLUB_ciSup hbdd)]
  -- 🎉 no goals
#align tendsto_at_top_csupr tendsto_atTop_ciSup

theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by convert tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1
                                         -- 🎉 no goals
#align tendsto_at_bot_csupr tendsto_atBot_ciSup

end CiSup

section CiInf

variable [ConditionallyCompleteLattice α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by convert tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1
                                         -- 🎉 no goals
#align tendsto_at_bot_cinfi tendsto_atBot_ciInf

theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by convert tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1
                                         -- 🎉 no goals
#align tendsto_at_top_cinfi tendsto_atTop_ciInf

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)
#align tendsto_at_top_supr tendsto_atTop_iSup

theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)
#align tendsto_at_bot_supr tendsto_atBot_iSup

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)
#align tendsto_at_bot_infi tendsto_atBot_iInf

theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)
#align tendsto_at_top_infi tendsto_atTop_iInf

end iInf

end

instance Prod.supConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [SupConvergenceClass α] [SupConvergenceClass β] : SupConvergenceClass (α × β) := by
  constructor
  -- ⊢ ∀ (a : α × β) (s : Set (α × β)), IsLUB s a → Tendsto CoeTC.coe atTop (𝓝 a)
  rintro ⟨a, b⟩ s h
  -- ⊢ Tendsto CoeTC.coe atTop (𝓝 (a, b))
  rw [isLUB_prod, ← range_restrict, ← range_restrict] at h
  -- ⊢ Tendsto CoeTC.coe atTop (𝓝 (a, b))
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.restrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.restrict s) h.2
  convert A.prod_mk_nhds B
  -- 🎉 no goals
  -- porting note: previously required below to close
  -- ext1 ⟨⟨x, y⟩, h⟩
  -- rfl

instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) :=
  show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

instance Pi.supConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) := by
  refine' ⟨fun f s h => _⟩
  -- ⊢ Tendsto CoeTC.coe atTop (𝓝 f)
  simp only [isLUB_pi, ← range_restrict] at h
  -- ⊢ Tendsto CoeTC.coe atTop (𝓝 f)
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).restrict _) (h i)
  -- 🎉 no goals

instance Pi.infConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) :=
  show InfConvergenceClass (∀ i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass

instance Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι → α) :=
  supConvergenceClass
#align pi.Sup_convergence_class' Pi.supConvergenceClass'

instance Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι → α) :=
  Pi.infConvergenceClass
#align pi.Inf_convergence_class' Pi.infConvergenceClass'

theorem tendsto_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) :=
  if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H
#align tendsto_of_monotone tendsto_of_monotone

theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  -- ⊢ Tendsto f atTop (𝓝 l) → Tendsto (f ∘ φ) atTop (𝓝 l)
                  -- ⊢ Tendsto (f ∘ φ) atTop (𝓝 l)
                  -- ⊢ Tendsto f atTop (𝓝 l)
  · exact h.comp hg
    -- 🎉 no goals
  · rcases tendsto_of_monotone hf with (h' | ⟨l', hl'⟩)
    -- ⊢ Tendsto f atTop (𝓝 l)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
      -- 🎉 no goals
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]
      -- 🎉 no goals
#align tendsto_iff_tendsto_subseq_of_monotone tendsto_iff_tendsto_subseq_of_monotone

/-! The next family of results, such as `isLUB_of_tendsto_atTop` and `iSup_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `Filter.atTop`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`IsLUB.isLUB_of_tendsto`, `IsGLB.isGLB_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/

theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)
#align monotone.ge_of_tendsto Monotone.ge_of_tendsto

theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeInf β] {f : β → α} {a : α} (hf : Monotone f) (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual.ge_of_tendsto ha b
#align monotone.le_of_tendsto Monotone.le_of_tendsto

theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual_right.ge_of_tendsto ha b
#align antitone.le_of_tendsto Antitone.le_of_tendsto

theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [SemilatticeInf β] {f : β → α} {a : α} (hf : Antitone f) (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  hf.dual_right.le_of_tendsto ha b
#align antitone.ge_of_tendsto Antitone.ge_of_tendsto

theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  -- ⊢ a ∈ upperBounds (range f)
  · rintro _ ⟨b, rfl⟩
    -- ⊢ f b ≤ a
    exact hf.ge_of_tendsto ha b
    -- 🎉 no goals
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)
    -- 🎉 no goals
#align is_lub_of_tendsto_at_top isLUB_of_tendsto_atTop

theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeInf β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a :=
  @isLUB_of_tendsto_atTop αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual ha
#align is_glb_of_tendsto_at_bot isGLB_of_tendsto_atBot

theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeInf β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a :=
  @isLUB_of_tendsto_atTop α βᵒᵈ _ _ _ _ _ _ _ hf.dual_left ha
#align is_lub_of_tendsto_at_bot isLUB_of_tendsto_atBot

theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a :=
  @isGLB_of_tendsto_atBot α βᵒᵈ _ _ _ _ _ _ _ hf.dual_left ha
#align is_glb_of_tendsto_at_top isGLB_of_tendsto_atTop

theorem iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) → iSup f = a :=
  tendsto_nhds_unique (tendsto_atTop_iSup hf)
#align supr_eq_of_tendsto iSup_eq_of_tendsto

theorem iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) → iInf f = a :=
  tendsto_nhds_unique (tendsto_atTop_iInf hf)
#align infi_eq_of_tendsto iInf_eq_of_tendsto

theorem iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
#align supr_eq_supr_subseq_of_monotone iSup_eq_iSup_subseq_of_monotone

theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
#align supr_eq_supr_subseq_of_antitone iSup_eq_iSup_subseq_of_antitone

theorem iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_monotone hf.dual hφ
#align infi_eq_infi_subseq_of_monotone iInf_eq_iInf_subseq_of_monotone

theorem iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_antitone hf.dual hφ
