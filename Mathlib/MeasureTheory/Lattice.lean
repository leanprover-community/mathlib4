/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable

#align_import measure_theory.lattice from "leanprover-community/mathlib"@"a95b442734d137aef46c1871e147089877fd0f62"

/-!
# Typeclasses for measurability of lattice operations

In this file we define classes `MeasurableSup` and `MeasurableInf` and prove dot-style
lemmas (`Measurable.sup`, `AEMeasurable.sup` etc). For binary operations we define two typeclasses:

- `MeasurableSup` says that both left and right sup are measurable;
- `MeasurableSup₂` says that `fun p : α × α => p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableSup₂`
etc require `α` to have a second countable topology.

For instances relating, e.g., `ContinuousSup` to `MeasurableSup` see file
`MeasureTheory.BorelSpace`.

## Tags

measurable function, lattice operation

-/


open MeasureTheory

/-- We say that a type has `MeasurableSup` if `(c ⊔ ·)` and `(· ⊔ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· ⊔ ·)` see `MeasurableSup₂`. -/
class MeasurableSup (M : Type*) [MeasurableSpace M] [Sup M] : Prop where
  measurable_const_sup : ∀ c : M, Measurable (c ⊔ ·)
  measurable_sup_const : ∀ c : M, Measurable (· ⊔ c)
#align has_measurable_sup MeasurableSup
#align has_measurable_sup.measurable_const_sup MeasurableSup.measurable_const_sup
#align has_measurable_sup.measurable_sup_const MeasurableSup.measurable_sup_const

/-- We say that a type has `MeasurableSup₂` if `uncurry (· ⊔ ·)` is a measurable functions.
For a typeclass assuming measurability of `(c ⊔ ·)` and `(· ⊔ c)` see `MeasurableSup`. -/
class MeasurableSup₂ (M : Type*) [MeasurableSpace M] [Sup M] : Prop where
  measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2
#align has_measurable_sup₂ MeasurableSup₂
#align has_measurable_sup₂.measurable_sup MeasurableSup₂.measurable_sup

export MeasurableSup₂ (measurable_sup)

export MeasurableSup (measurable_const_sup measurable_sup_const)

/-- We say that a type has `MeasurableInf` if `(c ⊓ ·)` and `(· ⊓ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· ⊓ ·)` see `MeasurableInf₂`. -/
class MeasurableInf (M : Type*) [MeasurableSpace M] [Inf M] : Prop where
  measurable_const_inf : ∀ c : M, Measurable (c ⊓ ·)
  measurable_inf_const : ∀ c : M, Measurable (· ⊓ c)
#align has_measurable_inf MeasurableInf
#align has_measurable_inf.measurable_const_inf MeasurableInf.measurable_const_inf
#align has_measurable_inf.measurable_inf_const MeasurableInf.measurable_inf_const

/-- We say that a type has `MeasurableInf₂` if `uncurry (· ⊓ ·)` is a measurable functions.
For a typeclass assuming measurability of `(c ⊓ ·)` and `(· ⊓ c)` see `MeasurableInf`. -/
class MeasurableInf₂ (M : Type*) [MeasurableSpace M] [Inf M] : Prop where
  measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2
#align has_measurable_inf₂ MeasurableInf₂
#align has_measurable_inf₂.measurable_inf MeasurableInf₂.measurable_inf

export MeasurableInf₂ (measurable_inf)

export MeasurableInf (measurable_const_inf measurable_inf_const)

variable {M : Type*} [MeasurableSpace M]

section OrderDual

instance (priority := 100) OrderDual.instMeasurableSup [Inf M] [MeasurableInf M] :
    MeasurableSup Mᵒᵈ :=
  ⟨@measurable_const_inf M _ _ _, @measurable_inf_const M _ _ _⟩
#align order_dual.has_measurable_sup OrderDual.instMeasurableSup

instance (priority := 100) OrderDual.instMeasurableInf [Sup M] [MeasurableSup M] :
    MeasurableInf Mᵒᵈ :=
  ⟨@measurable_const_sup M _ _ _, @measurable_sup_const M _ _ _⟩
#align order_dual.has_measurable_inf OrderDual.instMeasurableInf

instance (priority := 100) OrderDual.instMeasurableSup₂ [Inf M] [MeasurableInf₂ M] :
    MeasurableSup₂ Mᵒᵈ :=
  ⟨@measurable_inf M _ _ _⟩
#align order_dual.has_measurable_sup₂ OrderDual.instMeasurableSup₂

instance (priority := 100) OrderDual.instMeasurableInf₂ [Sup M] [MeasurableSup₂ M] :
    MeasurableInf₂ Mᵒᵈ :=
  ⟨@measurable_sup M _ _ _⟩
#align order_dual.has_measurable_inf₂ OrderDual.instMeasurableInf₂

end OrderDual

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α → M}

section Sup

variable [Sup M]

section MeasurableSup

variable [MeasurableSup M]

@[measurability]
theorem Measurable.const_sup (hf : Measurable f) (c : M) : Measurable fun x => c ⊔ f x :=
  (measurable_const_sup c).comp hf
#align measurable.const_sup Measurable.const_sup

@[measurability]
theorem AEMeasurable.const_sup (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊔ f x) μ :=
  (MeasurableSup.measurable_const_sup c).comp_aemeasurable hf
#align ae_measurable.const_sup AEMeasurable.const_sup

@[measurability]
theorem Measurable.sup_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊔ c :=
  (measurable_sup_const c).comp hf
#align measurable.sup_const Measurable.sup_const

@[measurability]
theorem AEMeasurable.sup_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊔ c) μ :=
  (measurable_sup_const c).comp_aemeasurable hf
#align ae_measurable.sup_const AEMeasurable.sup_const

end MeasurableSup

section MeasurableSup₂

variable [MeasurableSup₂ M]

@[measurability]
theorem Measurable.sup' (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊔ g) :=
  measurable_sup.comp (hf.prod_mk hg)
#align measurable.sup' Measurable.sup'

@[measurability]
theorem Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⊔ g a :=
  measurable_sup.comp (hf.prod_mk hg)
#align measurable.sup Measurable.sup

@[measurability]
theorem AEMeasurable.sup' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊔ g) μ :=
  measurable_sup.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.sup' AEMeasurable.sup'

@[measurability]
theorem AEMeasurable.sup (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a ⊔ g a) μ :=
  measurable_sup.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.sup AEMeasurable.sup

instance (priority := 100) MeasurableSup₂.toMeasurableSup : MeasurableSup M :=
  ⟨fun _ => measurable_const.sup measurable_id, fun _ => measurable_id.sup measurable_const⟩
#align has_measurable_sup₂.to_has_measurable_sup MeasurableSup₂.toMeasurableSup

end MeasurableSup₂

end Sup

section Inf

variable [Inf M]

section MeasurableInf

variable [MeasurableInf M]

@[measurability]
theorem Measurable.const_inf (hf : Measurable f) (c : M) : Measurable fun x => c ⊓ f x :=
  (measurable_const_inf c).comp hf
#align measurable.const_inf Measurable.const_inf

@[measurability]
theorem AEMeasurable.const_inf (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊓ f x) μ :=
  (MeasurableInf.measurable_const_inf c).comp_aemeasurable hf
#align ae_measurable.const_inf AEMeasurable.const_inf

@[measurability]
theorem Measurable.inf_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊓ c :=
  (measurable_inf_const c).comp hf
#align measurable.inf_const Measurable.inf_const

@[measurability]
theorem AEMeasurable.inf_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊓ c) μ :=
  (measurable_inf_const c).comp_aemeasurable hf
#align ae_measurable.inf_const AEMeasurable.inf_const

end MeasurableInf

section MeasurableInf₂

variable [MeasurableInf₂ M]

@[measurability]
theorem Measurable.inf' (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊓ g) :=
  measurable_inf.comp (hf.prod_mk hg)
#align measurable.inf' Measurable.inf'

@[measurability]
theorem Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⊓ g a :=
  measurable_inf.comp (hf.prod_mk hg)
#align measurable.inf Measurable.inf

@[measurability]
theorem AEMeasurable.inf' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊓ g) μ :=
  measurable_inf.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.inf' AEMeasurable.inf'

@[measurability]
theorem AEMeasurable.inf (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a ⊓ g a) μ :=
  measurable_inf.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.inf AEMeasurable.inf

instance (priority := 100) MeasurableInf₂.to_hasMeasurableInf : MeasurableInf M :=
  ⟨fun _ => measurable_const.inf measurable_id, fun _ => measurable_id.inf measurable_const⟩
#align has_measurable_inf₂.to_has_measurable_inf MeasurableInf₂.to_hasMeasurableInf

end MeasurableInf₂

end Inf

section SemilatticeSup

open Finset

variable {δ : Type*} [MeasurableSpace δ] [SemilatticeSup α] [MeasurableSup₂ α]

@[measurability]
theorem Finset.measurable_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.sup' hs f) :=
  Finset.sup'_induction hs _ (fun _f hf _g hg => hf.sup hg) fun n hn => hf n hn
#align finset.measurable_sup' Finset.measurable_sup'

@[measurability]
theorem Finset.measurable_range_sup' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable ((range (n + 1)).sup' nonempty_range_succ f) := by
  simp_rw [← Nat.lt_succ_iff] at hf
  -- ⊢ Measurable (sup' (range (n + 1)) (_ : Finset.Nonempty (range (n + 1))) f)
  refine' Finset.measurable_sup' _ _
  -- ⊢ ∀ (n_1 : ℕ), n_1 ∈ range (n + 1) → Measurable (f n_1)
  simpa [Finset.mem_range]
  -- 🎉 no goals
#align finset.measurable_range_sup' Finset.measurable_range_sup'

@[measurability]
theorem Finset.measurable_range_sup'' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable fun x => (range (n + 1)).sup' nonempty_range_succ fun k => f k x := by
  convert Finset.measurable_range_sup' hf using 1
  -- ⊢ (fun x => sup' (range (n + 1)) (_ : Finset.Nonempty (range (n + 1))) fun k = …
  ext x
  -- ⊢ (sup' (range (n + 1)) (_ : Finset.Nonempty (range (n + 1))) fun k => f k x)  …
  simp
  -- 🎉 no goals
#align finset.measurable_range_sup'' Finset.measurable_range_sup''

end SemilatticeSup
