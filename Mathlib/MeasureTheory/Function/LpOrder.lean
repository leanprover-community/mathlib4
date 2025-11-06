/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Order related properties of Lp spaces

## Results

- `Lp E p μ` is an `OrderedAddCommGroup` when `E` is a `NormedLatticeAddCommGroup`.

## TODO

- move definitions of `Lp.posPart` and `Lp.negPart` to this file, and define them as
  `PosPart.pos` and `NegPart.neg` given by the lattice structure.

-/



open TopologicalSpace MeasureTheory
open scoped ENNReal

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

namespace Lp

section Order

variable [NormedAddCommGroup E]

section PartialOrder

variable [PartialOrder E]

theorem coeFn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← AEEqFun.coeFn_le]

theorem coeFn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← coeFn_le]
  have h0 := Lp.coeFn_zero E p μ
  constructor <;> intro h <;> filter_upwards [h, h0] with _ _ h2
  · rwa [h2]
  · rwa [← h2]

variable [OrderClosedTopology E] [IsOrderedAddMonoid E]

instance instAddLeftMono : AddLeftMono (Lp E p μ) := by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  rw [← coeFn_le] at hg₁₂ ⊢
  filter_upwards [coeFn_add f g₁, coeFn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  exact add_le_add le_rfl h3

instance instIsOrderedAddMonoid : IsOrderedAddMonoid (Lp E p μ) :=
  { add_le_add_left := fun _ _ => add_le_add_left }

instance [Fact (1 ≤ p)] : OrderClosedTopology (Lp E p μ) where
  isClosed_le' := isClosed_le_of_isClosed_nonneg <| IsSeqClosed.isClosed <|
      fun f f₀ (hf : ∀ n, 0 ≤ f n) h_tendsto ↦ by
    simp only [← coeFn_nonneg] at hf ⊢
    obtain ⟨φ, -, hφ⟩ := tendstoInMeasure_of_tendsto_Lp h_tendsto |>.exists_seq_tendsto_ae
    filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
    exact ge_of_tendsto' hφx fun _ ↦ Set.mem_iInter.mp hx _

end PartialOrder

section Lattice

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]

theorem _root_.MeasureTheory.MemLp.sup {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊔ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.Eventually.of_forall fun x => norm_sup_le_add (f x) (g x))

theorem _root_.MeasureTheory.MemLp.inf {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊓ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.Eventually.of_forall fun x => norm_inf_le_add (f x) (g x))

theorem _root_.MeasureTheory.MemLp.abs {f : α → E} (hf : MemLp f p μ) : MemLp |f| p μ :=
  hf.sup hf.neg

instance instLattice : Lattice (Lp E p μ) :=
  Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_memLp] at *
      exact (memLp_congr_ae (AEEqFun.coeFn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_memLp] at *
    exact (memLp_congr_ae (AEEqFun.coeFn_inf _ _)).mpr (hf.inf hg)

theorem coeFn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
  AEEqFun.coeFn_sup _ _

theorem coeFn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
  AEEqFun.coeFn_inf _ _

theorem coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x| :=
  AEEqFun.coeFn_abs _

instance instHasSolidNorm [Fact (1 ≤ p)] :
    HasSolidNorm (Lp E p μ) :=
  { solid := fun f g hfg => by
      rw [← coeFn_le] at hfg
      simp_rw [Lp.norm_def, ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)]
      refine eLpNorm_mono_ae ?_
      filter_upwards [hfg, Lp.coeFn_abs f, Lp.coeFn_abs g] with x hx hxf hxg
      rw [hxf, hxg] at hx
      exact HasSolidNorm.solid hx }

end Lattice

end Order

end Lp

end MeasureTheory
