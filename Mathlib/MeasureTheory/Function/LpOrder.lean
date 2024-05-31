/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Function.LpSpace

#align_import measure_theory.function.lp_order from "leanprover-community/mathlib"@"5dc275ec639221ca4d5f56938eb966f6ad9bc89f"

/-!
# Order related properties of Lp spaces

### Results

- `Lp E p μ` is an `OrderedAddCommGroup` when `E` is a `NormedLatticeAddCommGroup`.

### TODO

- move definitions of `Lp.posPart` and `Lp.negPart` to this file, and define them as
  `PosPart.pos` and `NegPart.neg` given by the lattice structure.

-/


set_option linter.uppercaseLean3 false

open TopologicalSpace MeasureTheory
open scoped ENNReal

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

namespace Lp

section Order

variable [NormedLatticeAddCommGroup E]

theorem coeFn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← AEEqFun.coeFn_le]
#align measure_theory.Lp.coe_fn_le MeasureTheory.Lp.coeFn_le

theorem coeFn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← coeFn_le]
  have h0 := Lp.coeFn_zero E p μ
  constructor <;> intro h <;> filter_upwards [h, h0] with _ _ h2
  · rwa [h2]
  · rwa [← h2]
#align measure_theory.Lp.coe_fn_nonneg MeasureTheory.Lp.coeFn_nonneg

instance instCovariantClassLE : CovariantClass (Lp E p μ) (Lp E p μ) (· + ·) (· ≤ ·) := by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  rw [← coeFn_le] at hg₁₂ ⊢
  filter_upwards [coeFn_add f g₁, coeFn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  exact add_le_add le_rfl h3
#align measure_theory.Lp.has_le.le.covariant_class MeasureTheory.Lp.instCovariantClassLE

instance instOrderedAddCommGroup : OrderedAddCommGroup (Lp E p μ) :=
  { Subtype.partialOrder _, AddSubgroup.toAddCommGroup _ with
    add_le_add_left := fun _ _ => add_le_add_left }
#align measure_theory.Lp.ordered_add_comm_group MeasureTheory.Lp.instOrderedAddCommGroup

theorem _root_.MeasureTheory.Memℒp.sup {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    Memℒp (f ⊔ g) p μ :=
  Memℒp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.eventually_of_forall fun x => norm_sup_le_add (f x) (g x))
#align measure_theory.mem_ℒp.sup MeasureTheory.Memℒp.sup

theorem _root_.MeasureTheory.Memℒp.inf {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    Memℒp (f ⊓ g) p μ :=
  Memℒp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.eventually_of_forall fun x => norm_inf_le_add (f x) (g x))
#align measure_theory.mem_ℒp.inf MeasureTheory.Memℒp.inf

theorem _root_.MeasureTheory.Memℒp.abs {f : α → E} (hf : Memℒp f p μ) : Memℒp |f| p μ :=
  hf.sup hf.neg
#align measure_theory.mem_ℒp.abs MeasureTheory.Memℒp.abs

instance instLattice : Lattice (Lp E p μ) :=
  Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_memℒp] at *
      exact (memℒp_congr_ae (AEEqFun.coeFn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_memℒp] at *
    exact (memℒp_congr_ae (AEEqFun.coeFn_inf _ _)).mpr (hf.inf hg)
#align measure_theory.Lp.lattice MeasureTheory.Lp.instLattice

theorem coeFn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
  AEEqFun.coeFn_sup _ _
#align measure_theory.Lp.coe_fn_sup MeasureTheory.Lp.coeFn_sup

theorem coeFn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
  AEEqFun.coeFn_inf _ _
#align measure_theory.Lp.coe_fn_inf MeasureTheory.Lp.coeFn_inf

theorem coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x| :=
  AEEqFun.coeFn_abs _
#align measure_theory.Lp.coe_fn_abs MeasureTheory.Lp.coeFn_abs

noncomputable instance instNormedLatticeAddCommGroup [Fact (1 ≤ p)] :
    NormedLatticeAddCommGroup (Lp E p μ) :=
  { Lp.instLattice, Lp.instNormedAddCommGroup with
    add_le_add_left := fun f g => add_le_add_left
    solid := fun f g hfg => by
      rw [← coeFn_le] at hfg
      simp_rw [Lp.norm_def, ENNReal.toReal_le_toReal (Lp.snorm_ne_top f) (Lp.snorm_ne_top g)]
      refine snorm_mono_ae ?_
      filter_upwards [hfg, Lp.coeFn_abs f, Lp.coeFn_abs g] with x hx hxf hxg
      rw [hxf, hxg] at hx
      exact HasSolidNorm.solid hx }
#align measure_theory.Lp.normed_lattice_add_comm_group MeasureTheory.Lp.instNormedLatticeAddCommGroup

end Order

end Lp

end MeasureTheory
