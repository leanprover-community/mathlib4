/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He
-/
import Mathlib.Topology.Sequences
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuous

/-!
## Main results

We introduce some equivalent definitions of LowerSemicontinuous functions.
* `lowerSemicontinuous_iff_le_liminf`:
  a function is lower semi-continuous if and only if `∀ x, f x ≤ (liminf f <| 𝓝 x)`
* `lowerSemicontinuous_iff_IsClosed_epigraph`:
  a function is lower semi-continuous if and only if its epigraph is closed.
* `lowerSemicontinuous_iff_IsClosed_sublevel`:
  a function is lower semi-continuous if and only if all its sublevel sets are closed.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>
* <https://en.wikipedia.org/wiki/Semi-continuity>

-/


open Topology Filter Set TopologicalSpace

variable {𝕜 E F α β ι : Type*}

variable [AddCommMonoid E]

variable [CompleteLinearOrder F] [DenselyOrdered F]

variable {x : E} {s t : Set E} {f : E → F}

variable [TopologicalSpace E] [TopologicalSpace F]

variable [FirstCountableTopology E] [FirstCountableTopology F]

variable [OrderTopology F]

theorem lowerSemicontinuous_TFAE (f : E → F) :
    List.TFAE [LowerSemicontinuous f,
      ∀ x, f x ≤ (liminf f <| 𝓝 x),
      IsClosed {p : E × F | f p.1 ≤ p.2},
      ∀ (r : F), IsClosed {x | f x ≤ r}] := by
  tfae_have 1 → 2
  · intro hf x; specialize hf x
    unfold LowerSemicontinuousAt at hf
    contrapose! hf
    obtain ⟨y,lty,ylt⟩ := exists_between hf; use y
    exact ⟨ylt, fun h => not_le_of_lt lty
      (Filter.le_liminf_of_le (by isBoundedDefault)
        (Eventually.mono h (fun _ hx => le_of_lt hx)))⟩
  tfae_have 2 → 1
  · exact fun hf x y ylt
      => Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le ylt (hf x))
  tfae_have 2 → 3
  · intro hf; apply IsSeqClosed.isClosed
    intro f' ⟨x', y'⟩ hxy cxy
    rw [Prod.tendsto_iff] at cxy
    let x : ℕ -> E := fun (n : ℕ) => (f' n).1
    calc
      f x' ≤ liminf f (𝓝 x') := hf x'
      _ ≤ liminf (f ∘ x) atTop := by
        rw[liminf_eq, liminf_eq]
        exact sSup_le_sSup (fun _ fa => (eventually_iff_seq_eventually.mp fa) x cxy.1)
      _ ≤ liminf (fun (n : ℕ) => (f' n).2) atTop :=
        liminf_le_liminf (eventually_of_forall (fun n => by convert hxy n))
      _ = y' := (cxy.2).liminf_eq
  tfae_have 3 → 4
  · exact fun hf _ => IsSeqClosed.isClosed fun ⦃_⦄ ⦃_⦄ xns cx =>
    IsClosed.isSeqClosed hf (fun n => xns n) (Tendsto.prod_mk_nhds cx tendsto_const_nhds)
  tfae_have 4 → 2
  · intro h; by_contra h; push_neg at h
    obtain ⟨x, hx⟩ := h
    obtain ⟨t, ⟨ltt, tlt⟩⟩ := exists_between hx
    apply not_le_of_gt tlt
    apply isClosed_iff_frequently.mp (h t) x
    apply frequently_iff.mpr; intro _ hu
    have h : ∃ᶠ (y : E) in 𝓝 x, f y ≤ t := by
      apply frequently_iff.mpr; intro _ hu
      obtain ⟨x, xu, fx⟩ :=
        (frequently_iff.mp (frequently_lt_of_liminf_lt (by isBoundedDefault) ltt)) hu
      exact Exists.intro x ⟨xu, LT.lt.le fx⟩
    obtain ⟨x, xu, fx⟩ := (frequently_iff.mp h) hu
    exact Exists.intro x ⟨xu, fx⟩
  tfae_finish

theorem lowerSemicontinuous_iff_le_liminf :
    LowerSemicontinuous f ↔ ∀ x, f x ≤ (liminf f <| 𝓝 x) :=
  (lowerSemicontinuous_TFAE f).out 0 1

theorem lowerSemicontinuous_iff_IsClosed_epigraph :
    LowerSemicontinuous f ↔ IsClosed {p : E × F | f p.1 ≤ p.2} :=
  (lowerSemicontinuous_TFAE f).out 0 2

theorem lowerSemicontinuous_iff_IsClosed_sublevel :
    LowerSemicontinuous f ↔ ∀ (r : F), IsClosed {x | f x ≤ r} :=
  (lowerSemicontinuous_TFAE f).out 0 3

theorem LowerSemicontinuous.le_liminf (hf : LowerSemicontinuous f) :
    ∀ x, f x ≤ (liminf f <| 𝓝 x) :=
  lowerSemicontinuous_iff_le_liminf.mp hf

theorem LowerSemicontinuous.IsClosed_sublevel {f : E → F} (hf : LowerSemicontinuous f) :
    ∀ (r : F), IsClosed {x | f x ≤ r} :=
  lowerSemicontinuous_iff_IsClosed_sublevel.mp hf

theorem LowerSemicontinuous.IsClosed_epigraph {f : E → F} (hf : LowerSemicontinuous f) :
    IsClosed {p : E × F | f p.1 ≤ p.2} :=
  lowerSemicontinuous_iff_IsClosed_epigraph.mp hf
