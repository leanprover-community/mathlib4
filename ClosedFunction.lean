/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wanyi He
-/
import Mathlib.Topology.Sequences
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal

/-!
# Closedness and Semicontinuity
A function `f` from a topolofical space `E` to `EReal` is said to be closed if its epigraph is closed.
Equivalently, `f` is closed if all its sublevel sets are closed.

## Main definitions and results

We introduce 2 definitions related to closed function:
* `ClosedOn f s`
* `Closed f`

We prove the equivalance of semi-continuity, closed functions and closedness of sublevel set.
* `closed_iff_IsClosed_sublevel`: a function is closed if and only if all its sublevel sets are closed.
* `closed_iff_LowerSemicontinuous`: a function is closed if and only if it is lower semi-continuous.
* `lowerSemicontinuous_iff_IsClosed_sublevel`: 
  a function is lower semi-continuous if and only if all its sublevel sets are closed.

## Implementation details

Although Mathlib4 already has a definition of semi-continuity, this file uses a more natural 
definition in mathematics when proving the equivalence of semi-continuity and closed functions.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>

-/


open Topology Filter Set TopologicalSpace

variable {E α β ι : Type _}

variable [AddCommMonoid E]

variable {s t : Set E} {f : E → EReal}

variable [TopologicalSpace E] [FirstCountableTopology E]

/-- A function `f : E → EReal` is said to be closed on a set `s` if its epigraph 
`{p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}` is closed on `s`. -/
def ClosedOn (f : E → EReal) (s : Set E) : Prop :=
  IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2}

/-- A function `f : E → EReal` is said to be closed if its epigraph 
`{p : E × EReal | f p.1 ≤ p.2}` is closed. -/
def Closed (f : E → EReal) : Prop := 
  IsClosed {p : E × EReal | f p.1 ≤ p.2}

theorem ClosedOn.closed_epigraph (hf : ClosedOn f s) : 
  IsClosed {p : E × EReal | p.1 ∈ s ∧ f p.1 ≤ p.2} := hf

theorem Closed.closed_epigraph (hf : Closed f) :
  IsClosed {p : E × EReal | f p.1 ≤ p.2} := hf

theorem closed_univ_iff : ClosedOn f univ ↔ Closed f := by 
  simp [ClosedOn, Closed]

/-!
### Equivalence
-/

theorem Closed.isClosed_sublevel {f : E → EReal} (hf : Closed f) :
    ∀ (r : EReal), IsClosed {x | f x ≤ r} :=
  fun _ => IsSeqClosed.isClosed fun ⦃_⦄ ⦃_⦄ xns cx =>
    IsClosed.isSeqClosed hf (fun n => xns n) (Tendsto.prod_mk_nhds cx tendsto_const_nhds)

theorem LowerSemicontinuous.Closed {f : E → EReal}
    (hf : ∀ x, f x ≤ (liminf f <| 𝓝 x)) : Closed f := by
  apply IsSeqClosed.isClosed
  intro f' ⟨x', y'⟩ hxy cxy
  rw [Prod.tendsto_iff] at cxy
  let x : ℕ -> E := fun (n : ℕ) => (f' n).1
  have xley : ∀ (n : ℕ), (f ∘ x) n ≤ (f' n).snd :=
    fun n => by convert hxy n
  calc
    f x' ≤ liminf f (𝓝 x') := hf x'
    _ ≤ liminf (f ∘ x) atTop := by
      rw[liminf_eq, liminf_eq]
      exact sSup_le_sSup (fun _ fa => (eventually_iff_seq_eventually.mp fa) x cxy.1)
    _ ≤ liminf (fun (n : ℕ) => (f' n).2) atTop := liminf_le_liminf (eventually_of_forall xley)
    _ = y' := (cxy.2).liminf_eq

theorem lowerSemicontinuous_of_isClosed_sublevel {f : E → EReal}
    (h : ∀ r : EReal, IsClosed {x | f x ≤ r}) :
    ∀ x , f x ≤ (liminf f <| 𝓝 x) := by
  by_contra h; push_neg at h
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

/-- A function is closed if and only if all its sublevel sets are closed. -/
theorem closed_iff_IsClosed_sublevel {f : E → EReal} :
    Closed f ↔ ∀ (r : EReal), IsClosed {x | f x ≤ r} :=
  ⟨fun h => Closed.isClosed_sublevel h,
    fun h => LowerSemicontinuous.Closed fun x => lowerSemicontinuous_of_isClosed_sublevel h x⟩

/-- A function is closed if and only if it is lower semi-continuous. -/
theorem closed_iff_LowerSemicontinuous {f : E → EReal} :
    Closed f ↔ ∀ x, f x ≤ (liminf f <| 𝓝 x) :=
  ⟨fun h => lowerSemicontinuous_of_isClosed_sublevel fun _ => Closed.isClosed_sublevel h _,
    fun a => LowerSemicontinuous.Closed a⟩

/-- A function is lower semi-continuous if and only if all its sublevel sets are closed. -/
theorem lowerSemicontinuous_iff_IsClosed_sublevel {f : E → EReal} :
    (∀ x , f x ≤ (liminf f <| 𝓝 x)) ↔ ∀ (r : EReal), IsClosed {x | f x ≤ r} :=
  ⟨fun H => Closed.isClosed_sublevel (LowerSemicontinuous.Closed H),
    fun a _ => lowerSemicontinuous_of_isClosed_sublevel a _⟩

theorem ClosedOn.isClosed_sublevel {f : E → EReal} {s : Set E} (hf : ClosedOn f s) :
    ∀ (r : EReal), IsClosed {x | x ∈ s ∧ f x ≤ r} :=
  fun _ => IsSeqClosed.isClosed fun ⦃_⦄ ⦃_⦄ xns cx =>
    IsClosed.isSeqClosed hf (fun n => xns n) (Tendsto.prod_mk_nhds cx tendsto_const_nhds)

theorem LowerSemicontinuousOn.ClosedOn {f : E → EReal} {s : Set E}
    (hs : IsClosed s) (hf : ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x)) :
    ClosedOn f s:= by
  apply IsSeqClosed.isClosed
  intro f' ⟨x', y'⟩ hxy cxy
  rw [Prod.tendsto_iff] at cxy
  let x : ℕ -> E := fun (n : ℕ) => (f' n).1
  have h1 := isSeqClosed_iff_isClosed.mpr hs (fun n => (hxy n).1) cxy.1
  constructor
  · exact h1
  obtain cx := tendsto_nhdsWithin_iff.mpr ⟨cxy.1, eventually_of_forall (fun n => (hxy n).1)⟩
  obtain xley :=
    fun n => Trans.trans (Trans.trans (Eq.refl ((f ∘ x) n)) (hxy n).2) (Eq.refl (f' n).2)
  calc
      f x' ≤ liminf f (𝓝[s] x') := hf x' h1
      _ ≤ liminf (f ∘ x) atTop := by
        rw [liminf_eq, liminf_eq]
        exact sSup_le_sSup
          fun _ fa => (eventually_iff_seq_eventually.mp (mem_setOf.mp fa)) x cx
      _ ≤ liminf (fun (n : ℕ) => (f' n).2) atTop := liminf_le_liminf (eventually_of_forall xley)
      _ = y' := (cxy.2).liminf_eq

theorem lowerSemicontinuousOn_of_isClosed_sublevel {f : E → EReal} {s : Set E}
  (h : ∀ r : EReal, IsClosed {x | x ∈ s ∧ f x ≤ r}) :
    ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x) := by
      by_contra h; push_neg at h
      obtain ⟨x, ⟨_, hx⟩⟩ := h
      obtain ⟨t, ⟨ltt, tlt⟩⟩ := exists_between hx
      have : x ∈ {x | x ∈ s ∧ f x ≤ t} := by
        apply isClosed_iff_frequently.mp (h t) x
        apply frequently_iff.mpr; intro _ hu
        have h : ∃ᶠ (y : E) in 𝓝[s] x, f y ≤ t := by
          apply frequently_iff.mpr; intro _ hu
          obtain ⟨x, xu, fx⟩ :=
            (frequently_iff.mp (frequently_lt_of_liminf_lt (by isBoundedDefault) ltt)) hu
          exact Exists.intro x ⟨xu, LT.lt.le fx⟩
        obtain ⟨x, xu, fx, xs⟩ := (frequently_iff.mp (frequently_nhdsWithin_iff.mp h)) hu
        exact Exists.intro x ⟨xu, ⟨xs, fx⟩⟩
      apply not_le_of_gt tlt this.2

theorem closedOn_iff_IsClosed_sublevel {f : E → EReal} {s : Set E} (hs : IsClosed s):
    ClosedOn f s ↔ ∀ (r : EReal), IsClosed {x | x ∈ s ∧ f x ≤ r} :=
  ⟨fun h _ => ClosedOn.isClosed_sublevel h _,
    fun h => LowerSemicontinuousOn.ClosedOn hs
      fun x xs => lowerSemicontinuousOn_of_isClosed_sublevel h x xs⟩

theorem closedOn_iff_LowerSemicontinuousOn {f : E → EReal} {s : Set E} (hs : IsClosed s):
    ClosedOn f s ↔ ∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x) :=
  ⟨fun H => lowerSemicontinuousOn_of_isClosed_sublevel fun _ => ClosedOn.isClosed_sublevel H _,
    fun h => LowerSemicontinuousOn.ClosedOn hs h⟩

theorem lowerSemicontinuousOn_iff_IsClosed_sublevel {f : E → EReal} {s : Set E} (hs : IsClosed s) : 
    (∀ x ∈ s, f x ≤ (liminf f <| 𝓝[s] x)) ↔ ∀ (r : EReal), IsClosed {x | x ∈ s ∧ f x ≤ r} :=
  ⟨fun H => ClosedOn.isClosed_sublevel (LowerSemicontinuousOn.ClosedOn hs H),
    fun a _ => lowerSemicontinuousOn_of_isClosed_sublevel a _⟩

/-- If `f : E → EReal` is continuous and `s` is closed, then `f` is closed on `s`. -/ 
theorem ContinuousOn.isClosedFun {f : E → EReal} {s : Set E}
    (hs : IsClosed s) (hf : ContinuousOn f s) :
  ClosedOn f s := IsClosed.epigraph hs hf