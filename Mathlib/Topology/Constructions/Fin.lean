/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Constructions

/-!
# Pi types and finiteness
-/

open scoped Topology

universe u v u' v'
variable {X : Type u} {Y : Type v} {Z W ε ζ : Type*} [TopologicalSpace X]

section Fin

variable {n : ℕ} {π : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (π i)]

theorem Filter.Tendsto.finCons
    {f : Y → π 0} {g : Y → ∀ j : Fin n, π j.succ} {l : Filter Y} {x : π 0} {y : ∀ j, π (Fin.succ j)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.cons (f a) (g a)) l (𝓝 <| Fin.cons x y) :=
  tendsto_pi_nhds.2 fun j => Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

theorem ContinuousAt.finCons {f : X → π 0} {g : X → ∀ j : Fin n, π (Fin.succ j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.cons (f a) (g a)) x :=
  hf.tendsto.finCons hg

theorem Continuous.finCons {f : X → π 0} {g : X → ∀ j : Fin n, π (Fin.succ j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.cons (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt

variable [TopologicalSpace Z]

theorem Filter.Tendsto.matrixVecCons
    {f : Y → Z} {g : Y → Fin n → Z} {l : Filter Y} {x : Z} {y : Fin n → Z}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Matrix.vecCons (f a) (g a)) l (𝓝 <| Matrix.vecCons x y) :=
  hf.finCons hg

theorem ContinuousAt.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Matrix.vecCons (f a) (g a)) x :=
  hf.finCons hg

theorem Continuous.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => Matrix.vecCons (f a) (g a) :=
  hf.finCons hg

theorem Filter.Tendsto.finSnoc
    {f : Y → ∀ j : Fin n, π j.castSucc} {g : Y → π (Fin.last _)}
    {l : Filter Y} {x : ∀ j, π (Fin.castSucc j)} {y : π (Fin.last _)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.snoc (f a) (g a)) l (𝓝 <| Fin.snoc x y) :=
  tendsto_pi_nhds.2 fun j => Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

theorem ContinuousAt.finSnoc {f : X → ∀ j : Fin n, π j.castSucc} {g : X → π (Fin.last _)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.snoc (f a) (g a)) x :=
  hf.tendsto.finSnoc hg

theorem Continuous.finSnoc {f : X → ∀ j : Fin n, π j.castSucc} {g : X → π (Fin.last _)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.snoc (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finSnoc hg.continuousAt

theorem Filter.Tendsto.finInsertNth
    (i : Fin (n + 1)) {f : Y → π i} {g : Y → ∀ j : Fin n, π (i.succAbove j)} {l : Filter Y}
    {x : π i} {y : ∀ j, π (i.succAbove j)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[deprecated (since := "2025-01-02")]
alias Filter.Tendsto.fin_insertNth := Filter.Tendsto.finInsertNth

theorem ContinuousAt.finInsertNth
    (i : Fin (n + 1)) {f : X → π i} {g : X → ∀ j : Fin n, π (i.succAbove j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) x :=
  hf.tendsto.finInsertNth i hg

@[deprecated (since := "2025-01-02")]
alias ContinuousAt.fin_insertNth := ContinuousAt.finInsertNth

theorem Continuous.finInsertNth
    (i : Fin (n + 1)) {f : X → π i} {g : X → ∀ j : Fin n, π (i.succAbove j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInsertNth i hg.continuousAt

@[deprecated (since := "2025-01-02")]
alias Continuous.fin_insertNth := Continuous.finInsertNth

end Fin
