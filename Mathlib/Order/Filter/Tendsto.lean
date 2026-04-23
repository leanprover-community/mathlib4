/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.Attr.Core
import Batteries.Tactic.Init
import Mathlib.Data.Set.Insert
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive

/-!
# Convergence in terms of filters

The general notion of limit of a map with respect to filters on the source and target types
is `Filter.Tendsto`. It is defined in terms of the order and the push-forward operation.

For instance, anticipating on Topology.Basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from `Topology/Basic`.
-/

public section

open Set Filter

variable {α β γ : Type*} {ι : Sort*}

namespace Filter

theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl

theorem tendsto_iff_eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ ⦃p : β → Prop⦄, (∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x) :=
  Iff.rfl

theorem tendsto_iff_forall_eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, ∀ᶠ x in l₁, f x ∈ s :=
  Iff.rfl

lemma Tendsto.eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β}
    (hf : Tendsto f l₁ l₂) (h : s ∈ l₂) : ∀ᶠ x in l₁, f x ∈ s :=
  hf h

theorem Tendsto.eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) :=
  hf h

theorem not_tendsto_iff_exists_frequently_notMem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    ¬Tendsto f l₁ l₂ ↔ ∃ s ∈ l₂, ∃ᶠ x in l₁, f x ∉ s := by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]

theorem Tendsto.frequently {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∃ᶠ x in l₁, p (f x)) : ∃ᶠ y in l₂, p y :=
  mt hf.eventually h

theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop}
    (f : α → β) (c : Filter.Tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) :
    ∃ᶠ y in l₂, q y :=
  c.frequently (h.mono w)

@[simp]
theorem tendsto_bot {f : α → β} {l : Filter β} : Tendsto f ⊥ l := by simp [Tendsto]

theorem Tendsto.of_neBot_imp {f : α → β} {la : Filter α} {lb : Filter β}
    (h : NeBot la → Tendsto f la lb) : Tendsto f la lb := by
  rcases eq_or_neBot la with rfl | hla
  · exact tendsto_bot
  · exact h hla

@[simp] theorem tendsto_top {f : α → β} {l : Filter α} : Tendsto f l ⊤ := le_top

theorem le_map_of_right_inverse {mab : α → β} {mba : β → α} {f : Filter α} {g : Filter β}
    (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tendsto mba g f) : g ≤ map mab f := by
  rw [← @map_id _ g, ← map_congr h₁, ← map_map]
  exact map_mono h₂

theorem tendsto_of_isEmpty [IsEmpty α] {f : α → β} {la : Filter α} {lb : Filter β} :
    Tendsto f la lb := by simp only [filter_eq_bot_of_isEmpty la, tendsto_bot]

theorem eventuallyEq_of_left_inv_of_right_inv {f : α → β} {g₁ g₂ : β → α} {fa : Filter α}
    {fb : Filter β} (hleft : ∀ᶠ x in fa, g₁ (f x) = x) (hright : ∀ᶠ y in fb, f (g₂ y) = y)
    (htendsto : Tendsto g₂ fb fa) : g₁ =ᶠ[fb] g₂ :=
  (htendsto.eventually hleft).mp <| hright.mono fun _ hr hl => (congr_arg g₁ hr.symm).trans hl

theorem tendsto_iff_comap {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
  map_le_iff_le_comap

alias ⟨Tendsto.le_comap, _⟩ := tendsto_iff_comap

protected theorem Tendsto.disjoint {f : α → β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β}
    (h₁ : Tendsto f la₁ lb₁) (hd : Disjoint lb₁ lb₂) (h₂ : Tendsto f la₂ lb₂) : Disjoint la₁ la₂ :=
  (disjoint_comap hd).mono h₁.le_comap h₂.le_comap

theorem tendsto_congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ := by rw [Tendsto, Tendsto, map_congr hl]

theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
    (h : Tendsto f₁ l₁ l₂) : Tendsto f₂ l₁ l₂ :=
  (tendsto_congr' hl).1 h

theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem' h)

theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂ :=
  (tendsto_congr h).1

theorem tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x ≤ y :=
  Iff.rfl

theorem tendsto_id {x : Filter α} : Tendsto id x x :=
  le_refl x

theorem Tendsto.comp {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
    (hg : Tendsto g y z) (hf : Tendsto f x y) : Tendsto (g ∘ f) x z := fun _ hs => hf (hg hs)

protected theorem Tendsto.iterate {f : α → α} {l : Filter α} (h : Tendsto f l l) :
    ∀ n, Tendsto (f^[n]) l l
  | 0 => tendsto_id
  | (n + 1) => (h.iterate n).comp h

theorem Tendsto.mono_left {f : α → β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z)
    (h : y ≤ x) : Tendsto f y z :=
  (map_mono h).trans hx

theorem Tendsto.mono_right {f : α → β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y)
    (hz : y ≤ z) : Tendsto f x z :=
  le_trans hy hz

theorem Tendsto.neBot {f : α → β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x] :
    NeBot y :=
  (hx.map _).mono h

theorem tendsto_map {f : α → β} {x : Filter α} : Tendsto f x (map f x) :=
  le_refl (map f x)

@[simp]
theorem tendsto_map'_iff {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ} :
    Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y := by
  rw [Tendsto, Tendsto, map_map]

alias ⟨_, tendsto_map'⟩ := tendsto_map'_iff

theorem tendsto_comap {f : α → β} {x : Filter β} : Tendsto f (comap f x) x :=
  map_comap_le

@[simp]
theorem tendsto_comap_iff {f : α → β} {g : β → γ} {a : Filter α} {c : Filter γ} :
    Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c :=
  ⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp <| by rwa [map_map]⟩

theorem tendsto_comap'_iff {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α} (h : range i ∈ f) :
    Tendsto (m ∘ i) (comap i f) g ↔ Tendsto m f g := by
  rw [Tendsto, ← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, Tendsto]

theorem Tendsto.of_tendsto_comp {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ}
    (hfg : Tendsto (g ∘ f) a c) (hg : comap g c ≤ b) : Tendsto f a b := by
  rw [tendsto_iff_comap] at hfg ⊢
  calc
    a ≤ comap (g ∘ f) c := hfg
    _ ≤ comap f b := by simpa [comap_comap] using comap_mono hg

theorem comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : ψ ∘ φ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : comap φ g = f := by
  refine ((comap_mono <| map_le_iff_le_comap.1 hψ).trans ?_).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap, eq, comap_id]

theorem map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : φ ∘ ψ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : map φ f = g := by
  refine le_antisymm hφ (le_trans ?_ (map_mono hψ))
  rw [map_map, eq, map_id]

theorem tendsto_inf {f : α → β} {x : Filter α} {y₁ y₂ : Filter β} :
    Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂ := by
  simp only [Tendsto, le_inf_iff]

theorem tendsto_inf_left {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_left) h

theorem tendsto_inf_right {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_right) h

theorem Tendsto.inf {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁)
    (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
  tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp]
theorem tendsto_iInf {f : α → β} {x : Filter α} {y : ι → Filter β} :
    Tendsto f x (⨅ i, y i) ↔ ∀ i, Tendsto f x (y i) := by
  simp only [Tendsto, le_iInf_iff]

theorem tendsto_iInf' {f : α → β} {x : ι → Filter α} {y : Filter β} (i : ι)
    (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y :=
  hi.mono_left <| iInf_le _ _

theorem tendsto_iInf_iInf {f : α → β} {x : ι → Filter α} {y : ι → Filter β}
    (h : ∀ i, Tendsto f (x i) (y i)) : Tendsto f (iInf x) (iInf y) :=
  tendsto_iInf.2 fun i => tendsto_iInf' i (h i)

@[simp]
theorem tendsto_sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y := by
  simp only [Tendsto, map_sup, sup_le_iff]

theorem Tendsto.sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f x₁ y → Tendsto f x₂ y → Tendsto f (x₁ ⊔ x₂) y := fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩

theorem Tendsto.sup_sup {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β}
    (h₁ : Tendsto f x₁ y₁) (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊔ x₂) (y₁ ⊔ y₂) :=
  tendsto_sup.mpr ⟨h₁.mono_right le_sup_left, h₂.mono_right le_sup_right⟩

@[simp]
theorem tendsto_iSup {f : α → β} {x : ι → Filter α} {y : Filter β} :
    Tendsto f (⨆ i, x i) y ↔ ∀ i, Tendsto f (x i) y := by simp only [Tendsto, map_iSup, iSup_le_iff]

theorem tendsto_iSup_iSup {f : α → β} {x : ι → Filter α} {y : ι → Filter β}
    (h : ∀ i, Tendsto f (x i) (y i)) : Tendsto f (iSup x) (iSup y) :=
  tendsto_iSup.2 fun i => (h i).mono_right <| le_iSup _ _

@[simp] theorem tendsto_principal {f : α → β} {l : Filter α} {s : Set β} :
    Tendsto f l (𝓟 s) ↔ ∀ᶠ a in l, f a ∈ s := by
  simp only [Tendsto, le_principal_iff, mem_map', Filter.Eventually]

theorem tendsto_principal_principal {f : α → β} {s : Set α} {t : Set β} :
    Tendsto f (𝓟 s) (𝓟 t) ↔ ∀ a ∈ s, f a ∈ t := by
  simp

@[simp] theorem tendsto_pure {f : α → β} {a : Filter α} {b : β} :
    Tendsto f a (pure b) ↔ ∀ᶠ x in a, f x = b := by
  simp only [Tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]

theorem tendsto_pure_pure (f : α → β) (a : α) : Tendsto f (pure a) (pure (f a)) :=
  tendsto_pure.2 rfl

theorem tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun _ => b) a (pure b) :=
  tendsto_pure.2 <| univ_mem' fun _ => rfl

theorem pure_le_iff {a : α} {l : Filter α} : pure a ≤ l ↔ ∀ s ∈ l, a ∈ s :=
  Iff.rfl

theorem tendsto_pure_left {f : α → β} {a : α} {l : Filter β} :
    Tendsto f (pure a) l ↔ ∀ s ∈ l, f a ∈ s :=
  Iff.rfl

@[simp]
theorem map_inf_principal_preimage {f : α → β} {s : Set β} {l : Filter α} :
    map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s :=
  Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_setOf_eq, mem_preimage]

/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
theorem Tendsto.not_tendsto {f : α → β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁)
    [NeBot a] (hb : Disjoint b₁ b₂) : ¬Tendsto f a b₂ := fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).neBot.ne hb.eq_bot

protected theorem Tendsto.if {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {p : α → Prop}
    [∀ x, Decidable (p x)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 { x | p x }) l₂)
    (h₁ : Tendsto g (l₁ ⊓ 𝓟 { x | ¬p x }) l₂) :
    Tendsto (fun x => if p x then f x else g x) l₁ l₂ := by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs] with x hp₀ hp₁
  rw [mem_preimage]
  split_ifs with h
  exacts [hp₀ h, hp₁ h]

protected theorem Tendsto.if' {α β : Type*} {l₁ : Filter α} {l₂ : Filter β} {f g : α → β}
    {p : α → Prop} [DecidablePred p] (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₁ l₂) :
    Tendsto (fun a => if p a then f a else g a) l₁ l₂ :=
  (tendsto_inf_left hf).if (tendsto_inf_left hg)

protected theorem Tendsto.piecewise {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {s : Set α}
    [∀ x, Decidable (x ∈ s)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 s) l₂) (h₁ : Tendsto g (l₁ ⊓ 𝓟 sᶜ) l₂) :
    Tendsto (piecewise s f g) l₁ l₂ :=
  Tendsto.if h₀ h₁

end Filter

theorem Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t) :
    Filter.Tendsto f (𝓟 s) (𝓟 t) :=
  Filter.tendsto_principal_principal.2 h

theorem Filter.EventuallyEq.comp_tendsto {l : Filter α} {f : α → β} {f' : α → β}
    (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ} (hg : Tendsto g lc l) :
    f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.eventually H

variable {F : Filter α} {G : Filter β}

theorem Filter.map_mapsTo_Iic_iff_tendsto {m : α → β} :
    MapsTo (map m) (Iic F) (Iic G) ↔ Tendsto m F G :=
  ⟨fun hm ↦ hm self_mem_Iic, fun hm _ ↦ hm.mono_left⟩

alias ⟨_, Filter.Tendsto.map_mapsTo_Iic⟩ := Filter.map_mapsTo_Iic_iff_tendsto

theorem Filter.map_mapsTo_Iic_iff_mapsTo {s : Set α} {t : Set β} {m : α → β} :
    MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ MapsTo m s t := by
  rw [map_mapsTo_Iic_iff_tendsto, tendsto_principal_principal, MapsTo]

alias ⟨_, Set.MapsTo.filter_map_Iic⟩ := Filter.map_mapsTo_Iic_iff_mapsTo
