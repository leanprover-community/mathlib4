/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Convex.EGauge
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Asymptotics in a Topological Vector Space

This file defines `Asymptotics.IsLittleOTVS`, `Asymptotics.IsBigOTVS`, and `Asymptotics.IsThetaTVS`
as generalizations of `Asymptotics.IsLittleO`, `Asymptotics.IsBigO`, and `Asymptotics.IsTheta`
from normed spaces to topological vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ (resp., $f = O(g)$)
if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g(x)))$
(resp., $\operatorname{gauge}_{K, U} (f(x)) = O(\operatorname{gauge}_{K, V} (g(x)))$),
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

We say that $f=Θ(g)$, if both $f=O(g)$ and $g=O(f)$.

In a normed space, we can use balls of positive radius as both `U` and `V`,
thus reducing the definition to the classical one.

These modifications of the definitions free the user from having to chose a canonical norm,
at the expense of having to pick a specific base field.
This is exactly the tradeoff we want in `HasFDerivAtFilter`,
as there the base field is already chosen,
and this removes the choice of norm being part of the statement.

These definitions were added to the library in order to migrate Fréchet derivatives
from normed vector spaces to topological vector spaces.
The definitions are motivated by
https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative#Generalization_to_topological_vector_spaces
but the definition there doesn't work for topological vector spaces over general normed fields.
[This Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/generalizing.20deriv.20to.20TVS)
led to the current choice of the definition of `Asymptotics.IsLittleOTVS`,
and `Asymptotics.IsBigOTVS` was defined in a similar manner.

## Main results

* `isLittleOTVS_iff_isLittleO`: the equivalence between these two definitions in the case of a
  normed space.

* `isLittleOTVS_iff_tendsto_inv_smul`: the equivalence to convergence of the ratio to zero
  in case of a topological vector space.

## TODO

- Add `Asymptotics.IsEquivalentTVS`.
- Prove a version of `Asymptotics.isBigO_one` for `IsBigOTVS`.

-/

@[expose] public section

open Set Filter Asymptotics Metric Topology
open scoped Topology Pointwise ENNReal NNReal

namespace Asymptotics

section Defs

variable (𝕜 : Type*) {α E F : Type*}
  [ENorm 𝕜] [TopologicalSpace E] [TopologicalSpace F] [Zero E] [Zero F] [SMul 𝕜 E] [SMul 𝕜 F]

/-- `f =o[𝕜; l] g` (`IsLittleOTVS 𝕜 l f g`) is a generalization of `f =o[l] g` (`IsLittleO l f g`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `K`,
we say that $f = o(g)$ if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) = o(\operatorname{gauge}_{K, V} (g(x)))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.

We use an `ENNReal`-valued function `egauge` for the gauge,
so we unfold the definition of little o instead of reusing it. -/
@[mk_iff]
structure IsLittleOTVS (l : Filter α) (f : α → E) (g : α → F) : Prop where
  exists_eventuallyLE_mul : ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ (0 : ℝ≥0),
    (fun x ↦ egauge 𝕜 U (f x)) ≤ᶠ[l] (fun x ↦ ε * egauge 𝕜 V (g x))

@[inherit_doc]
notation:100 f " =o[" 𝕜 "; " l "] " g:100 => IsLittleOTVS 𝕜 l f g

/-- `f =O[𝕜; l] g` (`IsBigOTVS 𝕜 l f g`) is a generalization of `f =O[l] g` (`IsBigO l f g`)
that works in topological `𝕜`-vector spaces.

Given two functions `f` and `g` taking values in topological vector spaces
over a normed field `𝕜`,
we say that $f = O(g)$ if for any neighborhood of zero `U` in the codomain of `f`
there exists a neighborhood of zero `V` in the codomain of `g`
such that $\operatorname{gauge}_{K, U} (f(x)) \le \operatorname{gauge}_{K, V} (g(x))$,
where $\operatorname{gauge}_{K, U}(y) = \inf \{‖c‖ \mid y ∈ c • U\}$.
-/
@[mk_iff]
structure IsBigOTVS (l : Filter α) (f : α → E) (g : α → F) : Prop where
  exists_eventuallyLE : ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F),
    (egauge 𝕜 U <| f ·) ≤ᶠ[l] (egauge 𝕜 V <| g ·)

@[inherit_doc]
notation:100 f " =O[" 𝕜 "; " l "] " g:100 => IsBigOTVS 𝕜 l f g

/-- We say that `f =Θ[𝕜; l] g` (`IsThetaTVS 𝕜 l f g`), if `f =O[𝕜; l] g` and `g =O[𝕜; l] f`.
It is a generalization of `f =Θ[l] g` that works in topological `𝕜`-vector spaces. -/
def IsThetaTVS (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  (f =O[𝕜; l] g) ∧ (g =O[𝕜; l] f)

@[inherit_doc]
notation:100 f " =Θ[" 𝕜 "; " l "] " g:100 => IsThetaTVS 𝕜 l f g

end Defs

variable {α β 𝕜 E F G : Type*}

section TopologicalSpace

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

section congr

variable {f f₁ f₂ : α → E} {g g₁ g₂ : α → F} {l : Filter α}

theorem isLittleOTVS_iff_tendsto_div :
    f =o[𝕜; l] g ↔ ∀ U ∈ 𝓝 0, ∃ V ∈ 𝓝 0,
      Tendsto (fun x ↦ egauge 𝕜 U (f x) / egauge 𝕜 V (g x)) l (𝓝 0) := by
  simp only [isLittleOTVS_iff, ← ENNReal.coe_zero, ENNReal.nhds_coe, ← NNReal.bot_eq_zero,
    (nhds_bot_basis_Iic.map _).tendsto_right_iff]
  simp +contextual [ENNReal.div_le_iff_le_mul, pos_iff_ne_zero, EventuallyLE]

alias ⟨IsLittleOTVS.tendsto_div, IsLittleOTVS.of_tendsto_div⟩ := isLittleOTVS_iff_tendsto_div

/-- A version of `IsLittleOTVS.exists_eventuallyLE_mul`
where `ε` is quantified over `ℝ≥0∞` instead of `ℝ≥0`. -/
theorem IsLittleOTVS.exists_eventuallyLE_mul_ennreal (h : f =o[𝕜; l] g) {U : Set E} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ 0, (fun x ↦ egauge 𝕜 U (f x)) ≤ᶠ[l] (fun x ↦ ε * egauge 𝕜 V (g x)) := by
  obtain ⟨V, hV₀, hV⟩ := h.exists_eventuallyLE_mul U hU
  refine ⟨V, hV₀, fun ε hε ↦ ?_⟩
  cases ε with
  | top => exact (hV 1 one_ne_zero).trans <| .of_forall fun _ ↦ by dsimp; grw [← le_top]
  | coe ε => exact hV ε (mod_cast hε)

theorem isLittleOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =o[𝕜; l] g₁ ↔ f₂ =o[𝕜; l] g₂ := by
  simp only [isLittleOTVS_iff_tendsto_div]
  peel with U hU V hV
  exact tendsto_congr' (hf.comp₂ (egauge _ _ · / egauge _ _ ·) hg)

/-- A stronger version of `IsLittleOTVS.congr` that requires the functions only agree along the
filter. -/
theorem IsLittleOTVS.congr' (h : f₁ =o[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =o[𝕜; l] g₂ :=
  (isLittleOTVS_congr hf hg).mp h

theorem IsLittleOTVS.congr (h : f₁ =o[𝕜; l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[𝕜; l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsLittleOTVS.congr_left (h : f₁ =o[𝕜; l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[𝕜; l] g :=
  h.congr hf fun _ ↦ rfl

theorem IsLittleOTVS.congr_right (h : f =o[𝕜; l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[𝕜; l] g₂ :=
  h.congr (fun _ ↦ rfl) hg

theorem isBigOTVS_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₁ =O[𝕜; l] g₁ ↔ f₂ =O[𝕜; l] g₂ := by
  simp only [isBigOTVS_iff]
  peel with U hU V hV
  exact eventuallyLE_congr (hf.fun_comp (egauge 𝕜 U)) (hg.fun_comp (egauge 𝕜 V))

/-- A stronger version of `IsBigOTVS.congr` that requires the functions only agree along the
filter. -/
theorem IsBigOTVS.congr' (h : f₁ =O[𝕜; l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    f₂ =O[𝕜; l] g₂ :=
  (isBigOTVS_congr hf hg).mp h

theorem IsBigOTVS.congr (h : f₁ =O[𝕜; l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[𝕜; l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsBigOTVS.congr_left (h : f₁ =O[𝕜; l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[𝕜; l] g :=
  h.congr hf fun _ ↦ rfl

theorem IsBigOTVS.congr_right (h : f =O[𝕜; l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[𝕜; l] g₂ :=
  h.congr (fun _ ↦ rfl) hg

end congr

variable {l l₁ l₂ : Filter α} {f : α → E} {g : α → F}

protected theorem IsBigOTVS.refl (f : α → E) (l : Filter α) : f =O[𝕜; l] f := by
  rw [isBigOTVS_iff]
  exact fun U hU ↦ ⟨U, hU, EventuallyLE.rfl⟩

protected theorem IsBigOTVS.rfl : f =O[𝕜; l] f := .refl f l

protected theorem IsThetaTVS.refl (f : α → E) (l : Filter α) : f =Θ[𝕜; l] f :=
  ⟨.rfl, .rfl⟩

protected theorem IsThetaTVS.rfl : f =Θ[𝕜; l] f := .refl f l

theorem IsLittleOTVS.isBigOTVS (h : f =o[𝕜; l] g) : f =O[𝕜; l] g := by
  refine ⟨fun U hU ↦ ?_⟩
  rcases h.1 U hU with ⟨V, hV₀, hV⟩
  use V, hV₀
  simpa using hV 1 one_ne_zero

theorem IsThetaTVS.isBigOTVS (h : f =Θ[𝕜; l] g) : f =O[𝕜; l] g := h.left

@[symm]
theorem IsThetaTVS.symm (h : f =Θ[𝕜; l] g) : g =Θ[𝕜; l] f := And.symm h

theorem isThetaTVS_comm : f =Θ[𝕜; l] g ↔ g =Θ[𝕜; l] f := and_comm

/-!
### Transitivity lemmas
-/

section Trans

variable {k : α → G}

@[trans]
theorem IsBigOTVS.trans (hfg : f =O[𝕜; l] g) (hgk : g =O[𝕜; l] k) : f =O[𝕜; l] k := by
  refine ⟨fun U hU₀ ↦ ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, ?_⟩
  filter_upwards [hV, hW] with x hx₁ hx₂ using hx₁.trans hx₂

instance instTransIsBigOTVSIsBigOTVS :
    @Trans (α → E) (α → F) (α → G) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsBigOTVS.trans

theorem IsBigOTVS.trans_isThetaTVS (hfg : f =O[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) :
    f =O[𝕜; l] k :=
  hfg.trans hgk.isBigOTVS

instance instTransIsBigOTVSIsThetaTVS :
    @Trans (α → E) (α → F) (α → G) (IsBigOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsBigOTVS.trans_isThetaTVS

theorem IsThetaTVS.trans_isBigOTVS (hfg : f =Θ[𝕜; l] g) (hgk : g =O[𝕜; l] k) :
    f =O[𝕜; l] k :=
  hfg.isBigOTVS.trans hgk

instance instTransIsThetaOTVSIsBigOTVS :
    @Trans (α → E) (α → F) (α → G) (IsThetaTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsBigOTVS 𝕜 l) where
  trans := IsThetaTVS.trans_isBigOTVS

@[trans]
theorem IsThetaTVS.trans (hfg : f =Θ[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) : f =Θ[𝕜; l] k :=
  ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩

instance instTransIsThetaOTVS :
    @Trans (α → E) (α → F) (α → G) (IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsThetaTVS 𝕜 l) where
  trans := IsThetaTVS.trans

theorem IsLittleOTVS.trans_isBigOTVS (hfg : f =o[𝕜; l] g) (hgk : g =O[𝕜; l] k) :
    f =o[𝕜; l] k := by
  refine ⟨fun U hU₀ ↦ ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε ↦ ?_⟩
  filter_upwards [hV ε hε, hW] with x hx₁ hx₂ using hx₁.trans <| by gcongr

instance instTransIsLittleOTVSIsBigOTVS :
    @Trans (α → E) (α → F) (α → G) (IsLittleOTVS 𝕜 l) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans_isBigOTVS

theorem IsLittleOTVS.trans_isThetaTVS (hfg : f =o[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) :
    f =o[𝕜; l] k :=
  hfg.trans_isBigOTVS hgk.isBigOTVS

instance instTransIsLittleOTVSIsThetaTVS :
    @Trans (α → E) (α → F) (α → G) (IsLittleOTVS 𝕜 l) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans_isThetaTVS

theorem IsBigOTVS.trans_isLittleOTVS (hfg : f =O[𝕜; l] g) (hgk : g =o[𝕜; l] k) :
    f =o[𝕜; l] k := by
  refine ⟨fun U hU₀ ↦ ?_⟩
  obtain ⟨V, hV₀, hV⟩ := hfg.1 U hU₀
  obtain ⟨W, hW₀, hW⟩ := hgk.1 V hV₀
  refine ⟨W, hW₀, fun ε hε ↦ ?_⟩
  filter_upwards [hV, hW ε hε] with x hx₁ hx₂ using hx₁.trans hx₂

instance instTransIsBigOTVSIsLittleOTVS :
    @Trans (α → E) (α → F) (α → G) (IsBigOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsBigOTVS.trans_isLittleOTVS

theorem IsThetaTVS.trans_isLittleOTVS (hfg : f =Θ[𝕜; l] g) (hgk : g =o[𝕜; l] k) :
    f =o[𝕜; l] k :=
  hfg.isBigOTVS.trans_isLittleOTVS hgk

instance instTransIsThetaTVSIsLittleOTVS :
    @Trans (α → E) (α → F) (α → G) (IsThetaTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsThetaTVS.trans_isLittleOTVS

@[trans]
theorem IsLittleOTVS.trans (hfg : f =o[𝕜; l] g) (hgk : g =o[𝕜; l] k) : f =o[𝕜; l] k :=
  hfg.trans_isBigOTVS hgk.isBigOTVS

instance instTransIsLittleOTVSIsLittleOTVS :
    @Trans (α → E) (α → F) (α → G) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) (IsLittleOTVS 𝕜 l) where
  trans := IsLittleOTVS.trans

end Trans

protected theorem _root_.Filter.HasBasis.isLittleOTVS_iff
    {ιE ιF : Sort*} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) :
    f =o[𝕜; l] g ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ ε * egauge 𝕜 (sF j) (g x) := by
  rw [isLittleOTVS_iff]
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε ↦ (h ε hε).mono fun x hx ↦ hx.trans ?_
    simp only
    gcongr

protected theorem _root_.Filter.HasBasis.isBigOTVS_iff
    {ιE ιF : Sort*} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) :
    f =O[𝕜; l] g ↔ ∀ i, pE i → ∃ j, pF j ∧
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ egauge 𝕜 (sF j) (g x) := by
  rw [isBigOTVS_iff]
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, hV.mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · exact fun s t hsub h ↦ h.mono fun x hx ↦ hx.trans <| egauge_anti 𝕜 hsub (g x)

/-- The definition of `IsBigOTVS` says that
for each neighborhood `U` of the origin in the codomain of `f`,
there exists a neighborhood `V` of the origin in the codomain of `g` such that
`egauge 𝕜 U (f x) ≤ egauge 𝕜 V (g x)` eventually along `l`.

This lemma shows that it suffices to make this inequality work up to a constant multiplier. -/
theorem IsBigOTVS.of_egauge_le_mul [ContinuousConstSMul 𝕜 F] {ι} {p : ι → Prop} {U : ι → Set E}
    (hb : (𝓝 0).HasBasis p U)
    (h : ∀ i, p i → ∃ C : ℝ≥0, ∃ V ∈ 𝓝 (0 : F),
      (egauge 𝕜 (U i) <| f ·) ≤ᶠ[l] (fun x ↦ C * egauge 𝕜 V (g x))) :
    f =O[𝕜; l] g := by
  rw [hb.isBigOTVS_iff (basis_sets _)]
  intro i hi
  rcases h i hi with ⟨C, V, hV₀, hV⟩
  rcases NormedField.exists_lt_nnnorm 𝕜 C with ⟨c, hc⟩
  have hc₀ : c ≠ 0 := by rintro rfl; simp at hc
  refine ⟨c⁻¹ • V, (set_smul_mem_nhds_zero_iff <| inv_ne_zero hc₀).mpr hV₀, ?_⟩
  refine hV.trans <| .of_forall fun x ↦ ?_
  simp only
  grw [hc]
  simp [egauge_smul_left, hc₀, enorm_eq_nnnorm, ENNReal.div_eq_inv_mul]

theorem isLittleOTVS_iff_smallSets :
    f =o[𝕜; l] g ↔ ∀ U ∈ 𝓝 0, ∀ᶠ V in (𝓝 0).smallSets, ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ ε * egauge 𝕜 V (g x) :=
  (isLittleOTVS_iff ..).trans <| forall₂_congr fun U hU ↦ .symm <|
    eventually_smallSets' fun V₁ V₂ hV hV₂ ε hε ↦ (hV₂ ε hε).mono fun x hx ↦ hx.trans <| by gcongr

alias ⟨IsLittleOTVS.eventually_smallSets, _⟩ := isLittleOTVS_iff_smallSets

theorem isBigOTVS_iff_smallSets :
    f =O[𝕜; l] g ↔ ∀ U ∈ 𝓝 0, ∀ᶠ V in (𝓝 0).smallSets,
      ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ egauge 𝕜 V (g x) :=
  (isBigOTVS_iff ..).trans <| forall₂_congr fun U hU ↦ .symm <|
    eventually_smallSets' fun V₁ V₂ hV hV₂ ↦ hV₂.mono fun x hx ↦ hx.trans <| by gcongr

alias ⟨IsBigOTVS.eventually_smallSets, _⟩ := isBigOTVS_iff_smallSets

@[simp]
theorem isLittleOTVS_map {k : β → α} {l : Filter β} :
    f =o[𝕜; map k l] g ↔ (f ∘ k) =o[𝕜; l] (g ∘ k) := by
  simp [isLittleOTVS_iff, EventuallyLE]

@[simp]
theorem isBigOTVS_map {k : β → α} {l : Filter β} :
    f =O[𝕜; map k l] g ↔ (f ∘ k) =O[𝕜; l] (g ∘ k) := by
  simp [isBigOTVS_iff, EventuallyLE]

lemma IsLittleOTVS.mono (hf : f =o[𝕜; l₁] g) (h : l₂ ≤ l₁) : f =o[𝕜; l₂] g :=
  ⟨fun U hU ↦ let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, fun ε hε ↦ (hV ε hε).filter_mono h⟩⟩

lemma IsBigOTVS.mono (hf : f =O[𝕜; l₁] g) (h : l₂ ≤ l₁) : f =O[𝕜; l₂] g :=
  ⟨fun U hU ↦ let ⟨V, hV0, hV⟩ := hf.1 U hU; ⟨V, hV0, hV.filter_mono h⟩⟩

lemma IsLittleOTVS.comp_tendsto {k : β → α} {lb : Filter β} (h : f =o[𝕜; l] g)
    (hk : Tendsto k lb l) : (f ∘ k) =o[𝕜; lb] (g ∘ k) :=
  isLittleOTVS_map.mp (h.mono hk)

lemma IsBigOTVS.comp_tendsto {k : β → α} {lb : Filter β} (h : f =O[𝕜; l] g)
    (hk : Tendsto k lb l) : (f ∘ k) =O[𝕜; lb] (g ∘ k) :=
  isBigOTVS_map.mp (h.mono hk)

lemma isLittleOTVS_sup : f =o[𝕜; l₁ ⊔ l₂] g ↔ f =o[𝕜; l₁] g ∧ f =o[𝕜; l₂] g := by
  simp only [isLittleOTVS_iff_smallSets, ← forall_and, ← eventually_and, eventually_sup]

lemma IsLittleOTVS.sup (hf₁ : f =o[𝕜; l₁] g) (hf₂ : f =o[𝕜; l₂] g) : f =o[𝕜; l₁ ⊔ l₂] g :=
  isLittleOTVS_sup.mpr ⟨hf₁, hf₂⟩

lemma _root_.ContinuousLinearMap.isBigOTVS_id {l : Filter E} (f : E →L[𝕜] F) : f =O[𝕜; l] id :=
  ⟨fun U hU ↦ ⟨f ⁻¹' U, (map_continuous f).tendsto' 0 0 (map_zero f) hU, .of_forall <|
    (mapsTo_preimage f U).egauge_le 𝕜 f⟩⟩

lemma _root_.ContinuousLinearMap.isBigOTVS_comp (g : E →L[𝕜] F) : (g ∘ f) =O[𝕜; l] f :=
  g.isBigOTVS_id.comp_tendsto tendsto_top

lemma _root_.ContinuousLinearMap.isBigOTVS_fun_comp (g : E →L[𝕜] F) : (g <| f ·) =O[𝕜; l] f :=
  g.isBigOTVS_comp

lemma _root_.LinearMap.isBigOTVS_rev_comp (g : E →ₗ[𝕜] F) (hg : comap g (𝓝 0) ≤ 𝓝 0) :
    f =O[𝕜; l] (g ∘ f) := by
  constructor
  intro U hU
  rcases mem_comap.1 (hg hU) with ⟨V, hV, hgV⟩
  use V, hV
  filter_upwards with a
  refine le_egauge_of_forall_ne_zero (mem_of_mem_nhds hV) fun c hc₀ hc ↦ ?_
  apply egauge_le_of_mem_smul
  grw [← hgV, ← (IsUnit.mk0 _ hc₀).preimage_smul_set]
  exact hc

lemma _root_.ContinuousLinearMap.isThetaTVS_comp (g : E →L[𝕜] F) (hg : Topology.IsInducing g) :
    (g ∘ f) =Θ[𝕜; l] f :=
  ⟨g.isBigOTVS_comp, g.isBigOTVS_rev_comp <| by simp [hg.nhds_eq_comap]⟩

lemma _root_.Topology.IsInducing.isBigOTVS_iff_left (φ : E →ₗ[𝕜] G) (hφ : IsInducing φ) :
    ((φ ∘ f) =O[𝕜; l] g) ↔ (f =O[𝕜; l] g) := by
  let Φ : E →L[𝕜] G := ⟨φ, hφ.continuous⟩
  have hφ' : comap φ (𝓝 0) ≤ 𝓝 0 := by rw [hφ.nhds_eq_comap, map_zero]
  exact ⟨(φ.isBigOTVS_rev_comp hφ').trans, Φ.isBigOTVS_comp.trans⟩

lemma _root_.Topology.IsInducing.isBigOTVS_iff_right (φ : F →ₗ[𝕜] G) (hφ : IsInducing φ) :
    (f =O[𝕜; l] (φ ∘ g)) ↔ (f =O[𝕜; l] g) := by
  let Φ : F →L[𝕜] G := ⟨φ, hφ.continuous⟩
  have hφ' : comap φ (𝓝 0) ≤ 𝓝 0 := by rw [hφ.nhds_eq_comap, map_zero]
  exact ⟨fun H ↦ H.trans Φ.isBigOTVS_comp, fun H ↦ H.trans (φ.isBigOTVS_rev_comp hφ')⟩

lemma _root_.Topology.IsInducing.isLittleOTVS_iff_left (φ : E →ₗ[𝕜] G) (hφ : IsInducing φ) :
    ((φ ∘ f) =o[𝕜; l] g) ↔ (f =o[𝕜; l] g) := by
  let Φ : E →L[𝕜] G := ⟨φ, hφ.continuous⟩
  have hφ' : comap φ (𝓝 0) ≤ 𝓝 0 := by rw [hφ.nhds_eq_comap, map_zero]
  exact ⟨(φ.isBigOTVS_rev_comp hφ').trans_isLittleOTVS, Φ.isBigOTVS_comp.trans_isLittleOTVS⟩

lemma _root_.Topology.IsInducing.isLittleOTVS_iff_right (φ : F →ₗ[𝕜] G) (hφ : IsInducing φ) :
    (f =o[𝕜; l] (φ ∘ g)) ↔ (f =o[𝕜; l] g) := by
  let Φ : F →L[𝕜] G := ⟨φ, hφ.continuous⟩
  have hφ' : comap φ (𝓝 0) ≤ 𝓝 0 := by rw [hφ.nhds_eq_comap, map_zero]
  exact ⟨fun H ↦ H.trans_isBigOTVS Φ.isBigOTVS_comp,
    fun H ↦ H.trans_isBigOTVS (φ.isBigOTVS_rev_comp hφ')⟩

omit [TopologicalSpace E] [TopologicalSpace G] in
lemma isBigOTVS_induced_left {tG : TopologicalSpace G} (φ : E →ₗ[𝕜] G) :
    letI : TopologicalSpace E := .induced φ tG
    (f =O[𝕜; l] g) ↔ ((φ ∘ f) =O[𝕜; l] g) :=
  letI : TopologicalSpace E := .induced φ tG
  IsInducing.isBigOTVS_iff_left _ ⟨rfl⟩ |>.symm

omit [TopologicalSpace F] [TopologicalSpace G] in
lemma isBigOTVS_induced_right {tG : TopologicalSpace G} (φ : F →ₗ[𝕜] G) :
    letI : TopologicalSpace F := .induced φ tG
    (f =O[𝕜; l] g) ↔ (f =O[𝕜; l] (φ ∘ g)) :=
  letI : TopologicalSpace F := .induced φ tG
  IsInducing.isBigOTVS_iff_right _ ⟨rfl⟩ |>.symm

omit [TopologicalSpace E] [TopologicalSpace G] in
lemma isLittleOTVS_induced_left {tG : TopologicalSpace G} (φ : E →ₗ[𝕜] G) :
    letI : TopologicalSpace E := .induced φ tG
    (f =o[𝕜; l] g) ↔ ((φ ∘ f) =o[𝕜; l] g) :=
  letI : TopologicalSpace E := .induced φ tG
  IsInducing.isLittleOTVS_iff_left _ ⟨rfl⟩ |>.symm

omit [TopologicalSpace F] [TopologicalSpace G] in
lemma isLittleOTVS_induced_right {tG : TopologicalSpace G} (φ : F →ₗ[𝕜] G) :
    letI : TopologicalSpace F := .induced φ tG
    (f =o[𝕜; l] g) ↔ (f =o[𝕜; l] (φ ∘ g)) :=
  letI : TopologicalSpace F := .induced φ tG
  IsInducing.isLittleOTVS_iff_right _ ⟨rfl⟩ |>.symm

@[simp]
lemma IsLittleOTVS.zero (g : α → F) (l : Filter α) : (0 : α → E) =o[𝕜; l] g := by
  refine ⟨fun U hU ↦ ?_⟩
  use univ
  simp [egauge_zero_right _ (Filter.nonempty_of_mem hU), EventuallyLE]

lemma isLittleOTVS_insert [TopologicalSpace α] {x : α} {s : Set α} (h : f x = 0) :
    f =o[𝕜; 𝓝[insert x s] x] g ↔ f =o[𝕜; (𝓝[s] x)] g := by
  rw [nhdsWithin_insert, isLittleOTVS_sup, and_iff_right]
  exact .congr' (.zero g _) h.symm .rfl

lemma IsLittleOTVS.insert [TopologicalSpace α] {x : α} {s : Set α}
    (h : f =o[𝕜; 𝓝[s] x] g) (hf : f x = 0) :
    f =o[𝕜; 𝓝[insert x s] x] g :=
  (isLittleOTVS_insert hf).2 h

@[simp]
lemma IsLittleOTVS.bot : f =o[𝕜; ⊥] g :=
  ⟨fun u hU ↦ ⟨univ, by simp [EventuallyLE]⟩⟩

theorem IsLittleOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G}
    (hf : f =o[𝕜; l] k) (hg : g =o[𝕜; l] k) : (fun x ↦ (f x, g x)) =o[𝕜; l] k := by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isLittleOTVS_iff
    (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, fun ε hε ↦ ?_⟩
  filter_upwards [hWf ε hε, hWg ε hε] with x hfx hgx
  simp [egauge_prod_mk, *]

protected theorem IsLittleOTVS.fst {f : α → E × F} {g : α → G} (h : f =o[𝕜; l] g) :
    (f · |>.fst) =o[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E F |>.isBigOTVS_comp |>.trans_isLittleOTVS h

protected theorem IsLittleOTVS.snd {f : α → E × F} {g : α → G} (h : f =o[𝕜; l] g) :
    (f · |>.snd) =o[𝕜; l] g :=
  ContinuousLinearMap.snd 𝕜 E F |>.isBigOTVS_comp |>.trans_isLittleOTVS h

@[simp]
theorem isLittleOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G} :
    (fun x ↦ (f x, g x)) =o[𝕜; l] k ↔ f =o[𝕜; l] k ∧ g =o[𝕜; l] k :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.elim .prodMk⟩

theorem IsBigOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G}
    (hf : f =O[𝕜; l] k) (hg : g =O[𝕜; l] k) : (fun x ↦ (f x, g x)) =O[𝕜; l] k := by
  rw [((nhds_basis_balanced 𝕜 E).prod_nhds (nhds_basis_balanced 𝕜 F)).isBigOTVS_iff (basis_sets _)]
  rintro ⟨U, V⟩ ⟨⟨hU, hUb⟩, hV, hVb⟩
  rcases ((hf.eventually_smallSets U hU).and (hg.eventually_smallSets V hV)).exists_mem_of_smallSets
    with ⟨W, hW, hWf, hWg⟩
  refine ⟨W, hW, ?_⟩
  filter_upwards [hWf, hWg] with x hfx hgx
  simp [egauge_prod_mk, *]

protected theorem IsBigOTVS.fst {f : α → E × F} {g : α → G} (h : f =O[𝕜; l] g) :
    (f · |>.fst) =O[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E F |>.isBigOTVS_comp |>.trans h

protected theorem IsBigOTVS.snd {f : α → E × F} {g : α → G} (h : f =O[𝕜; l] g) :
    (f · |>.snd) =O[𝕜; l] g :=
  ContinuousLinearMap.snd 𝕜 E F |>.isBigOTVS_comp |>.trans h

@[simp]
theorem isBigOTVS_prodMk_left [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G} :
    (fun x ↦ (f x, g x)) =O[𝕜; l] k ↔ f =O[𝕜; l] k ∧ g =O[𝕜; l] k :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.elim .prodMk⟩

@[to_fun]
theorem IsLittleOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α → E} {g : α → F} {l : Filter α}
    (h₁ : f₁ =o[𝕜; l] g) (h₂ : f₂ =o[𝕜; l] g) : (f₁ + f₂) =o[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E |>.isBigOTVS_comp
    |>.trans_isLittleOTVS <| h₁.prodMk h₂

@[to_fun]
theorem IsBigOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ : α → E} {g : α → F} {l : Filter α}
    (h₁ : f₁ =O[𝕜; l] g) (h₂ : f₂ =O[𝕜; l] g) : (f₁ + f₂) =O[𝕜; l] g :=
  ContinuousLinearMap.fst 𝕜 E E + ContinuousLinearMap.snd 𝕜 E E |>.isBigOTVS_comp
    |>.trans <| h₁.prodMk h₂

theorem IsLittleOTVS.triangle [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ f₃ : α → E} {g : α → F} {l : Filter α}
    (h₁ : (f₁ - f₂) =o[𝕜; l] g) (h₂ : (f₂ - f₃) =o[𝕜; l] g) : (f₁ - f₃) =o[𝕜; l] g := by
  simpa using h₁.add h₂

theorem IsBigOTVS.triangle [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f₁ f₂ f₃ : α → E} {g : α → F} {l : Filter α}
    (h₁ : (f₁ - f₂) =O[𝕜; l] g) (h₂ : (f₂ - f₃) =O[𝕜; l] g) : (f₁ - f₃) =O[𝕜; l] g := by
  simpa using h₁.add h₂

section NegLeft

variable [ContinuousNeg E]

theorem IsBigOTVS.neg_left (h : f =O[𝕜; l] g) : (-f) =O[𝕜; l] g :=
  .trans ((ContinuousLinearMap.mk (-.id (R := 𝕜)) continuous_neg).isBigOTVS_comp) h

@[simp]
theorem isBigOTVS_neg_left : (-f) =O[𝕜; l] g ↔ f =O[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_left, .neg_left⟩

@[simp]
theorem isBigOTVS_fun_neg_left : (-f ·) =O[𝕜; l] g ↔ f =O[𝕜; l] g :=
  isBigOTVS_neg_left

theorem IsLittleOTVS.neg_left (h : f =o[𝕜; l] g) : (-f) =o[𝕜; l] g :=
  IsBigOTVS.rfl.neg_left.trans_isLittleOTVS h

@[simp]
theorem isLittleOTVS_neg_left : (-f) =o[𝕜; l] g ↔ f =o[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_left, .neg_left⟩

@[simp]
theorem isLittleOTVS_fun_neg_left : (-f ·) =o[𝕜; l] g ↔ f =o[𝕜; l] g :=
  isLittleOTVS_neg_left

@[to_fun]
protected theorem IsLittleOTVS.symm {f₁ f₂ : α → E} (h : (f₁ - f₂) =o[𝕜; l] g) :
    (f₂ - f₁) =o[𝕜; l] g := by
  simpa using h.neg_left

theorem isLittleOTVS_comm {f₁ f₂ : α → E} :
    (f₁ - f₂) =o[𝕜; l] g ↔ (f₂ - f₁) =o[𝕜; l] g :=
  ⟨.symm, .symm⟩

theorem isLittleOTVS_fun_comm {f₁ f₂ : α → E} :
    (fun a ↦ f₁ a - f₂ a) =o[𝕜; l] g ↔ (fun a ↦ f₂ a - f₁ a) =o[𝕜; l] g :=
  isLittleOTVS_comm

@[to_fun]
protected theorem IsBigOTVS.symm {f₁ f₂ : α → E} (h : (f₁ - f₂) =O[𝕜; l] g) :
    (f₂ - f₁) =O[𝕜; l] g := by
  simpa using h.neg_left

theorem isBigOTVS_comm {f₁ f₂ : α → E} :
    (f₁ - f₂) =O[𝕜; l] g ↔ (f₂ - f₁) =O[𝕜; l] g :=
  ⟨.symm, .symm⟩

theorem isBigOTVS_fun_comm {f₁ f₂ : α → E} :
    (fun a ↦ f₁ a - f₂ a) =O[𝕜; l] g ↔ (fun a ↦ f₂ a - f₁ a) =O[𝕜; l] g :=
  isBigOTVS_comm

end NegLeft

section NegRight

variable [ContinuousNeg F]

theorem IsBigOTVS.neg_right (h : f =O[𝕜; l] g) : f =O[𝕜; l] (-g) :=
  h.trans <| by simpa using (IsBigOTVS.refl (-g) l).neg_left

@[simp]
theorem isBigOTVS_neg_right : f =O[𝕜; l] (-g) ↔ f =O[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_right, .neg_right⟩

@[simp]
theorem isBigOTVS_fun_neg_right : f =O[𝕜; l] (-g ·) ↔ f =O[𝕜; l] g :=
  isBigOTVS_neg_right

theorem IsLittleOTVS.neg_right (h : f =o[𝕜; l] g) : f =o[𝕜; l] (-g) :=
  h.trans_isBigOTVS (.neg_right .rfl)

@[simp]
theorem isLittleOTVS_neg_right : f =o[𝕜; l] (-g) ↔ f =o[𝕜; l] g :=
  ⟨fun h ↦ by simpa using h.neg_right, .neg_right⟩

@[simp]
theorem isLittleOTVS_fun_neg_right : f =o[𝕜; l] (-g ·) ↔ f =o[𝕜; l] g :=
  isLittleOTVS_neg_right

end NegRight

protected theorem IsLittleOTVS.pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : ∀ i, α → E i} (h : ∀ i, f i =o[𝕜; l] g) : (fun x i ↦ f i x) =o[𝕜; l] g := by
  have := hasBasis_pi fun i ↦ nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi, ← Pi.zero_def] at this
  simp only [this.isLittleOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi ↦ (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε ↦ ?_⟩
  refine (hIf.eventually_all.mpr (hV · · ε hε)).mono fun x hx ↦ ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]

theorem IsLittleOTVS.proj {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] {f : α → ∀ i, E i}
    (h : f =o[𝕜; l] g) (i : ι) : (f · i) =o[𝕜; l] g :=
  ContinuousLinearMap.proj i |>.isBigOTVS_fun_comp |>.trans_isLittleOTVS h

theorem isLittleOTVS_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : α → ∀ i, E i} : f =o[𝕜; l] g ↔ ∀ i, (f · i) =o[𝕜; l] g :=
  ⟨.proj, .pi⟩

omit [TopologicalSpace E] in
theorem isLittleOTVS_iInf {ι : Type*} {t : ι → TopologicalSpace E}
    (ht : ∀ i, @ContinuousSMul 𝕜 E _ _ (t i)) :
    (letI : TopologicalSpace E := ⨅ i, t i; f =o[𝕜; l] g) ↔ ∀ i,
      (letI : TopologicalSpace E := t i; f =o[𝕜; l] g) := by
  let Φ : E →ₗ[𝕜] (ι → E) := .pi fun _ ↦ .id
  have : ⨅ i, t i = .induced Φ (@Pi.topologicalSpace _ _ t) := by
    simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose]
    congr!
    exact (@induced_id _ ?_).symm
  rw [this, isLittleOTVS_induced_left, @isLittleOTVS_pi]
  rfl

omit [TopologicalSpace E] in
theorem isLittleOTVS_sInf {s : Set (TopologicalSpace E)}
    (hs : ∀ t ∈ s, @ContinuousSMul 𝕜 E _ _ t) :
    (letI : TopologicalSpace E := sInf s; f =o[𝕜; l] g) ↔ ∀ t ∈ s,
      (letI : TopologicalSpace E := t; f =o[𝕜; l] g) := by
  rw [Subtype.forall'] at hs ⊢
  simp_rw [sInf_eq_iInf', isLittleOTVS_iInf]

omit [TopologicalSpace E] in
theorem isLittleOTVS_inf {t₁ t₂ : TopologicalSpace E}
    [@ContinuousSMul 𝕜 E _ _ t₁] [@ContinuousSMul 𝕜 E _ _ t₂] :
    (letI : TopologicalSpace E := t₁ ⊓ t₂; f =o[𝕜; l] g) ↔
      (letI : TopologicalSpace E := t₁; f =o[𝕜; l] g) ∧
      (letI : TopologicalSpace E := t₂; f =o[𝕜; l] g) := by
  rw [inf_eq_iInf, isLittleOTVS_iInf, Bool.forall_bool, cond_false, cond_true, and_comm]
  intro i; cases i <;> assumption

protected theorem IsBigOTVS.pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : ∀ i, α → E i} (h : ∀ i, f i =O[𝕜; l] g) : (fun x i ↦ f i x) =O[𝕜; l] g := by
  have := hasBasis_pi fun i ↦ nhds_basis_balanced 𝕜 (E i)
  rw [← nhds_pi, ← Pi.zero_def] at this
  simp only [this.isBigOTVS_iff (basis_sets _), forall_and, Prod.forall, id]
  rintro I U ⟨hIf, hU, Ub⟩
  have := fun i hi ↦ (h i).eventually_smallSets (U i) (hU i hi)
  rcases (hIf.eventually_all.mpr this).exists_mem_of_smallSets with ⟨V, hV₀, hV⟩
  use V, hV₀
  refine (hIf.eventually_all.mpr hV).mono fun x hx ↦ ?_
  simpa only [id, egauge_pi hIf Ub, iSup₂_le_iff]

theorem IsBigOTVS.proj {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] {f : α → ∀ i, E i}
    (h : f =O[𝕜; l] g) (i : ι) : (f · i) =O[𝕜; l] g :=
  ContinuousLinearMap.proj i |>.isBigOTVS_fun_comp |>.trans h

theorem isBigOTVS_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
    {f : α → ∀ i, E i} : f =O[𝕜; l] g ↔ ∀ i, (f · i) =O[𝕜; l] g :=
  ⟨.proj, .pi⟩

omit [TopologicalSpace E] in
theorem isBigOTVS_iInf {ι : Type*} {t : ι → TopologicalSpace E}
    (ht : ∀ i, @ContinuousSMul 𝕜 E _ _ (t i)) :
    (letI : TopologicalSpace E := ⨅ i, t i; f =O[𝕜; l] g) ↔ ∀ i,
      (letI : TopologicalSpace E := t i; f =O[𝕜; l] g) := by
  let Φ : E →ₗ[𝕜] (ι → E) := .pi fun _ ↦ .id
  have : ⨅ i, t i = .induced Φ (@Pi.topologicalSpace _ _ t) := by
    simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose]
    congr!
    exact (@induced_id _ ?_).symm
  rw [this, isBigOTVS_induced_left, @isBigOTVS_pi]
  rfl

omit [TopologicalSpace E] in
theorem isBigOTVS_sInf {s : Set (TopologicalSpace E)}
    (hs : ∀ t ∈ s, @ContinuousSMul 𝕜 E _ _ t) :
    (letI : TopologicalSpace E := sInf s; f =O[𝕜; l] g) ↔ ∀ t ∈ s,
      (letI : TopologicalSpace E := t; f =O[𝕜; l] g) := by
  rw [Subtype.forall'] at hs ⊢
  simp_rw [sInf_eq_iInf', isBigOTVS_iInf]

omit [TopologicalSpace E] in
theorem isBigOTVS_inf {t₁ t₂ : TopologicalSpace E}
    [@ContinuousSMul 𝕜 E _ _ t₁] [@ContinuousSMul 𝕜 E _ _ t₂] :
    (letI : TopologicalSpace E := t₁ ⊓ t₂; f =O[𝕜; l] g) ↔
      (letI : TopologicalSpace E := t₁; f =O[𝕜; l] g) ∧
      (letI : TopologicalSpace E := t₂; f =O[𝕜; l] g) := by
  rw [inf_eq_iInf, isBigOTVS_iInf, Bool.forall_bool, cond_false, cond_true, and_comm]
  intro i; cases i <;> assumption

protected lemma IsLittleOTVS.smul_left (h : f =o[𝕜; l] g) (c : α → 𝕜) :
    (fun x ↦ c x • f x) =o[𝕜; l] (fun x ↦ c x • g x) := by
  simp only [isLittleOTVS_iff] at *
  peel h with U hU V hV ε hε x hx
  simp only at *
  rw [egauge_smul_right, egauge_smul_right, mul_left_comm]
  · gcongr
  all_goals exact fun _ ↦ Filter.nonempty_of_mem ‹_›

lemma isLittleOTVS_one [ContinuousSMul 𝕜 E] : f =o[𝕜; l] (1 : α → 𝕜) ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro hf
    rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at hf
    rw [(nhds_basis_balanced 𝕜 E).tendsto_right_iff]
    rintro U ⟨hU, hUb⟩
    rcases hf U hU with ⟨r, hr₀, hr⟩
    lift r to ℝ≥0 using hr₀.le
    norm_cast at hr₀
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    obtain ⟨ε, hε₀, hε⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ (ε * ‖c‖₊ / r : ℝ≥0∞) < 1 := by
      apply Eventually.exists_gt
      refine Continuous.tendsto' ?_ _ _ (by simp) |>.eventually_lt_const zero_lt_one
      fun_prop (disch := intros; first | apply ENNReal.coe_ne_top | positivity)
    filter_upwards [hr ε hε₀.ne'] with x hx
    refine mem_of_egauge_lt_one hUb (hx.trans_lt ?_)
    calc
      (ε : ℝ≥0∞) * egauge 𝕜 (ball (0 : 𝕜) r) 1 ≤ (ε * ‖c‖₊ / r : ℝ≥0∞) := by
        rw [mul_div_assoc]
        gcongr
        simpa using egauge_ball_le_of_one_lt_norm (r := r) (x := (1 : 𝕜)) hc (by simp)
      _ < 1 := ‹_›
  · simp only [isLittleOTVS_iff]
    intro hf U hU
    refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε ↦ ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε⟩
    replace hc₀ : c ≠ 0 := by simpa using hc₀
    filter_upwards [hf ((set_smul_mem_nhds_zero_iff hc₀).2 hU)] with a ha
    calc
      egauge 𝕜 U (f a) ≤ ‖c‖₊ := egauge_le_of_mem_smul ha
      _ ≤ ε := mod_cast hcε.le
      _ ≤ ε * egauge 𝕜 (ball (0 : 𝕜) 1) 1 := by
        apply le_mul_of_one_le_right'
        simpa using le_egauge_ball_one 𝕜 (1 : 𝕜)

lemma IsLittleOTVS.tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α → 𝕜} {g : α → E}
    (h : g =o[𝕜; l] f) : Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  rw [← isLittleOTVS_one (𝕜 := 𝕜), isLittleOTVS_iff]
  intro U hU
  rcases (h.smul_left f⁻¹).1 U hU with ⟨V, hV₀, hV⟩
  refine ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x hx ↦ hx.trans ?_⟩
  by_cases hx₀ : f x = 0 <;> simp [hx₀, egauge_zero_right _ (Filter.nonempty_of_mem hV₀)]

lemma isLittleOTVS_iff_tendsto_inv_smul [ContinuousSMul 𝕜 E] {f : α → 𝕜} {g : α → E} {l : Filter α}
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    g =o[𝕜; l] f ↔ Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h ↦ ?_⟩
  refine (((isLittleOTVS_one (𝕜 := 𝕜)).mpr h).smul_left f).congr' (h₀.mono fun x hx ↦ ?_) (by simp)
  by_cases h : f x = 0 <;> simp [h, hx]

variable (𝕜) in
/-- If `f` converges along `l` to a finite limit `x`, then `f =O[𝕜, l] 1`. -/
lemma Filter.Tendsto.isBigOTVS_one [ContinuousAdd E] [ContinuousSMul 𝕜 E] {x : E}
    (h : Tendsto f l (𝓝 x)) : f =O[𝕜; l] (fun _ ↦ 1 : α → 𝕜) := by
  replace h : Tendsto (f · - x) l (𝓝 0) := by
    simpa [sub_eq_add_neg] using h.add (tendsto_const_nhds (x := -x))
  rw [(nhds_basis_balanced 𝕜 E).add_self.isBigOTVS_iff nhds_basis_ball]
  rintro U ⟨hU₀, hUb⟩
  obtain ⟨r, hr₀, hr₁, hr⟩ : ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ (r : ℝ≥0∞) ≤ (egauge 𝕜 U x)⁻¹ := by
    apply Eventually.exists_gt
    refine .and (eventually_le_nhds one_pos) ?_
    refine (ENNReal.tendsto_coe.mpr tendsto_id).eventually_le_const ?_
    suffices ∃ c : 𝕜, x ∈ c • U by simpa [egauge_eq_top]
    simpa using (absorbent_nhds_zero (𝕜 := 𝕜) hU₀ x).exists
  use r, by positivity
  filter_upwards [h.eventually_mem hU₀] with a ha
  calc
    egauge 𝕜 (U + U) (f a) ≤ max (egauge 𝕜 U (f a - x)) (egauge 𝕜 U x) := by
      simpa using egauge_add_add_le hUb hUb (f a - x) x
    _ ≤ (r : ℝ≥0∞)⁻¹ := by
      apply max_le
      · refine (egauge_le_one _ ha).trans ?_
        simp [hr₁]
      · rwa [ENNReal.le_inv_iff_le_inv]
    _ ≤ egauge 𝕜 (ball (0 : 𝕜) _) 1 := by simpa using div_le_egauge_ball 𝕜 r (1 : 𝕜)

end TopologicalSpace

section NormedSpace

variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
variable {f : α → E} {g : α → F} {l : Filter α}

lemma isLittleOTVS_iff_isLittleO : f =o[𝕜; l] g ↔ f =o[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ⟨1, one_pos, fun δ hδ ↦ ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to ℝ≥0 using hε.le; lift δ to ℝ≥0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : ℝ≥0∞) ≤ ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff₀' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : ℝ≥0∞) ≤ egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ ≤ ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ ≤ (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ ≤ 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ ≤ ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to ℝ≥0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) ≤ ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ ≤ ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ ≤ 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ ≤ δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one

alias ⟨isLittleOTVS.isLittleO, IsLittleO.isLittleOTVS⟩ := isLittleOTVS_iff_isLittleO

lemma isBigOTVS_iff_isBigO : f =O[𝕜; l] g ↔ f =O[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  constructor
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff]
    intro h
    rcases h 1 one_pos with ⟨r, hr₀, hr⟩
    lift r to ℝ≥0 using hr₀.le
    norm_cast at hr₀
    refine ⟨(‖c‖₊ / r : ℝ≥0), hr.mono fun x hx ↦ ?_⟩
    suffices ‖f x‖ₑ ≤ (‖c‖₊ / r : ℝ≥0) * ‖g x‖ₑ by
      simp only [enorm_eq_nnnorm, ← coe_nnnorm] at this ⊢
      exact mod_cast this
    calc
      ‖f x‖ₑ ≤ egauge 𝕜 (ball 0 1) (f x) := le_egauge_ball_one ..
      _ ≤ egauge 𝕜 (ball 0 r) (g x) := hx
      _ ≤ ‖c‖ₑ * ‖g x‖ₑ / ↑r :=
        egauge_ball_le_of_one_lt_norm hc <| .inl hr₀.ne'
      _ = (‖c‖₊ / r : ℝ≥0) * ‖g x‖ₑ := by
        simp [hr₀.ne', ENNReal.mul_div_right_comm, enorm_eq_nnnorm]
  · rw [nhds_basis_ball.isBigOTVS_iff nhds_basis_ball, isBigO_iff']
    have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
    rintro ⟨C, hC₀, hC⟩ r hr₀
    lift C to ℝ≥0 using hC₀.le; norm_cast at hC₀
    lift r to ℝ≥0 using hr₀.le; norm_cast at hr₀
    refine ⟨r / (C * ‖c‖₊), by positivity, hC.mono fun x hx ↦ ?_⟩
    calc
      egauge 𝕜 (ball 0 r) (f x) ≤ ‖c‖ₑ * ‖f x‖ₑ / r :=
        egauge_ball_le_of_one_lt_norm hc <| .inl hr₀.ne'
      _ ≤ ‖c‖ₑ * (C * ‖g x‖ₑ) / r := by
        gcongr
        simp only [enorm_eq_nnnorm, ← coe_nnnorm] at hx ⊢
        exact mod_cast hx
      _ = ‖g x‖ₑ / (r / (C * ‖c‖₊) : ℝ≥0) := by
        simp_all [pos_iff_ne_zero, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        ac_rfl
      _ ≤ _ := div_le_egauge_ball _ _ _

alias ⟨IsBigOTVS.isBigO, IsBigO.isBigOTVS⟩ := isBigOTVS_iff_isBigO

@[deprecated (since := "2026-02-03")]
alias isBigOTVS.isBigO := IsBigOTVS.isBigO

lemma isThetaTVS_iff_isTheta : f =Θ[𝕜; l] g ↔ f =Θ[l] g :=
  .and isBigOTVS_iff_isBigO isBigOTVS_iff_isBigO

alias ⟨IsThetaTVS.isTheta, IsTheta.isThetaTVS⟩ := isThetaTVS_iff_isTheta

end NormedSpace

end Asymptotics
