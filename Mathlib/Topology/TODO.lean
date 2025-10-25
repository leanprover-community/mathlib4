import Mathlib.Analysis.Calculus.Deriv.Basic

open Filter
open scoped Topology Pointwise

@[to_additive]
theorem nhds_smul {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (g : G) (x : X) : 𝓝 (g • x) = g • 𝓝 x :=
  (Homeomorph.smul g).map_nhds_eq x |>.symm

@[to_additive]
theorem Filter.smul_principal {α β : Type*} [SMul α β] (a : α) (s : Set β) : a • 𝓟 s = 𝓟 (a • s) :=
  map_principal

@[to_additive]
theorem Filter.smul_filter_inf {G α : Type*} [Group G] [MulAction G α] (g : G) (l₁ l₂ : Filter α) :
    g • (l₁ ⊓ l₂) = g • l₁ ⊓ g • l₂ :=
  map_inf <| MulAction.injective g

@[to_additive]
theorem nhdsWithin_smul {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (g : G) (s : Set X) (x : X) : 𝓝[g • s] (g • x) = g • 𝓝[s] x := by
  simp only [nhdsWithin, smul_filter_inf, nhds_smul, smul_principal]

theorem Set.Subsingleton.hasFDerivWithinAt {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {a : E} (hs : s.Subsingleton) :
    HasFDerivWithinAt f f' s a :=
  .of_subsingleton hs

theorem Set.Finite.fderivWithin_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : s.Finite) (f : E → F) : fderivWithin 𝕜 f s = 0 := by
  ext1 x
  simp [fderivWithin, HasFDerivWithinAt.of_finite hs]

theorem Set.Subsingleton.fderivWithin_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : s.Subsingleton) (f : E → F) : fderivWithin 𝕜 f s = 0 :=
  hs.finite.fderivWithin_eq f

theorem Set.Finite.derivWithin_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set 𝕜} (hs : s.Finite) (f : 𝕜 → E) :
    derivWithin f s = 0 := by
  ext1 x
  simp [derivWithin, hs.fderivWithin_eq]

theorem Set.Subsingleton.derivWithin_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set 𝕜} (hs : s.Subsingleton) (f : 𝕜 → E) :
    derivWithin f s = 0 :=
  hs.finite.derivWithin_eq f
