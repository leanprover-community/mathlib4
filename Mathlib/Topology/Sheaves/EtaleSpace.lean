/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Etale space of a presheaf
-/

public section

open Function Set CategoryTheory TopologicalSpace Opposite Filter
open scoped Topology

namespace TopCat.Presheaf

universe v u w
variable {X : TopCat.{v}} {C : Type u} [Category.{v} C] {CC : C → Type v} {FC : C → C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [Limits.HasColimits.{v} C]

/-- Etale space of a presheaf. -/
structure EtaleSpace (F : Presheaf C X) where
  base : X
  germ : ToType (F.stalk base)

instance (F : Presheaf C X) : TopologicalSpace F.EtaleSpace :=
  .generateFrom {s | ∃ U, ∃ f : ToType (F.obj (op U)),
    s = {g | ∃ h, g.germ = F.germ U g.base h f}}

variable {F : Presheaf C X}

theorem EtaleSpace.eventually_nhds (g : EtaleSpace F) {U : Opens X} (h : g.base ∈ U)
    (f : ToType (F.obj (op U))) (hf : F.germ U g.base h f = g.germ) :
    ∀ᶠ g' : EtaleSpace F in 𝓝 g, ∃ hgU : g'.base ∈ U, g'.germ = F.germ U g'.base hgU f := by
  simp only [nhds_generateFrom, Filter.Eventually, mem_setOf_eq, iInf_and, iInf_exists]
  refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_iInf_of_mem U <| mem_iInf_of_mem f <|
    mem_iInf_of_mem rfl <| mem_principal_self _
  simp [*]

variable [Limits.PreservesFilteredColimits (forget C)]

variable (F) in
@[fun_prop]
theorem EtaleSpace.continuous_base : Continuous (base (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
  rintro U ⟨hxU, hUo⟩
  lift U to Opens X using hUo
  rcases F.exists_le_germ_eq x.germ hxU with ⟨V, hVU, hxV, f, hf⟩
  refine x.eventually_nhds hxV f hf |>.mono ?_
  simp +contextual [@hVU _]

@[expose, simps apply_fst]
noncomputable def EtaleSpace.homeomorph (U : Opens X)
    (hF_bij : ∀ (x : X) (hx : x ∈ U), Bijective (F.germ U x hx))
    (x : X) (hx : x ∈ U) :
    (base (F := F) ⁻¹' U) ≃ₜ U × WithTopology (ToType (F.stalk x)) ⊥ where
  toFun s := (⟨s.1.base, s.2⟩,
    .toTopology ⊥ <| F.germ U x hx <| surjInv (hF_bij s.1.base s.2).surjective s.1.germ)
  invFun
  | (⟨y, hy⟩, .toTopology _ g) => ⟨⟨y, F.germ U y hy <| surjInv (hF_bij x hx).surjective g⟩, hy⟩
  left_inv := by
    rintro ⟨⟨base, s⟩, hs⟩
    simp only
    congr 2
    rw [leftInverse_surjInv (hF_bij _ _), surjInv_eq (hF_bij _ _).surjective]
  right_inv := by
    rintro ⟨⟨y, hy⟩, ⟨g⟩⟩
    simp only
    congr
    rw [leftInverse_surjInv (hF_bij _ _), surjInv_eq (hF_bij _ _).surjective]
  continuous_toFun := by
    refine .prodMk (by fun_prop) ?_
    simp_rw [continuous_iff_continuousAt, ContinuousAt, nhds_discrete, tendsto_pure, nhds_subtype,
      eventually_comap]
    rintro ⟨g, hg⟩
    rcases hF_bij _ hg |>.surjective g.germ with ⟨f, hf⟩
    filter_upwards [g.eventually_nhds hg f hf]
    rintro _ ⟨hgU, hgf⟩ g' rfl
    congr 1
    rw [hgf, ← hf, leftInverse_surjInv (hF_bij _ _), leftInverse_surjInv (hF_bij _ _)]
  continuous_invFun := by
    simp_rw [continuous_iff_continuousAt, continuousAt_prod_of_discrete_right]
    rintro ⟨y, ⟨g⟩⟩
    simp only [ContinuousAt, nhds_subtype_eq_comap, tendsto_comap_iff, comp_def,
      nhds_generateFrom, tendsto_iInf, mem_setOf_eq, tendsto_principal]
    rintro _ ⟨hmem, V, f, rfl⟩
    simp only [mem_setOf_eq] at hmem
    rcases hmem with ⟨hyV, hgf⟩
    rcases F.germ_eq _ _ _ _ _ hgf with ⟨W, hyW, ιWU, ιWV, hW⟩
    filter_upwards [W.isOpen.preimage continuous_subtype_val |>.mem_nhds hyW] with z hz
    use ιWV.le hz
    rw [← F.germ_res_apply ιWU z hz, hW, F.germ_res_apply]

theorem EtaleSpace.isCoveringMap_base
    (hF_bij : ∀ x, ∃ (U : Opens X), x ∈ U ∧ ∀ y (hyU : y ∈ U), Bijective (F.germ U y hyU)) :
    IsCoveringMap (base (F := F)) := by
  refine fun x ↦ .to_isEvenlyCovered_preimage (I := WithTopology (ToType (F.stalk x)) ⊥) ?_
  use inferInstance
  rcases hF_bij x with ⟨U, hxU, hU_bij⟩
  use U, hxU, U.isOpen, U.isOpen.preimage (continuous_base F), homeomorph U hU_bij x hxU
  simp

theorem EtaleSpace.exists_section_of_tendsto {α : Type*} {l : Filter α} {g : α → F.EtaleSpace}
    {g₀ : F.EtaleSpace} (h : Tendsto g l (𝓝 g₀)) :
    ∃ (U : Opens X), g₀.base ∈ U ∧ ∃ (f : ToType (F.obj (op U))),
      ∀ᶠ a in l, ∃ ha : (g a).base ∈ U, (g a).germ = F.germ U (g a).base ha f := by
  rcases F.exists_germ_eq g₀.germ with ⟨U, hU, s, hs⟩
  use U, hU, s
  exact h.eventually <| g₀.eventually_nhds hU s hs

end TopCat.Presheaf
