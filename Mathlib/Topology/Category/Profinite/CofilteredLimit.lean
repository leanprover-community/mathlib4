/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Category.TopCat.Limits.Konig

#align_import topology.category.Profinite.cofiltered_limit from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_isClopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/

namespace Profinite

open scoped Classical

open CategoryTheory

open CategoryTheory.Limits

universe u v

variable {J : Type v} [SmallCategory J] [IsCofiltered J] {F : J ⥤ ProfiniteMax.{u, v}} (C : Cone F)

noncomputable
instance preserves_smaller_limits_toTopCat :
    PreservesLimitsOfSize.{v, v} (toTopCat : ProfiniteMax.{v, u} ⥤ TopCatMax.{v, u}) :=
  Limits.preservesLimitsOfSizeShrink.{v, max u v, v, max u v} _

-- include hC
-- Porting note: I just add `(hC : IsLimit C)` explicitly as a hypothesis to all the theorems

/-- If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_isClopen_of_cofiltered {U : Set C.pt} (hC : IsLimit C) (hU : IsClopen U) :
    ∃ (j : J) (V : Set (F.obj j)) (_ : IsClopen V), U = C.π.app j ⁻¹' V := by
  have := preserves_smaller_limits_toTopCat.{u, v}
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB := TopCat.isTopologicalBasis_cofiltered_limit.{u, v} (F ⋙ Profinite.toTopCat)
      (Profinite.toTopCat.mapCone C) (isLimitOfPreserves _ hC) (fun j => {W | IsClopen W}) ?_
      (fun i => isClopen_univ) (fun i U1 U2 hU1 hU2 => hU1.inter hU2) ?_
  rotate_left
  · intro i
    change TopologicalSpace.IsTopologicalBasis {W : Set (F.obj i) | IsClopen W}
    apply isTopologicalBasis_isClopen
  · rintro i j f V (hV : IsClopen _)
    exact ⟨hV.1.preimage ((F ⋙ toTopCat).map f).continuous,
      hV.2.preimage ((F ⋙ toTopCat).map f).continuous⟩
    -- Porting note: `<;> continuity` fails
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S, hS, h⟩ := hB.open_eq_sUnion hU.1
  clear hB
  let j : S → J := fun s => (hS s.2).choose
  let V : ∀ s : S, Set (F.obj (j s)) := fun s => (hS s.2).choose_spec.choose
  have hV : ∀ s : S, IsClopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' V s := fun s =>
    (hS s.2).choose_spec.choose_spec

  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have hUo : ∀ (i : ↑S), IsOpen ((fun s ↦ (forget Profinite).map (C.π.app (j s)) ⁻¹' V s) i)
  · intro s
    exact (hV s).1.1.preimage (C.π.app (j s)).continuous
  have hsU : U ⊆ ⋃ (i : ↑S), (fun s ↦ (forget Profinite).map (C.π.app (j s)) ⁻¹' V s) i
  · dsimp only
    rw [h]
    rintro x ⟨T, hT, hx⟩
    refine' ⟨_, ⟨⟨T, hT⟩, rfl⟩, _⟩
    dsimp only [forget_map_eq_coe]
    rwa [← (hV ⟨T, hT⟩).2]
  have := hU.2.isCompact.elim_finite_subcover (fun s : S => C.π.app (j s) ⁻¹' V s) hUo hsU
  -- Porting note: same remark as after `hB`
  -- We thus obtain a finite set `G : Finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G, hG⟩ := this
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists (G.image j)
  let f : ∀ (s : S) (_ : s ∈ G), j0 ⟶ j s := fun s hs =>
    (hj0 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let W : S → Set (F.obj j0) := fun s => if hs : s ∈ G then F.map (f s hs) ⁻¹' V s else Set.univ
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine' ⟨j0, ⋃ (s : S) (_ : s ∈ G), W s, _, _⟩
  · apply isClopen_biUnion_finset
    intro s hs
    dsimp
    rw [dif_pos hs]
    exact ⟨(hV s).1.1.preimage (F.map _).continuous, (hV s).1.2.preimage (F.map _).continuous⟩
  · ext x
    constructor
    · intro hx
      simp_rw [Set.preimage_iUnion, Set.mem_iUnion]
      obtain ⟨_, ⟨s, rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx
      refine' ⟨s, hs, _⟩
      rwa [dif_pos hs, ← Set.preimage_comp, ← Profinite.coe_comp, ← Functor.map_comp, C.w]
    · intro hx
      simp_rw [Set.preimage_iUnion, Set.mem_iUnion] at hx
      obtain ⟨s, hs, hx⟩ := hx
      rw [h]
      refine' ⟨s.1, s.2, _⟩
      rw [(hV s).2]
      rwa [dif_pos hs, ← Set.preimage_comp, ← Profinite.coe_comp, ← Functor.map_comp, C.w] at hx
set_option linter.uppercaseLean3 false in
#align Profinite.exists_clopen_of_cofiltered Profinite.exists_isClopen_of_cofiltered

theorem exists_locallyConstant_fin_two (hC : IsLimit C) (f : LocallyConstant C.pt (Fin 2)) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (C.π.app _) := by
  let U := f ⁻¹' {0}
  have hU : IsClopen U := f.isLocallyConstant.isClopen_fiber _
  obtain ⟨j, V, hV, h⟩ := exists_isClopen_of_cofiltered C hC hU
  use j, LocallyConstant.ofIsClopen hV
  apply LocallyConstant.locallyConstant_eq_of_fiber_zero_eq
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LocallyConstant.coe_comap _ _ (C.π.app j).continuous]
  conv_rhs => rw [Set.preimage_comp]
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LocallyConstant.ofIsClopen_fiber_zero hV, ← h]
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant_fin_two Profinite.exists_locallyConstant_fin_two

theorem exists_locallyConstant_finite_aux {α : Type*} [Finite α] (hC : IsLimit C)
    (f : LocallyConstant C.pt α) : ∃ (j : J) (g : LocallyConstant (F.obj j) (α → Fin 2)),
      (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.app _) := by
  cases nonempty_fintype α
  let ι : α → α → Fin 2 := fun x y => if x = y then 0 else 1
  let ff := (f.map ι).flip
  have hff := fun a : α => exists_locallyConstant_fin_two _ hC (ff a)
  choose j g h using hff
  let G : Finset J := Finset.univ.image j
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists G
  have hj : ∀ a, j a ∈ (Finset.univ.image j : Finset J) := by
    intro a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]
  let fs : ∀ a : α, j0 ⟶ j a := fun a => (hj0 (hj a)).some
  let gg : α → LocallyConstant (F.obj j0) (Fin 2) := fun a => (g a).comap (F.map (fs _))
  let ggg := LocallyConstant.unflip gg
  refine' ⟨j0, ggg, _⟩
  have : f.map ι = LocallyConstant.unflip (f.map ι).flip := by simp
  rw [this]; clear this
  have :
    LocallyConstant.comap (C.π.app j0) ggg =
      LocallyConstant.unflip (LocallyConstant.comap (C.π.app j0) ggg).flip :=
    by simp
  rw [this]; clear this
  congr 1
  ext1 a
  change ff a = _
  rw [h]
  dsimp
  ext1 x
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LocallyConstant.coe_comap _ _ (C.π.app (j a)).continuous]
  dsimp [LocallyConstant.flip, LocallyConstant.unflip]
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LocallyConstant.coe_comap _ _ (C.π.app j0).continuous]
  dsimp
  rw [LocallyConstant.coe_comap _ _ _]
  -- Porting note: `repeat' rw [LocallyConstant.coe_comap]` didn't work
  -- so I did all three rewrites manually
  · dsimp
    congr! 1
    change _ = (C.π.app j0 ≫ F.map (fs a)) x
    rw [C.w]; rfl
  · exact (F.map _).continuous
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant_finite_aux Profinite.exists_locallyConstant_finite_aux

theorem exists_locallyConstant_finite_nonempty {α : Type*} [Finite α] [Nonempty α]
    (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  inhabit α
  obtain ⟨j, gg, h⟩ := exists_locallyConstant_finite_aux _ hC f
  let ι : α → α → Fin 2 := fun a b => if a = b then 0 else 1
  let σ : (α → Fin 2) → α := fun f => if h : ∃ a : α, ι a = f then h.choose else default
  refine' ⟨j, gg.map σ, _⟩
  ext x
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LocallyConstant.coe_comap _ _ (C.π.app j).continuous]
  dsimp
  have h1 : ι (f x) = gg (C.π.app j x) := by
    change f.map (fun a b => if a = b then (0 : Fin 2) else 1) x = _
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [h, LocallyConstant.coe_comap _ _ (C.π.app j).continuous]
    rfl
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [dif_pos h2]
  apply_fun ι
  · rw [h2.choose_spec]
    exact h1
  · intro a b hh
    have hhh := congr_fun hh a
    dsimp at hhh
    rw [if_pos rfl] at hhh
    split_ifs at hhh with hh1
    · exact hh1.symm
    · exact False.elim (bot_ne_top hhh)
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant_finite_nonempty Profinite.exists_locallyConstant_finite_nonempty

/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
theorem exists_locallyConstant {α : Type*} (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  have := preserves_smaller_limits_toTopCat.{u, v}
  let S := f.discreteQuotient
  let ff : S → α := f.lift
  cases isEmpty_or_nonempty S
  · suffices ∃ j, IsEmpty (F.obj j) by
      refine' this.imp fun j hj => _
      refine' ⟨⟨hj.elim, fun A => _⟩, _⟩
      · suffices : (fun a ↦ IsEmpty.elim hj a) ⁻¹' A = ∅
        · rw [this]
          exact isOpen_empty
        exact @Set.eq_empty_of_isEmpty _ hj _
      · ext x
        exact hj.elim' (C.π.app j x)
    simp only [← not_nonempty_iff, ← not_forall]
    intro h
    haveI : ∀ j : J, Nonempty ((F ⋙ Profinite.toTopCat).obj j) := h
    haveI : ∀ j : J, T2Space ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : T2Space (F.obj j))
    haveI : ∀ j : J, CompactSpace ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : CompactSpace (F.obj j))
    have cond := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u}
      (F ⋙ Profinite.toTopCat)
    suffices : Nonempty C.pt; exact IsEmpty.false (S.proj this.some)
    let D := Profinite.toTopCat.mapCone C
    have hD : IsLimit D := isLimitOfPreserves Profinite.toTopCat hC
    have CD := (hD.conePointUniqueUpToIso (TopCat.limitConeIsLimit.{v, max u v} _)).inv
    exact cond.map CD
  · let f' : LocallyConstant C.pt S := ⟨S.proj, S.proj_isLocallyConstant⟩
    obtain ⟨j, g', hj⟩ := exists_locallyConstant_finite_nonempty _ hC f'
    refine' ⟨j, ⟨ff ∘ g', g'.isLocallyConstant.comp _⟩, _⟩
    ext1 t
    apply_fun fun e => e t at hj
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [LocallyConstant.coe_comap _ _ (C.π.app j).continuous] at hj ⊢
    dsimp at hj ⊢
    rw [← hj]
    rfl
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant Profinite.exists_locallyConstant

end Profinite
