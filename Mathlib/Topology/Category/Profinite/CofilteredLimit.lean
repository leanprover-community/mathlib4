/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module topology.category.Profinite.cofiltered_limit
! leanprover-community/mathlib commit 178a32653e369dce2da68dc6b2694e385d484ef1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Profinite.Basic
import Mathbin.Topology.LocallyConstant.Basic
import Mathbin.Topology.DiscreteQuotient
import Mathbin.Topology.Category.Top.Limits.Cofiltered
import Mathbin.Topology.Category.Top.Limits.Konig

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_clopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/


namespace Profinite

open scoped Classical

open CategoryTheory

open CategoryTheory.Limits

universe u

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {F : J ⥤ Profinite.{u}} (C : Cone F)
  (hC : IsLimit C)

include hC

/-- If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_clopen_of_cofiltered {U : Set C.pt} (hU : IsClopen U) :
    ∃ (j : J) (V : Set (F.obj j)) (hV : IsClopen V), U = C.π.app j ⁻¹' V :=
  by
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB :=
    TopCat.isTopologicalBasis_cofiltered_limit.{u} (F ⋙ Profinite.toTopCat)
      (Profinite.to_Top.map_cone C) (is_limit_of_preserves _ hC) (fun j => {W | IsClopen W}) _
      (fun i => isClopen_univ) (fun i U1 U2 hU1 hU2 => hU1.inter hU2) _
  rotate_left
  · intro i
    change TopologicalSpace.IsTopologicalBasis {W : Set (F.obj i) | IsClopen W}
    apply isTopologicalBasis_clopen
  · rintro i j f V (hV : IsClopen _)
    refine' ⟨hV.1.preimage _, hV.2.preimage _⟩ <;> continuity
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S, hS, h⟩ := hB.open_eq_sUnion hU.1
  clear hB
  let j : S → J := fun s => (hS s.2).some
  let V : ∀ s : S, Set (F.obj (j s)) := fun s => (hS s.2).choose_spec.some
  have hV : ∀ s : S, IsClopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' V s := fun s =>
    (hS s.2).choose_spec.choose_spec
  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have := hU.2.IsCompact.elim_finite_subcover (fun s : S => C.π.app (j s) ⁻¹' V s) _ _
  rotate_left
  · intro s
    refine' (hV s).1.1.preimage _
    continuity
  · dsimp only
    rw [h]
    rintro x ⟨T, hT, hx⟩
    refine' ⟨_, ⟨⟨T, hT⟩, rfl⟩, _⟩
    dsimp only
    rwa [← (hV ⟨T, hT⟩).2]
  -- We thus obtain a finite set `G : finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G, hG⟩ := this
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  obtain ⟨j0, hj0⟩ := is_cofiltered.inf_objs_exists (G.image j)
  let f : ∀ (s : S) (hs : s ∈ G), j0 ⟶ j s := fun s hs =>
    (hj0 (finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let W : S → Set (F.obj j0) := fun s => if hs : s ∈ G then F.map (f s hs) ⁻¹' V s else Set.univ
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine' ⟨j0, ⋃ (s : S) (hs : s ∈ G), W s, _, _⟩
  · apply isClopen_biUnion_finset
    intro s hs
    dsimp only [W]
    rw [dif_pos hs]
    refine' ⟨(hV s).1.1.preimage _, (hV s).1.2.preimage _⟩ <;> continuity
  · ext x
    constructor
    · intro hx
      simp_rw [Set.preimage_iUnion, Set.mem_iUnion]
      obtain ⟨_, ⟨s, rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx
      refine' ⟨s, hs, _⟩
      dsimp only [W] at hh ⊢
      rwa [dif_pos hs, ← Set.preimage_comp, ← Profinite.coe_comp, C.w]
    · intro hx
      simp_rw [Set.preimage_iUnion, Set.mem_iUnion] at hx 
      obtain ⟨s, hs, hx⟩ := hx
      rw [h]
      refine' ⟨s.1, s.2, _⟩
      rw [(hV s).2]
      dsimp only [W] at hx 
      rwa [dif_pos hs, ← Set.preimage_comp, ← Profinite.coe_comp, C.w] at hx 
#align Profinite.exists_clopen_of_cofiltered Profinite.exists_clopen_of_cofiltered

theorem exists_locallyConstant_fin_two (f : LocallyConstant C.pt (Fin 2)) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (C.π.app _) :=
  by
  let U := f ⁻¹' {0}
  have hU : IsClopen U := f.is_locally_constant.is_clopen_fiber _
  obtain ⟨j, V, hV, h⟩ := exists_clopen_of_cofiltered C hC hU
  use j, LocallyConstant.ofClopen hV
  apply LocallyConstant.locallyConstant_eq_of_fiber_zero_eq
  rw [LocallyConstant.coe_comap _ _ (C.π.app j).Continuous]
  conv_rhs => rw [Set.preimage_comp]
  rw [LocallyConstant.ofClopen_fiber_zero hV, ← h]
#align Profinite.exists_locally_constant_fin_two Profinite.exists_locallyConstant_fin_two

theorem exists_locallyConstant_finite_aux {α : Type _} [Finite α] (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (α → Fin 2)),
      (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.app _) :=
  by
  cases nonempty_fintype α
  let ι : α → α → Fin 2 := fun x y => if x = y then 0 else 1
  let ff := (f.map ι).flip
  have hff := fun a : α => exists_locally_constant_fin_two _ hC (ff a)
  choose j g h using hff
  let G : Finset J := finset.univ.image j
  obtain ⟨j0, hj0⟩ := is_cofiltered.inf_objs_exists G
  have hj : ∀ a, j a ∈ G := by
    intro a
    simp [G]
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
  dsimp [ggg, gg]
  ext1
  repeat'
    rw [LocallyConstant.coe_comap]
    dsimp [LocallyConstant.flip, LocallyConstant.unflip]
  · congr 1
    change _ = (C.π.app j0 ≫ F.map (fs a)) x
    rw [C.w]
  all_goals continuity
#align Profinite.exists_locally_constant_finite_aux Profinite.exists_locallyConstant_finite_aux

theorem exists_locallyConstant_finite_nonempty {α : Type _} [Finite α] [Nonempty α]
    (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) :=
  by
  inhabit α
  obtain ⟨j, gg, h⟩ := exists_locally_constant_finite_aux _ hC f
  let ι : α → α → Fin 2 := fun a b => if a = b then 0 else 1
  let σ : (α → Fin 2) → α := fun f => if h : ∃ a : α, ι a = f then h.some else Inhabited.default _
  refine' ⟨j, gg.map σ, _⟩
  ext
  rw [LocallyConstant.coe_comap _ _ (C.π.app j).Continuous]
  dsimp [σ]
  have h1 : ι (f x) = gg (C.π.app j x) :=
    by
    change f.map (fun a b => if a = b then (0 : Fin 2) else 1) x = _
    rw [h, LocallyConstant.coe_comap _ _ (C.π.app j).Continuous]
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  rw [dif_pos h2]
  apply_fun ι
  · rw [h2.some_spec]
    exact h1
  · intro a b hh
    apply_fun fun e => e a at hh 
    dsimp [ι] at hh 
    rw [if_pos rfl] at hh 
    split_ifs at hh  with hh1 hh1
    · exact hh1.symm
    · exact False.elim (bot_ne_top hh)
#align Profinite.exists_locally_constant_finite_nonempty Profinite.exists_locallyConstant_finite_nonempty

/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
theorem exists_locallyConstant {α : Type _} (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) :=
  by
  let S := f.discrete_quotient
  let ff : S → α := f.lift
  cases isEmpty_or_nonempty S
  · suffices ∃ j, IsEmpty (F.obj j) by
      refine' this.imp fun j hj => _
      refine' ⟨⟨hj.elim, fun A => _⟩, _⟩
      · convert isOpen_empty
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
    have cond := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system (F ⋙ Profinite.toTopCat)
    suffices : Nonempty C.X; exact IsEmpty.false (S.proj this.some)
    let D := Profinite.to_Top.map_cone C
    have hD : is_limit D := is_limit_of_preserves Profinite.toTopCat hC
    have CD := (hD.cone_point_unique_up_to_iso (TopCat.limitConeIsLimit.{u} _)).inv
    exact cond.map CD
  · let f' : LocallyConstant C.X S := ⟨S.proj, S.proj_is_locally_constant⟩
    obtain ⟨j, g', hj⟩ := exists_locally_constant_finite_nonempty _ hC f'
    refine' ⟨j, ⟨ff ∘ g', g'.is_locally_constant.comp _⟩, _⟩
    ext1 t
    apply_fun fun e => e t at hj 
    rw [LocallyConstant.coe_comap _ _ (C.π.app j).Continuous] at hj ⊢
    dsimp at hj ⊢
    rw [← hj]
    rfl
#align Profinite.exists_locally_constant Profinite.exists_locallyConstant

end Profinite

