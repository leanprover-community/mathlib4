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

-- include hC
-- Porting note: I just add `(hC : IsLimit C)` explicitly as a hypothesis to all the theorems

/-- If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_clopen_of_cofiltered {U : Set C.pt} (hC : IsLimit C) (hU : IsClopen U) :
    ∃ (j : J) (V : Set (F.obj j)) (_ : IsClopen V), U = C.π.app j ⁻¹' V := by
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB := TopCat.isTopologicalBasis_cofiltered_limit.{u, u} (F ⋙ Profinite.toTopCat)
      (Profinite.toTopCat.mapCone C) (isLimitOfPreserves _ hC) (fun j => {W | IsClopen W}) ?_
      (fun i => isClopen_univ) (fun i U1 U2 hU1 hU2 => hU1.inter hU2) ?_
  rotate_left
  · intro i
    -- ⊢ TopologicalSpace.IsTopologicalBasis ((fun j => {W | IsClopen W}) i)
    change TopologicalSpace.IsTopologicalBasis {W : Set (F.obj i) | IsClopen W}
    -- ⊢ TopologicalSpace.IsTopologicalBasis {W | IsClopen W}
    apply isTopologicalBasis_clopen
    -- 🎉 no goals
  · rintro i j f V (hV : IsClopen _)
    -- ⊢ ↑((F ⋙ toTopCat).map f) ⁻¹' V ∈ (fun j => {W | IsClopen W}) i
    exact ⟨hV.1.preimage ((F ⋙ toTopCat).map f).continuous,
      hV.2.preimage ((F ⋙ toTopCat).map f).continuous⟩
    -- Porting note: `<;> continuity` fails
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S, hS, h⟩ := hB.open_eq_sUnion hU.1
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  clear hB
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  let j : S → J := fun s => (hS s.2).choose
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  let V : ∀ s : S, Set (F.obj (j s)) := fun s => (hS s.2).choose_spec.choose
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  have hV : ∀ s : S, IsClopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' V s := fun s =>
    (hS s.2).choose_spec.choose_spec

  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have hUo : ∀ (i : ↑S), IsOpen ((fun s ↦ (forget Profinite).map (C.π.app (j s)) ⁻¹' V s) i)
  -- ⊢ ∀ (i : ↑S), IsOpen ((fun s => (forget Profinite).map (NatTrans.app C.π (j s) …
  · intro s
    -- ⊢ IsOpen ((fun s => (forget Profinite).map (NatTrans.app C.π (j s)) ⁻¹' V s) s)
    exact (hV s).1.1.preimage (C.π.app (j s)).continuous
    -- 🎉 no goals
  have hsU : U ⊆ ⋃ (i : ↑S), (fun s ↦ (forget Profinite).map (C.π.app (j s)) ⁻¹' V s) i
  -- ⊢ U ⊆ ⋃ (i : ↑S), (fun s => (forget Profinite).map (NatTrans.app C.π (j s)) ⁻¹ …
  · dsimp only
    -- ⊢ U ⊆ ⋃ (i : ↑S), (forget Profinite).map (NatTrans.app C.π (Exists.choose (_ : …
    rw [h]
    -- ⊢ ⋃₀ S ⊆ ⋃ (i : ↑S), (forget Profinite).map (NatTrans.app C.π (Exists.choose ( …
    rintro x ⟨T, hT, hx⟩
    -- ⊢ x ∈ ⋃ (i : ↑S), (forget Profinite).map (NatTrans.app C.π (Exists.choose (_ : …
    refine' ⟨_, ⟨⟨T, hT⟩, rfl⟩, _⟩
    -- ⊢ x ∈ (fun i => (forget Profinite).map (NatTrans.app C.π (Exists.choose (_ : ↑ …
    dsimp only [forget_map_eq_coe]
    -- ⊢ x ∈ ↑(NatTrans.app C.π (Exists.choose (_ : T ∈ {U | ∃ j V, V ∈ (fun j => {W  …
    rwa [← (hV ⟨T, hT⟩).2]
    -- 🎉 no goals
  have := hU.2.isCompact.elim_finite_subcover (fun s : S => C.π.app (j s) ⁻¹' V s) hUo hsU
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  -- Porting note: same remark as after `hB`
  -- We thus obtain a finite set `G : Finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G, hG⟩ := this
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists (G.image j)
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  let f : ∀ (s : S) (_ : s ∈ G), j0 ⟶ j s := fun s hs =>
    (hj0 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let W : S → Set (F.obj j0) := fun s => if hs : s ∈ G then F.map (f s hs) ⁻¹' V s else Set.univ
  -- ⊢ ∃ j V x, U = ↑(NatTrans.app C.π j) ⁻¹' V
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine' ⟨j0, ⋃ (s : S) (_ : s ∈ G), W s, _, _⟩
  -- ⊢ IsClopen (⋃ (s : ↑S) (_ : s ∈ G), W s)
  · apply isClopen_biUnion_finset
    -- ⊢ ∀ (i : ↑S), i ∈ G → IsClopen (W i)
    intro s hs
    -- ⊢ IsClopen (W s)
    dsimp
    -- ⊢ IsClopen (if hs : s ∈ G then ↑(F.map (Nonempty.some (_ : Nonempty (j0 ⟶ Exis …
    rw [dif_pos hs]
    -- ⊢ IsClopen (↑(F.map (Nonempty.some (_ : Nonempty (j0 ⟶ Exists.choose (_ : ↑s ∈ …
    exact ⟨(hV s).1.1.preimage (F.map _).continuous, (hV s).1.2.preimage (F.map _).continuous⟩
    -- 🎉 no goals
  · ext x
    -- ⊢ x ∈ U ↔ x ∈ ↑(NatTrans.app C.π j0) ⁻¹' ⋃ (s : ↑S) (_ : s ∈ G), W s
    constructor
    -- ⊢ x ∈ U → x ∈ ↑(NatTrans.app C.π j0) ⁻¹' ⋃ (s : ↑S) (_ : s ∈ G), W s
    · intro hx
      -- ⊢ x ∈ ↑(NatTrans.app C.π j0) ⁻¹' ⋃ (s : ↑S) (_ : s ∈ G), W s
      simp_rw [Set.preimage_iUnion, Set.mem_iUnion]
      -- ⊢ ∃ i i_1, x ∈ ↑(NatTrans.app C.π j0) ⁻¹' if h : i ∈ G then ↑(F.map (Nonempty. …
      obtain ⟨_, ⟨s, rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx
      -- ⊢ ∃ i i_1, x ∈ ↑(NatTrans.app C.π j0) ⁻¹' if h : i ∈ G then ↑(F.map (Nonempty. …
      refine' ⟨s, hs, _⟩
      -- ⊢ x ∈ ↑(NatTrans.app C.π j0) ⁻¹' if h : s ∈ G then ↑(F.map (Nonempty.some (_ : …
      rwa [dif_pos hs, ← Set.preimage_comp, ← Profinite.coe_comp, ← Functor.map_comp, C.w]
      -- 🎉 no goals
    · intro hx
      -- ⊢ x ∈ U
      simp_rw [Set.preimage_iUnion, Set.mem_iUnion] at hx
      -- ⊢ x ∈ U
      obtain ⟨s, hs, hx⟩ := hx
      -- ⊢ x ∈ U
      rw [h]
      -- ⊢ x ∈ ⋃₀ S
      refine' ⟨s.1, s.2, _⟩
      -- ⊢ x ∈ ↑s
      rw [(hV s).2]
      -- ⊢ x ∈ ↑(NatTrans.app C.π (j s)) ⁻¹' V s
      rwa [dif_pos hs, ← Set.preimage_comp, ← Profinite.coe_comp, ← Functor.map_comp, C.w] at hx
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Profinite.exists_clopen_of_cofiltered Profinite.exists_clopen_of_cofiltered

theorem exists_locallyConstant_fin_two (hC : IsLimit C) (f : LocallyConstant C.pt (Fin 2)) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (C.π.app _) := by
  let U := f ⁻¹' {0}
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  have hU : IsClopen U := f.isLocallyConstant.isClopen_fiber _
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  obtain ⟨j, V, hV, h⟩ := exists_clopen_of_cofiltered C hC hU
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  use j, LocallyConstant.ofClopen hV
  -- ⊢ f = LocallyConstant.comap (↑(NatTrans.app C.π j)) (LocallyConstant.ofClopen  …
  apply LocallyConstant.locallyConstant_eq_of_fiber_zero_eq
  -- ⊢ ↑f ⁻¹' {0} = ↑(LocallyConstant.comap (↑(NatTrans.app C.π j)) (LocallyConstan …
  rw [LocallyConstant.coe_comap _ _ (C.π.app j).continuous]
  -- ⊢ ↑f ⁻¹' {0} = ↑(LocallyConstant.ofClopen hV) ∘ ↑(NatTrans.app C.π j) ⁻¹' {0}
  conv_rhs => rw [Set.preimage_comp]
  -- ⊢ ↑f ⁻¹' {0} = ↑(NatTrans.app C.π j) ⁻¹' (↑(LocallyConstant.ofClopen hV) ⁻¹' { …
  rw [LocallyConstant.ofClopen_fiber_zero hV, ← h]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant_fin_two Profinite.exists_locallyConstant_fin_two

theorem exists_locallyConstant_finite_aux {α : Type*} [Finite α] (hC : IsLimit C)
    (f : LocallyConstant C.pt α) : ∃ (j : J) (g : LocallyConstant (F.obj j) (α → Fin 2)),
      (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.app _) := by
  cases nonempty_fintype α
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  let ι : α → α → Fin 2 := fun x y => if x = y then 0 else 1
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  let ff := (f.map ι).flip
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  have hff := fun a : α => exists_locallyConstant_fin_two _ hC (ff a)
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  choose j g h using hff
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  let G : Finset J := Finset.univ.image j
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists G
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  have hj : ∀ a, j a ∈ (Finset.univ.image j : Finset J) := by
    intro a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]
  let fs : ∀ a : α, j0 ⟶ j a := fun a => (hj0 (hj a)).some
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  let gg : α → LocallyConstant (F.obj j0) (Fin 2) := fun a => (g a).comap (F.map (fs _))
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  let ggg := LocallyConstant.unflip gg
  -- ⊢ ∃ j g, LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyCo …
  refine' ⟨j0, ggg, _⟩
  -- ⊢ LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyConstant. …
  have : f.map ι = LocallyConstant.unflip (f.map ι).flip := by simp
  -- ⊢ LocallyConstant.map (fun a b => if a = b then 0 else 1) f = LocallyConstant. …
  rw [this]; clear this
  -- ⊢ LocallyConstant.unflip (LocallyConstant.flip (LocallyConstant.map ι f)) = Lo …
             -- ⊢ LocallyConstant.unflip (LocallyConstant.flip (LocallyConstant.map ι f)) = Lo …
  have :
    LocallyConstant.comap (C.π.app j0) ggg =
      LocallyConstant.unflip (LocallyConstant.comap (C.π.app j0) ggg).flip :=
    by simp
  rw [this]; clear this
  -- ⊢ LocallyConstant.unflip (LocallyConstant.flip (LocallyConstant.map ι f)) = Lo …
             -- ⊢ LocallyConstant.unflip (LocallyConstant.flip (LocallyConstant.map ι f)) = Lo …
  congr 1
  -- ⊢ LocallyConstant.flip (LocallyConstant.map ι f) = LocallyConstant.flip (Local …
  ext1 a
  -- ⊢ LocallyConstant.flip (LocallyConstant.map ι f) a = LocallyConstant.flip (Loc …
  change ff a = _
  -- ⊢ ff a = LocallyConstant.flip (LocallyConstant.comap (↑(NatTrans.app C.π j0))  …
  rw [h]
  -- ⊢ LocallyConstant.comap (↑(NatTrans.app C.π (j a))) (g a) = LocallyConstant.fl …
  dsimp
  -- ⊢ LocallyConstant.comap (↑(NatTrans.app C.π (j a))) (g a) = LocallyConstant.fl …
  ext1 x
  -- ⊢ ↑(LocallyConstant.comap (↑(NatTrans.app C.π (j a))) (g a)) x = ↑(LocallyCons …
  rw [LocallyConstant.coe_comap _ _ (C.π.app (j a)).continuous]
  -- ⊢ (↑(g a) ∘ ↑(NatTrans.app C.π (j a))) x = ↑(LocallyConstant.flip (LocallyCons …
  dsimp [LocallyConstant.flip, LocallyConstant.unflip]
  -- ⊢ ↑(g a) (↑(NatTrans.app C.π (j a)) x) = ↑(LocallyConstant.comap ↑(NatTrans.ap …
  rw [LocallyConstant.coe_comap _ _ (C.π.app j0).continuous]
  -- ⊢ ↑(g a) (↑(NatTrans.app C.π (j a)) x) = (↑{ toFun := fun x a => ↑(LocallyCons …
  dsimp
  -- ⊢ ↑(g a) (↑(NatTrans.app C.π (j a)) x) = ↑(LocallyConstant.comap (↑(F.map (Non …
  rw [LocallyConstant.coe_comap _ _ _]
  -- ⊢ ↑(g a) (↑(NatTrans.app C.π (j a)) x) = (↑(g a) ∘ ↑(F.map (Nonempty.some (_ : …
  -- Porting note: `repeat' rw [LocallyConstant.coe_comap]` didn't work
  -- so I did all three rewrites manually
  · dsimp
    -- ⊢ ↑(g a) (↑(NatTrans.app C.π (j a)) x) = ↑(g a) (↑(F.map (Nonempty.some (_ : N …
    congr! 1
    -- ⊢ ↑(NatTrans.app C.π (j a)) x = ↑(F.map (Nonempty.some (_ : Nonempty (j0 ⟶ j a …
    change _ = (C.π.app j0 ≫ F.map (fs a)) x
    -- ⊢ ↑(NatTrans.app C.π (j a)) x = ↑(NatTrans.app C.π j0 ≫ F.map (fs a)) x
    rw [C.w]
    -- 🎉 no goals
  · exact (F.map _).continuous
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant_finite_aux Profinite.exists_locallyConstant_finite_aux

theorem exists_locallyConstant_finite_nonempty {α : Type*} [Finite α] [Nonempty α]
    (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  inhabit α
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  obtain ⟨j, gg, h⟩ := exists_locallyConstant_finite_aux _ hC f
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  let ι : α → α → Fin 2 := fun a b => if a = b then 0 else 1
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  let σ : (α → Fin 2) → α := fun f => if h : ∃ a : α, ι a = f then h.choose else default
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  refine' ⟨j, gg.map σ, _⟩
  -- ⊢ f = LocallyConstant.comap (↑(NatTrans.app C.π j)) (LocallyConstant.map σ gg)
  ext x
  -- ⊢ ↑f x = ↑(LocallyConstant.comap (↑(NatTrans.app C.π j)) (LocallyConstant.map  …
  rw [LocallyConstant.coe_comap _ _ (C.π.app j).continuous]
  -- ⊢ ↑f x = (↑(LocallyConstant.map σ gg) ∘ ↑(NatTrans.app C.π j)) x
  dsimp
  -- ⊢ ↑f x = if h : ∃ a, (fun b => if a = b then 0 else 1) = ↑gg (↑(NatTrans.app C …
  have h1 : ι (f x) = gg (C.π.app j x) := by
    change f.map (fun a b => if a = b then (0 : Fin 2) else 1) x = _
    rw [h, LocallyConstant.coe_comap _ _ (C.π.app j).continuous]
    rfl
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  -- ⊢ ↑f x = if h : ∃ a, (fun b => if a = b then 0 else 1) = ↑gg (↑(NatTrans.app C …
  rw [dif_pos h2]
  -- ⊢ ↑f x = Exists.choose h2
  apply_fun ι
  -- ⊢ ι (↑f x) = ι (Exists.choose h2)
  · rw [h2.choose_spec]
    -- ⊢ ι (↑f x) = ↑gg (↑(NatTrans.app C.π j) x)
    exact h1
    -- 🎉 no goals
  · intro a b hh
    -- ⊢ a = b
    have hhh := congr_fun hh a
    -- ⊢ a = b
    dsimp at hhh
    -- ⊢ a = b
    rw [if_pos rfl] at hhh
    -- ⊢ a = b
    split_ifs at hhh with hh1
    -- ⊢ a = b
    · exact hh1.symm
      -- 🎉 no goals
    · exact False.elim (bot_ne_top hhh)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant_finite_nonempty Profinite.exists_locallyConstant_finite_nonempty

/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
theorem exists_locallyConstant {α : Type*} (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  let S := f.discreteQuotient
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  let ff : S → α := f.lift
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
  cases isEmpty_or_nonempty S
  -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
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
    -- ⊢ ¬∀ (x : J), Nonempty ↑(F.obj x).toCompHaus.toTop
    intro h
    -- ⊢ False
    haveI : ∀ j : J, Nonempty ((F ⋙ Profinite.toTopCat).obj j) := h
    -- ⊢ False
    haveI : ∀ j : J, T2Space ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : T2Space (F.obj j))
    haveI : ∀ j : J, CompactSpace ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : CompactSpace (F.obj j))
    have cond := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u}
      (F ⋙ Profinite.toTopCat)
    suffices : Nonempty C.pt; exact IsEmpty.false (S.proj this.some)
    -- ⊢ False
                              -- ⊢ Nonempty ↑C.pt.toCompHaus.toTop
    let D := Profinite.toTopCat.mapCone C
    -- ⊢ Nonempty ↑C.pt.toCompHaus.toTop
    have hD : IsLimit D := isLimitOfPreserves Profinite.toTopCat hC
    -- ⊢ Nonempty ↑C.pt.toCompHaus.toTop
    have CD := (hD.conePointUniqueUpToIso (TopCat.limitConeIsLimit.{u, u} _)).inv
    -- ⊢ Nonempty ↑C.pt.toCompHaus.toTop
    exact cond.map CD
    -- 🎉 no goals
  · let f' : LocallyConstant C.pt S := ⟨S.proj, S.proj_isLocallyConstant⟩
    -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
    obtain ⟨j, g', hj⟩ := exists_locallyConstant_finite_nonempty _ hC f'
    -- ⊢ ∃ j g, f = LocallyConstant.comap (↑(NatTrans.app C.π j)) g
    refine' ⟨j, ⟨ff ∘ g', g'.isLocallyConstant.comp _⟩, _⟩
    -- ⊢ f = LocallyConstant.comap ↑(NatTrans.app C.π j) { toFun := ff ∘ ↑g', isLocal …
    ext1 t
    -- ⊢ ↑f t = ↑(LocallyConstant.comap ↑(NatTrans.app C.π j) { toFun := ff ∘ ↑g', is …
    apply_fun fun e => e t at hj
    -- ⊢ ↑f t = ↑(LocallyConstant.comap ↑(NatTrans.app C.π j) { toFun := ff ∘ ↑g', is …
    rw [LocallyConstant.coe_comap _ _ (C.π.app j).continuous] at hj ⊢
    -- ⊢ ↑f t = (↑{ toFun := ff ∘ ↑g', isLocallyConstant := (_ : IsLocallyConstant (f …
    dsimp at hj ⊢
    -- ⊢ ↑f t = ↑(LocallyConstant.lift f) (↑g' (↑(NatTrans.app C.π j) t))
    rw [← hj]
    -- ⊢ ↑f t = ↑(LocallyConstant.lift f) (DiscreteQuotient.proj (LocallyConstant.dis …
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Profinite.exists_locally_constant Profinite.exists_locallyConstant

end Profinite
