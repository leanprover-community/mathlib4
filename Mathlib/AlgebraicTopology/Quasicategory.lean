/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.KanComplex
import Mathlib.AlgebraicTopology._InternalHom
import Mathlib.AlgebraicTopology._MorphismProperty
import Mathlib.CategoryTheory.Adhesive

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Nerve.lean`
we show (TODO) that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in `Mathlib/AlgebraicTopology/KanComplex.lean`.

-/

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.

[Kerodon, 003A] -/
class Quasicategory (S : SSet) : Prop where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : Δ[n+2] ⟶ S, σ₀ = hornInclusion (n+2) i ≫ σ

lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : Λ[n, i] ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_iff_val_lt_val] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory.

[Kerodon, 003C] -/
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

lemma quasicategory_of_filler (S : SSet)
    (filler : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : S _[n+2], ∀ (j) (h : j ≠ i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨(S.yonedaEquiv _).symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj, NatTrans.comp_app]
    rfl

/- p : X ⟶ Y is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  ∂Δ[n] ⟶ Δ[n] -/
class trivialKanFibration {X Y : SSet} (p : X ⟶ Y) : Prop where
  has_rlp (n : ℕ) : HasLiftingProperty (boundaryInclusion n) p

/- equivalent to trivial Kan fibration by `006Y` -/
class rlp_mono {X Y : SSet} (p : X ⟶ Y) where
  has_rlp {A B : SSet} (i : A ⟶ B) [Mono i] : HasLiftingProperty i p

section _006Y

open MorphismProperty

instance sset_mono_pushout : StableUnderCobaseChange (monomorphisms SSet) := by
  intro A B A' B' f s f' t P hf
  letI _ : Mono f := hf
  letI _ : Adhesive SSet := adhesive_functor
  exact Adhesive.mono_of_isPushout_of_mono_right P

def C_prop (α : Ordinal) (F : {β | β ≤ α} ⥤ SSet) : Ordinal → Prop := fun γ ↦
  (hγ : γ ≤ α) → monomorphisms SSet (F.map (gam γ hγ))

--
instance transfinite_monos
    (X Y : SSet) (f : X ⟶ Y)
    (α : Ordinal)
    (F : {β | β ≤ α} ⥤ SSet) (hF : Limits.PreservesColimits F)
    (hS : ∀ (β : Ordinal) (hβ : β < α), monomorphisms SSet (F.map (to_succ hβ))) :
      ∀ {γ} (hγ : γ ≤ α), monomorphisms SSet (F.map (gam γ hγ)) := by
  intro γ hγ
  refine @Ordinal.limitRecOn (C_prop α F) γ ?_ ?_ ?_ hγ
  dsimp [C_prop]
  · intro; simp [gam]; exact instMonoId (F.obj bot)
  · dsimp [C_prop]
    intro o IH (succ_le : o + 1 ≤ α)
    have o_lt : o < α := Order.succ_le_iff.mp succ_le
    have : (F.map (gam (Order.succ o) succ_le)) = (F.map (gam o (le_of_lt o_lt))) ≫
        (F.map (to_succ o_lt)) := by
      suffices (gam (Order.succ o) succ_le) = (gam o (le_of_lt o_lt)) ≫ (to_succ o_lt) by
        aesop
      simp only [Set.coe_setOf, Set.mem_setOf_eq, gam, to_succ, homOfLE_comp]
    rw [this]
    have a := IH (le_of_lt o_lt)
    have b := hS o o_lt
    exact @CategoryTheory.mono_comp SSet _ _ _ _
      (F.map (gam o (le_of_lt o_lt))) a (F.map (to_succ o_lt)) b
  · simp [C_prop]
    intro o ho IH o_le
    sorry -- because monomorphisms are closed under filtered colimits?

-- o is colimit of o' < o, and ∀ o' < o we have f_o'_0 : F(0) ⟶ F(o') is a Mono.
-- {o' | o' < o} is a filtered category (as a directed set), so o is a filtered colimit
-- F preserves colimits, so F(o) is a filtered colimit of F(o') for o' < o
-- since each F(0) ⟶ F(o') is a Mono, also F(0) ⟶ F(o) is a Mono


instance sset_mono_comp : StableUnderTransfiniteComposition (monomorphisms SSet) := by
  intro X Y f hf
  induction hf with
  | mk α F hF hS => exact transfinite_monos X Y f α F hF hS (le_refl α)

-- `0077` (a)
instance : WeaklySaturated (monomorphisms SSet) := ⟨sset_mono_pushout, mono_retract, sset_mono_comp⟩

-- Fix a TKF `p` and let `S` be the collection of all morphisms with LLP wrt `p`.
-- Then `S` contains all boundary inclusions
instance {X Y : SSet} (p : X ⟶ Y) [trivialKanFibration p] (n : ℕ) :
    llp_wrt' p (boundaryInclusion n) := trivialKanFibration.has_rlp n
-- and `S` is weakly saturated
instance {X Y : SSet} (p : X ⟶ Y) [trivialKanFibration p] : WeaklySaturated (llp_wrt' p) :=
  llp_weakly_saturated' p

-- `0077` (b) says that the WSC of monomorphisms is generated by boundary inclusions
-- since S contains all boundary inclusions and is weakly saturated, it contains all monomorphisms
-- thus all monomorphisms have LLP wrt p

-- `006Y`, need weakly satured stuff to prove, and `0077`
/- RLP wrt all monomorphisms iff trivial Kan fib -/
instance tkf_iff_rlp_mono {X Y : SSet} (p : X ⟶ Y) : trivialKanFibration p ↔
    ∀ {A B : SSet} (i : A ⟶ B) [Mono i], HasLiftingProperty i p := by
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

end _006Y

/- inner fibration if RLP wrt all inner horn inclusions -/
class innerFibration {X Y : SSet} (p : X ⟶ Y) where
  has_rlp ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    HasLiftingProperty (hornInclusion (n+2) i) p

/- inner anodyne if LLP wrt all inner fibrations -/
class innerAnodyne {A B : SSet} (i : A ⟶ B) where
  has_llp {X Y : SSet} (p : X ⟶ Y) [innerFibration p] : HasLiftingProperty i p

/- inner horn inclusions are inner anodyne -/
instance innerAnodyne_of_innerHorn
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    innerAnodyne (hornInclusion (n+2) i) where
  has_llp _ h := h.has_rlp _h0 _hn

-- `007E`, if extension property wrt every inner anodyne, then quasicat
-- to prove converse, need that class of inner anodyne morphisms is generated
-- by inner horn inclusions
instance {S : SSet}
    (h : ∀ {A B} (i : A ⟶ B) [innerAnodyne i] (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) :
    Quasicategory S where
  hornFilling' n i σ₀ _h0 _hn := by
    letI _ : innerAnodyne (hornInclusion (n + 2) i) := innerAnodyne_of_innerHorn _h0 _hn
    exact h (hornInclusion (n + 2) i) σ₀

open MonoidalCategory MonoidalClosed

noncomputable
abbrev Fun : SSetᵒᵖ ⥤ SSet ⥤ SSet := internalHom

-- pushout in `0079`
-- inclusions of this into Δ[2] ⊗ Δ[m] generate the WSC of inner anodyne morphisms (`007F`)
noncomputable
def pushout0079 (m : ℕ) :
    Limits.PushoutCocone (Λ[2, 1] ◁ boundaryInclusion m) (hornInclusion 2 1 ▷ ∂Δ[m]) :=
  Limits.PushoutCocone.mk (hornInclusion 2 1 ▷ Δ[m]) (Δ[2] ◁ boundaryInclusion m) (by aesop)

-- `0079`, hard to show
/- B is a quasicat iff Fun(Δ[2], B) ⟶ Fun(Λ[2, 1], B) is a trivial Kan fib -/
instance horn_tkf_iff_quasicat (B : SSet) : Quasicategory B ↔
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app B) := sorry

-- ∂Δ[n] ⟶ Δ[n] is a monomorphism
instance (n : ℕ) : Mono (boundaryInclusion n) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((boundaryInclusion n).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

-- need that B ⊗ ∂Δ[n] ⟶ B ⊗ Δ[n] is a monomorphism for next lemma
instance (B : SSet) (n : ℕ) : Mono (B ◁ (boundaryInclusion n)) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((B ◁ boundaryInclusion n).app k) := by
    intro k
    rw [mono_iff_injective]
    rintro ⟨b, x⟩ ⟨b', x'⟩ h
    apply Prod.ext_iff.1 at h
    apply Prod.ext
    · exact h.1
    · simp only [boundaryInclusion, whiskerLeft_app_apply] at h ⊢
      apply (Set.injective_codRestrict Subtype.property).mp
      exact fun ⦃a₁ a₂⦄ a ↦ a
      exact h.2
  apply NatTrans.mono_of_mono_app

/- changing the square to apply the lifting property of p
   on the monomorphism `(B ◁ boundaryInclusion n)` -/
lemma induced_tkf_aux (B X Y : SSet) (p : X ⟶ Y)
    [trivialKanFibration p] (n : ℕ) [h : HasLiftingProperty (B ◁ boundaryInclusion n) p] :
    HasLiftingProperty (boundaryInclusion n) ((Fun.obj (Opposite.op B)).map p) where
  sq_hasLift sq :=
    (CommSq.left_adjoint_hasLift_iff sq (FunctorToTypes.adj B)).1
      (h.sq_hasLift (sq.left_adjoint (Closed.adj)))

-- `0071` (special case of `0070`)
/- if p : X ⟶ Y is a trivial Kan fib, then Fun(B,X) ⟶ Fun(B, Y) is -/
noncomputable
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) [trivialKanFibration p] :
    trivialKanFibration ((Fun.obj (.op B)).map p) where
  has_rlp n := by
    have := (tkf_iff_rlp_mono p).1 (by infer_instance) (B ◁ (boundaryInclusion n))
    apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `ihom_equiv` and `0079`
open MonoidalClosed in
noncomputable
instance fun_quasicat_aux (S D : SSet) [Quasicategory D] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (.op S)).obj D)) where
  has_rlp n := by
    -- since Fun[Δ[n], D] ⟶ Fun[Λ[2,1], D] is a TKF by `0079`,
    -- get Fun(S, Fun(Δ[n], D)) ⟶ Fun(S, Fun(Λ[2,1], D)) is a TKF by `0071`
    have := (horn_tkf_iff_quasicat D).1 (by infer_instance)
    have := (induced_tkf S _ _ ((Fun.map (hornInclusion 2 1).op).app D)).has_rlp n
    dsimp at this
    have H : Arrow.mk ((ihom S).map ((MonoidalClosed.pre (hornInclusion 2 1)).app D)) ≅
        Arrow.mk ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (Opposite.op S)).obj D)) :=
      CategoryTheory.Comma.isoMk (ihom_iso' _ _ _) (ihom_iso' _ _ _)
    exact HasLiftingProperty.of_arrow_iso_right (boundaryInclusion n) H


-- what can be said for more general filling conditions?
-- `0066`
/- if D is a quasicat, then Fun(S, D) is -/
instance fun_quasicat (S D : SSet) [Quasicategory D] : Quasicategory ((Fun.obj (.op S)).obj D) :=
  -- instance inferred by `fun_quasicat_aux`
  (horn_tkf_iff_quasicat ((Fun.obj (.op S)).obj D)).2 (by infer_instance)

end SSet
