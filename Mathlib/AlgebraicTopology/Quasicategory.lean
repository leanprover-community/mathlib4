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

open MorphismProperty

/- a morphism is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  `∂Δ[n] ⟶ Δ[n]`. -/
def trivialKanFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ (n : ℕ), HasLiftingProperty (boundaryInclusion n) p

/- a morphism is an inner fibration if it has the right lifting property wrt
  every inner horn inclusion  `Λ[n, i] ⟶ Δ[n]`. -/
def innerFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
    HasLiftingProperty (hornInclusion (n+2) i) p

/- a morphism is inner anodyne if it has the left lifting property wrt all inner fibrations. -/
abbrev innerAnodyne := llp_wrt innerFibration

/- inner horn inclusions are inner anodyne. -/
lemma innerAnodyne_of_innerHorn
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    innerAnodyne (hornInclusion (n+2) i) := fun _ _ _ h ↦ h _h0 _hn

section Monomorphism

-- boundary inclusions are monomorphisms
instance boundaryInclusion_mono (n : ℕ) : Mono (boundaryInclusion n) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((boundaryInclusion n).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

open MonoidalCategory in
-- need that B ⊗ ∂Δ[n] ⟶ B ⊗ Δ[n] is a monomorphism for next lemma
instance boundaryInclusion_whisker_mono (B : SSet) (n : ℕ) : Mono (B ◁ (boundaryInclusion n)) := by
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

-- inner horn inclusions are monomorphisms
instance inner_horn_mono ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    monomorphisms SSet (hornInclusion (n+2) i) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((hornInclusion (n + 2) i).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

instance monomorphisms.StableUnderCobaseChange : StableUnderCobaseChange (monomorphisms SSet) := by
  intro A B A' B' f s f' t P hf
  letI _ : Mono f := hf
  letI _ : Adhesive SSet := adhesive_functor
  exact Adhesive.mono_of_isPushout_of_mono_right P

def transfinite_monos_aux (α : Ordinal) (F : {β | β ≤ α} ⥤ SSet) : Ordinal → Prop := fun γ ↦
  (hγ : γ ≤ α) → monomorphisms SSet (F.map (zero_to γ hγ))

instance transfinite_monos
    (X Y : SSet) (f : X ⟶ Y)
    (α : Ordinal)
    (F : {β | β ≤ α} ⥤ SSet) (hF : Limits.PreservesColimits F)
    (hS : ∀ (β : Ordinal) (hβ : β < α), monomorphisms SSet (F.map (to_succ hβ))) :
    ∀ {γ} (hγ : γ ≤ α), monomorphisms SSet (F.map (zero_to γ hγ)) := by
  intro γ hγ
  refine @Ordinal.limitRecOn (transfinite_monos_aux α F) γ ?_ ?_ ?_ hγ
  all_goals dsimp [transfinite_monos_aux]
  · intro; simp [zero_to]; exact instMonoId _
  · intro o IH (succ_le : o + 1 ≤ α)
    have o_lt : o < α := Order.succ_le_iff.mp succ_le
    have : (F.map (zero_to (Order.succ o) succ_le)) = (F.map (zero_to o (le_of_lt o_lt))) ≫
        (F.map (to_succ o_lt)) := by
      suffices (zero_to (Order.succ o) succ_le) = (zero_to o (le_of_lt o_lt)) ≫ (to_succ o_lt) by
        aesop
      simp only [Set.coe_setOf, Set.mem_setOf_eq, zero_to, to_succ, homOfLE_comp]
    rw [this]
    have a := IH (le_of_lt o_lt)
    have b := hS o o_lt
    exact @CategoryTheory.mono_comp SSet _ _ _ _
      (F.map (zero_to o (le_of_lt o_lt))) a (F.map (to_succ o_lt)) b
  · simp only [monomorphisms.iff]
    intro o ho IH o_le
    sorry -- because monomorphisms are closed under filtered colimits?
-- o is colimit of o' < o, and ∀ o' < o we have f_o'_0 : F(0) ⟶ F(o') is a Mono.
-- {o' | o' < o} is a filtered category (as a directed set), so o is a filtered colimit
-- F preserves colimits, so F(o) is a filtered colimit of F(o') for o' < o
-- since each F(0) ⟶ F(o') is a Mono, also F(0) ⟶ F(o) is a Mono

instance monomorphisms.StableUnderTransfiniteComposition :
    StableUnderTransfiniteComposition (monomorphisms SSet) := by
  intro X Y f hf
  induction hf with
  | mk α F hF hS => exact transfinite_monos X Y f α F hF hS (le_refl α)

-- `0077` (a) monomorphisms are weakly saturated
instance monomorphisms.WeaklySaturated : WeaklySaturated (monomorphisms SSet) :=
  ⟨ monomorphisms.StableUnderCobaseChange,
    monomorphisms.StableUnderRetracts,
    monomorphisms.StableUnderTransfiniteComposition⟩

-- `0077` (b) monomorphisms are generated by boundary inclusions
lemma contains_mono_of_contains_boundaryInclusion
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ (n : ℕ), S (boundaryInclusion n))
      → ∀ {A B : SSet} (i : A ⟶ B) [Mono i], S i := by
  sorry

/- `006Y` trivial Kan fibration iff rlp wrt all monomorphisms -/
lemma trivialKanFibration_iff_rlp_monomorphisms {X Y : SSet} (p : X ⟶ Y) :
    trivialKanFibration p ↔ rlp_wrt (monomorphisms SSet) p :=
  ⟨ contains_mono_of_contains_boundaryInclusion (llp_wrt' p) (llp_weakly_saturated' p),
    fun h n ↦ h (boundaryInclusion_mono n)⟩

-- innerAnodyne is WSC gen. by inner horn inclusions
lemma contains_innerAnodyne_of_contains_inner_horn
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)), S (hornInclusion (n+2) i))
      → (∀ {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p), S p) := by
  intro h X Y p hp
  sorry

-- innerAnodyne is generated by inner horn inclusions, which are monos and monos are saturated,
-- thus innerAnodynes are monos
lemma innerAnodyne_mono {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p) :
    monomorphisms SSet p :=
  contains_innerAnodyne_of_contains_inner_horn
    (monomorphisms SSet) monomorphisms.WeaklySaturated inner_horn_mono p hp

end Monomorphism

section _007E

-- `007E` (1), if extension property wrt every inner anodyne, then quasicat
-- to prove converse, need that class of inner anodyne morphisms is generated by inner horn inclusions
instance _007Ea {S : SSet}
    (h : ∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) :
    Quasicategory S where
  hornFilling' n i σ₀ _h0 _hn := h (hornInclusion (n + 2) i) (innerAnodyne_of_innerHorn _h0 _hn) σ₀

def ptIsTerminal : Limits.IsTerminal Δ[0] := sorry

abbrev proj (S : SSet) : S ⟶ Δ[0] := Limits.IsTerminal.from ptIsTerminal S

-- extension property wrt every inner anodyne morphism is equivalent to (S ⟶ Δ[0]) having RLP wrt
-- every inner anodyne morphism
lemma extension_iff_llp_proj {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    (rlp_wrt (innerAnodyne)) (proj S) := by
  refine ⟨?_, ?_⟩
  · intro h A B i hi
    refine ⟨?_⟩
    intro f₀ t sq
    obtain ⟨l, hl⟩ := h i hi f₀
    exact ⟨l, hl.symm, Limits.IsTerminal.hom_ext ptIsTerminal _ _⟩
  · intro h A B i hi f₀
    have : f₀ ≫ proj S = (i ≫ proj B) := Limits.IsTerminal.hom_ext ptIsTerminal _ _
    obtain ⟨⟨lift⟩⟩ := (h hi).sq_hasLift (CommSq.mk this)
    exact ⟨lift.l, lift.fac_left.symm⟩

-- since S is a quasicat, every inner horn inclusion has LLP wrt (S ⟶ Δ[0]), and
-- inner horn inclusions generate inner anodyne morphisms,
-- so all inner anodyne must have LLP wrt (S ⟶ Δ[0])

-- `007E`
-- quasicategory iff extension property wrt every inner anodyne morphism
instance {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    Quasicategory S := by
  refine ⟨_007Ea, ?_⟩
  intro hS
  rw [extension_iff_llp_proj]
  apply contains_innerAnodyne_of_contains_inner_horn (llp_wrt' S.proj)
    (llp_weakly_saturated' S.proj)
  intro n i _h0 _hn
  constructor
  intro σ₀ _ sq
  obtain ⟨l, hl⟩ := hS.hornFilling _h0 _hn σ₀
  use l
  exact hl.symm
  apply Limits.IsTerminal.hom_ext ptIsTerminal

end _007E

open MonoidalCategory MonoidalClosed

noncomputable
abbrev Fun : SSetᵒᵖ ⥤ SSet ⥤ SSet := internalHom

section _0079

-- pushout in `0079`,
-- inclusions of this into `Δ[2] ⊗ Δ[m]` generate the WSC of inner anodyne morphisms (`007F` (b))
def Δ_pushout (m : ℕ) :=
  IsPushout.of_hasPushout (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ boundaryInclusion m)

-- the cocone with point `Δ[2] ⊗ Δ[m]` given by the 4 natural maps
noncomputable
def Δ_cocone (m : ℕ) :
    Limits.PushoutCocone (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ boundaryInclusion m) :=
  Limits.PushoutCocone.mk (Δ[2] ◁ boundaryInclusion m) (hornInclusion 2 1 ▷ Δ[m]) rfl

-- induced morphism from pushout to `Δ[2] ⊗ Δ[m]` given by `Δ_cocone`
noncomputable
def to_Δ (m : ℕ) : (Δ_pushout m).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  (Δ_pushout m).isColimit.desc (Δ_cocone m)

-- the cocone with point `S` given by uncurrying the maps `α` and `β`
noncomputable
def S_cocone (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    Limits.PushoutCocone (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ boundaryInclusion m) := by
  let α' := MonoidalClosed.uncurry α
  let β' := MonoidalClosed.uncurry β
  refine Limits.PushoutCocone.mk α' β' ?_
  let w := sq.w
  ext n ⟨x, y⟩
  have := congr_fun (congr_app w n) y
  change ((MonoidalClosed.pre (hornInclusion 2 1)).app S).app n (α.app n y) =
    β.app n ((boundaryInclusion m).app n y) at this
  change α'.app n ((hornInclusion 2 1 ▷ ∂Δ[m]).app n (x, y)) =
    β'.app n ((Λ[2, 1] ◁ boundaryInclusion m).app n (x, y))
  simp [β', α', MonoidalClosed.uncurry]
  simp [ihom.adjunction, Closed.adj, FunctorToTypes.adj, FunctorToTypes.homEquiv,
    FunctorToTypes.homEquiv_invFun]
  rw [← this]
  simp [MonoidalClosed.pre]
  aesop

-- induced morphism from pushout to `S` given by `S_cocone`
noncomputable
def to_S (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    (Δ_pushout m).cocone.pt ⟶ S :=
  (Δ_pushout m).isColimit.desc (S_cocone S m sq)

open IsPushout in
-- the new square in `0079`
lemma newSquare (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    CommSq (to_S S m sq) (to_Δ m) S.proj (Δ[2] ⊗ Δ[m]).proj :=
  CommSq.mk (Limits.IsTerminal.hom_ext ptIsTerminal
    ((to_S S m sq) ≫ S.proj) ((to_Δ m) ≫ (Δ[2] ⊗ Δ[m]).proj))

lemma sqLift_iff_newSqLift (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    sq.HasLift ↔ (newSquare S m sq).HasLift := by
  refine ⟨?_, ?_⟩
  · intro ⟨lift, fac_left, fac_right⟩
    refine ⟨MonoidalClosed.uncurry lift, ?_, ?_⟩
    · refine ((Δ_pushout m).isColimit.uniq
        (S_cocone S m sq) (to_Δ m ≫ MonoidalClosed.uncurry lift) ?_).trans
        ((Δ_pushout m).isColimit.uniq (S_cocone S m sq) (S.to_S m sq) ?_).symm
      · intro j
        cases j
        · simp [S_cocone, to_Δ, Δ_cocone]
          apply_fun (fun f ↦ MonoidalClosed.uncurry f) at fac_left
          simp [uncurry_natural_left] at fac_left
          rw [← fac_left]
          --have := Limits.PushoutCocone.IsColimit.inl_desc (Δ_pushout m).isColimit
          --have := Limits.pushout.inl_desc
          sorry
        · rename_i k
          cases k
          sorry
          sorry
      · sorry
    · sorry
  · intro ⟨lift, fac_left, fac_right⟩
    refine ⟨MonoidalClosed.curry lift, ?_, ?_⟩
    ·
      sorry
    · sorry

-- `0079`, hard to show. still need `007F`
/- S is a quasicat iff Fun(Δ[2], S) ⟶ Fun(Λ[2, 1], S) is a trivial Kan fib -/
instance horn_tkf_iff_quasicat (S : SSet) : Quasicategory S ↔
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app S) := by
  refine ⟨?_, ?_⟩
  intro h
  intro m
  constructor
  intro α β sq
  rw [sqLift_iff_newSqLift]
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry
  sorry
  sorry

end _0079

/- changing the square to apply the lifting property of p
   on the monomorphism `(B ◁ boundaryInclusion n)` -/
lemma induced_tkf_aux (B X Y : SSet) (p : X ⟶ Y)
    (n : ℕ) [h : HasLiftingProperty (B ◁ boundaryInclusion n) p] :
    HasLiftingProperty (boundaryInclusion n) ((Fun.obj (Opposite.op B)).map p) where
  sq_hasLift sq :=
    (CommSq.left_adjoint_hasLift_iff sq (FunctorToTypes.adj B)).1
      (h.sq_hasLift (sq.left_adjoint (Closed.adj)))

-- `0071` (special case of `0070`)
/- if p : X ⟶ Y is a trivial Kan fib, then Fun(B,X) ⟶ Fun(B, Y) is -/
noncomputable
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) (hp: trivialKanFibration p) :
    trivialKanFibration ((Fun.obj (.op B)).map p) := by
  intro n
  have := (trivialKanFibration_iff_rlp_monomorphisms p).1 hp (boundaryInclusion_whisker_mono B n)
  apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `ihom_equiv` and `0079`
open MonoidalClosed in
noncomputable
def fun_quasicat_aux (S D : SSet) [Quasicategory D] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (.op S)).obj D)) := by
  intro n
  -- since Fun[Δ[n], D] ⟶ Fun[Λ[2,1], D] is a TKF by `0079`,
  -- get Fun(S, Fun(Δ[n], D)) ⟶ Fun(S, Fun(Λ[2,1], D)) is a TKF by `0071`
  have := (horn_tkf_iff_quasicat D).1 (by infer_instance)
  have := (induced_tkf S _ _ ((Fun.map (hornInclusion 2 1).op).app D)) this n
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
  (horn_tkf_iff_quasicat ((Fun.obj (.op S)).obj D)).2 (fun_quasicat_aux S D)

end SSet
