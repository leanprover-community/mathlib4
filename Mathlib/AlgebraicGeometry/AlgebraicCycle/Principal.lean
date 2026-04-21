module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

--import newRiemannRoch.Mathlib.Codimension
--import newRiemannRoch.Mathlib.AlgebraicCycle.Basic
--import newRiemannRoch.Mathlib.OrderOfVanishing.Scheme

/-!
# Principal Cycles

In this file we define the notion of a `principal` cycle, which is a slightly nonstandard notion
denoting those cycles which witness rational equivalence between two other cycles.
-/

@[expose] public section

open Filter Real Set Topology

open AlgebraicGeometry
open LocallyRingedSpace
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring
open TopologicalSpace

section Topology

open Topology

/-
These lemmas don't really belong in this file for when we eventually put this stuff in mathlib,
but I'm only using them here so it seems sensible enough to put them here for right now.
-/
variable {X : Type*} [TopologicalSpace X] (W V : Set X) [QuasiSober W] (hV : IsClosed V)

lemma QuasiSober.quasiSober_inter (hV : IsClosed V) : QuasiSober (W ∩ V : Set X) := by
  have : W ∩ V ⊆ W := Set.inter_subset_left
  have : IsClosedEmbedding <| Set.inclusion this := by
    refine IsClosedEmbedding.inclusion this ?_
    rw [Subtype.preimage_coe_self_inter W V]
    exact IsClosed.preimage_val hV
  exact Topology.IsClosedEmbedding.quasiSober this

def inter_homeo_val_preimage : ↑(W ∩ V) ≃ₜ ↑(Subtype.val (p := W) ⁻¹' V) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨⟨x, hx.1⟩, hx.2⟩
  invFun := fun ⟨⟨x, hx1⟩, hx2⟩ ↦ ⟨x, ⟨hx1, hx2⟩⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [QuasiSober ↑W] in
lemma NoetherianSpace.noetherian_inter [ntW : NoetherianSpace W] :
    NoetherianSpace <| (W ∩ V : Set X) := by
  convert @NoetherianSpace.set _ _ ntW (Subtype.val (p := W) ⁻¹' V)
  exact TopologicalSpace.noetherianSpace_iff_of_homeomorph <| inter_homeo_val_preimage W V

end Topology

section IrreducibleComponents

open Order TopologicalSpace Topology

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

lemma maximal_top_iff_isMax {α : Type*} (x : α) [LE α] : Maximal ⊤ x ↔ IsMax x := by
  simp [Maximal, IsMax]


/--
If a predicate `p` on `α` holds for all elements of `α`,
then `Subtype p` is order isomorphic to the original type.
-/
def subtypeUnivOrderIso {α : Type*} [LE α] {p : α → Prop} (h : ∀ (x : α), p x) :
  Subtype p ≃o α where
    __ := Equiv.subtypeUnivEquiv h
    map_rel_iff' := by simp

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
/--
In a sober topological space, the irreducible components are precisely the points with coheight
`0` in the specialization order.
-/
noncomputable
def coheightZeroSetOrderIsoIrreducibleComponents :
    {x : X | coheight x = 0} ≃o irreducibleComponents X := by
  have : {x : X | coheight x = 0} = {x : X | Maximal ⊤ x} := by simp [maximal_top_iff_isMax]
  rw [irreducibleComponents_eq_maximals_closed, this]
  exact OrderIso.mapSetOfMaximal <| OrderIso.trans
    (OrderIso.trans (subtypeUnivOrderIso (by tauto : ∀ x : X, ⊤))
    (irreducibleSetEquivPoints (α := X)).symm) <|
    TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' X

/--
For preorders `α` and `β`, if there is a strictly monotone function `f : WithTop α → β`, then if
`f x` has coheight `1`, then `x` has coheight `0`.
-/
lemma coheight_zero_of_coheight_one_of_strictMono
    {α β: Type*} [Preorder α] [Preorder β] (f : WithTop α → β) (hf : StrictMono f) (x : α)
    (h : coheight (f x) = 1) : coheight x = 0 := by
  suffices coheight (x : WithTop α) = 1 by
    simp only [coheight_coe_withTop] at this
    by_cases m : coheight x = ⊤
    · rw [m] at this
      contradiction
    · push_neg at m
      rw [ENat.ne_top_iff_exists] at m
      obtain ⟨a, ha⟩ := m
      rw [← ha] at this ⊢
      rw [← Nat.cast_one, ← ENat.coe_add, ENat.coe_inj] at this
      simp only [Nat.add_eq_right] at this
      rw [this, ENat.coe_zero]
  exact le_antisymm (h ▸ coheight_le_coheight_apply_of_strictMono f hf ↑x) (by simp)

/--
For types `X, Y` where `Y` is a quasisober, irreducible space, we can lift a function `f : X → Y`
to a function `f' : WithTop X → Y` sending `⊤` to a generic point of `Y`.
-/
noncomputable
def QuasiSober.withTopLift {X Y : Type*} [DecidableEq X] [TopologicalSpace Y] [QuasiSober Y]
    [IrreducibleSpace Y]
    (f : X → Y) : WithTop X → Y :=
  fun a ↦ if h : a = ⊤ then genericPoint Y else f (WithTop.untop a h)

noncomputable
def withtop_map' {X Y : Type*} [DecidableEq X] [Top Y]
    (f : X → Y) : WithTop X → Y := fun a ↦ if h : a = ⊤ then ⊤ else f (WithTop.untop a h)

/--
Given topological space `X, Y` and a function `f : X → Y` which is stricly monotone with respect
to the specialziation order, `QuasiSober.withTop_lift f` is strictly monotone with respect to the
specialization order.
-/
local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
lemma QuasiSober.withTopLift_strictMono {X Y : Type*} [DecidableEq X] [TopologicalSpace X]
    [TopologicalSpace Y]
    [QuasiSober Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : @StrictMono _ _ (specializationPreorder X) (specializationPreorder Y) f)
    (hf2 : ∀ x : X, f x < genericPoint Y) :
  @StrictMono _ _ (@WithTop.instPreorder _ (specializationPreorder X)) (specializationPreorder Y)
  (QuasiSober.withTopLift f) := fun a ↦ by aesop (add simp QuasiSober.withTopLift)

def IrreducibleCloseds.univ {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y] :
    IrreducibleCloseds Y where
  carrier := Set.univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

instance {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y] :
    OrderTop (IrreducibleCloseds Y) where
  top := IrreducibleCloseds.univ
  le_top := fun _ ↦ le_of_eq_of_le rfl fun _ _ ↦ trivial

/-
In principle it's probably better to prove this about irreducible closeds instead of points, but
who has the energy...

More seriously, we run into issues like the following, where we need to decide on a topological
space instance for WithTop X. Maybe we should just have this, I'm not sure - I suspect not though.

The sensible thing to do is just take the disjoint union of `X` and a point named `⊤` for this
instance if we ever decide to implement it.

lemma QuasiSober.withTopLift_strictMono' {X Y : Type*} [DecidableEq X] [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober Y] [IrreducibleSpace Y]
    {f : X → Y} (hf : Continuous f) (hf' : StrictMono <| IrreducibleCloseds.map f hf)
    (hf2 : ∀ x : IrreducibleCloseds X, IrreducibleCloseds.map f hf x < ⊤) :
  StrictMono (IrreducibleCloseds.map (QuasiSober.withTopLift f) sorry) := sorry-/

variable {X : Type*} {p : Set X} [TopologicalSpace X]

--set_option backward.isDefEq.respectTransparency false in
/--
For a subset `p` of a topoological space `X`, `Subtype.val` is strictly monotone with respect to the
specialization order.
-/
lemma Specialization.strictMono_val :
    @StrictMono _ _ (specializationPreorder p) (specializationPreorder X) Subtype.val :=
  fun _ _ _ ↦ by simp_all [LT.lt, subtype_specializes_iff, subtype_specializes_iff]

variable [QuasiSober X] [IrreducibleSpace X]

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
/--
In a quasisober, irreducible space `X`, if `p` is some non dense subset, then the generic point of
`X` specializes to any point of `p`.
-/
lemma QuasiSober.val_lt_genericPoint_of_closure_ne_top (hp : closure p ≠ univ) :
    ∀ x : p, @LT.lt X (specializationPreorder X).toLT (Subtype.val x) (genericPoint X) := by
  simp_all only [ne_eq, Subtype.forall]
  refine fun x hx ↦ ⟨genericPoint_specializes x, fun h ↦ ?_⟩
  have : closure {Subtype.val ⟨x, hx⟩} ⊆ closure p := closure_mono (by simp [hx])
  simp_all [specializes_iff_closure_subset]

variable [T0Space X]
/--
Note this is NOT USED ANYWHERE. I think it could be useful to have in the library, but it doesn't
belong in PRs relating to cycles.
-/
lemma eq_genericPoint_of_specializes_genericPoint (x : X) (hx : x ⤳ genericPoint X) :
    x = genericPoint X := IsGenericPoint.eq
  (le_antisymm (by simp) (by simpa [specializes_iff_closure_subset] using hx))
  (by simp [IsGenericPoint] : IsGenericPoint (genericPoint X) ⊤)

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
omit [T0Space X] in
/--
In a quasisober, irreducible space `X`, any set `p` which is not dense satisfies that the
set of points in `X` which lie in `p` and have coheight `1` in the specialization order on `X` have
coheight `0` in the specialization order on `p`.
-/
lemma QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one [DecidableEq X] (hp : closure p ≠ ⊤) :
    {x : X | x ∈ p ∧ coheight x = 1} ⊆ Subtype.val '' {x : p | coheight x = 0} := by
  simp only [Set.subset_def, Set.mem_setOf_eq, Set.mem_image,
    Subtype.exists, exists_and_right, exists_eq_right, and_imp]
  intro x hx kx
  use hx
  convert @coheight_zero_of_coheight_one_of_strictMono (Subtype p) X
    (specializationPreorder (Subtype p)) (specializationPreorder X)
    (QuasiSober.withTopLift (Subtype.val : Subtype p → X))
    (QuasiSober.withTopLift_strictMono (Subtype.val : Subtype p → X)
    Specialization.strictMono_val <| QuasiSober.val_lt_genericPoint_of_closure_ne_top hp) ⟨x, hx⟩ kx

  simp only [Subtype.preorder, Preorder.lift, specializationPreorder]
  ext a b
  exact (subtype_specializes_iff b a).symm

end IrreducibleComponents

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         {X Y : Scheme.{u}}

namespace AlgebraicCycle

open Multiplicative WithZero

def irreducibleComponents_irreducibleClosed (T : irreducibleComponents X) :
    IrreducibleCloseds X where
  carrier := T
  isIrreducible' := T.2.1
  isClosed' := isClosed_of_mem_irreducibleComponents T.1 T.2

open Set in
lemma ne_univ_of_sdiff_nonempty {α : Type*} {s u : Set α} (hu : u.Nonempty) : s \ u ≠ univ := by
  rw [ne_univ_iff_exists_notMem]
  use hu.some
  simp [hu.some_mem]


/--
This proof is fairly horrendous, but it remains so for a reason. A somewhat similar argument is used
to show that the pushforward is locally finite. This proof is about to have a fairly major
refactor which will generalize the context from schemes to more general topological spaces
with some suitable properties. It has already been cleaned up a huge amount and looks pretty ok now,
so in principle we could make the changes made there to this lemma, but I'm deferring doing this
until that lemma is in its final form. For now, just be happy this compiles.
-/
lemma div_locally_finite [DecidableEq X] [IsIntegral X] [nt : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : ∀ z ∈ (⊤ : Set X),
  ∃ t ∈ 𝓝 z,
  (t ∩ Function.support fun Z : X ↦ if h : coheight Z = 1
                                    then Multiplicative.toAdd <| WithZero.unzero (Scheme.ord_ne_zero h hf)
                                    else 0).Finite := by
    intro z hz
      -- Take `U` to be an open on which `f ∈ 𝒪(U)ˣ`
    obtain ⟨U, f', hU, hf'⟩ := Scheme.functionField_exists_unit_nhd f hf

    by_cases h : z ∈ U
    · /-
      By assumption, the order of vanishing at every point of `U` is trivial.
      Hence, if `z ∈ U`, we can take our neighbourhood to be `U`, where the support will be empty
      and hence clearly finite.
      -/
      use U
      refine ⟨IsOpen.mem_nhds U.2 h, ?_⟩
      convert finite_empty
      ext a
      simp only [mem_inter_iff, SetLike.mem_coe, Function.mem_support, ne_eq, dite_eq_right_iff,
        toAdd_eq_zero, not_forall, mem_empty_iff_false, iff_false, not_and, not_exists,
        Decidable.not_not]
      intro ha ha'
      suffices Scheme.ord a ha' f = 1 by aesop
      rw [← hf'.1]
      exact AlgebraicGeometry.Scheme.ord_of_isUnit _ _ hf'.2 _ _ ha

    · let XU := (⊤ : Set X) \ U
      have properClosed : XU ≠ univ ∧ IsClosed XU := by
        have := U.2
        unfold XU
        constructor
        · apply ne_univ_of_sdiff_nonempty ((Scheme.Opens.nonempty_iff _).mp hU)
          /-
          NOTE: This proof works, it's just that it should be replaced with a single lemma like the
          one above. Don't delete till this is all working.

          simp_all only [ne_eq, top_eq_univ, mem_univ, Opens.carrier_eq_coe, sdiff_eq_left,
          univ_disjoint, Opens.coe_eq_empty]
          convert hU
          simp only [Scheme.Opens.nonempty_iff]
          exact Opens.ne_bot_iff_nonempty U-/
        · apply IsClosed.sdiff isClosed_univ (Opens.isOpen U)


      /-
      All points where `f` has nontrivial vanishing must lie outside `U` (i.e. inside `XU`).

      !! Should be its own lemma !!
      -/
      have imp (y : X) (h : Order.coheight y = 1)
          (hy : Scheme.ord y h f ≠ 1) : y ∈ XU := by
        simp only [top_sdiff', hnot_eq_compl, mem_compl_iff, SetLike.mem_coe, XU]
        exact fun a ↦ hy (hf'.1 ▸ AlgebraicGeometry.Scheme.ord_of_isUnit _ _ hf'.2 _ h a)

      obtain ⟨W, hW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
        (x := z) (U := ⊤) (by simp)
      refine ⟨W, ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2.1, ?_⟩⟩

      /-
      Our strategy is to show that the points intersecting `W` of codimension `1` are just the
      irreducible components of `WXU`. Then, we show `WXU` is Noetherian and hence has finitely
      many irreducible components.
      -/
      let WXU := W.1 ∩ XU

      -- This should probably be an instance
      /-
      I.e. an affine subset of a locally noetherian space is a notherian space

      !! Should be its own lemma !!
      -/
      have ntW : NoetherianSpace W :=
        have : IsAffine W := hW.1
        have : IsNoetherianRing ↑Γ(↑W, ⊤) :=
          have := nt.1 ⟨W, hW.1⟩
          isNoetherianRing_of_ringEquiv Γ(X, W) W.topIso.commRingCatIsoToRingEquiv.symm
        AlgebraicGeometry.noetherianSpace_of_isAffine

      have : NoetherianSpace WXU := @NoetherianSpace.noetherian_inter _ _ W.1 XU ntW
      have ans : (irreducibleComponents WXU).Finite :=
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

      suffices {z ∈ WXU | coheight z = 1}.Finite by
          apply Finite.subset (by aesop : (WXU ∩ {z : X | coheight z = 1}).Finite)
          simp_all only [top_eq_univ, mem_univ, ne_eq, Opens.carrier_eq_coe, Opens.coe_top,
            subset_univ, and_true, subset_inter_iff]
          constructor
          · simp only [subset_def, mem_inter_iff, SetLike.mem_coe, Function.mem_support, ne_eq,
            dite_eq_right_iff, toAdd_eq_zero, not_forall, and_imp, forall_exists_index, WXU]
            intro a ha ha' _
            have : ¬(Scheme.ord a ha') f = 1 := by
              rwa [← coe_unzero (Scheme.ord_ne_zero ha' hf), ← coe_one, coe_inj]
            exact ⟨ha, imp a ha' this⟩
          · simp only [subset_def, mem_inter_iff, SetLike.mem_coe, Function.mem_support, ne_eq,
            dite_eq_right_iff, toAdd_eq_zero, not_forall, mem_setOf_eq, and_imp,
            forall_exists_index]
            exact fun _ _ c _ ↦ c

      have : closure WXU ≠ ⊤ := by
        have ans : closure WXU ⊆ closure XU := closure_mono <| by simp [WXU]
        aesop
      refine Finite.subset (Finite.image Subtype.val ?_)
        (QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one this)
      have qsW : QuasiSober W := instQuasiSoberCarrierCarrierCommRingCat W
      have : QuasiSober ↑WXU := @QuasiSober.quasiSober_inter _ _ W.1 XU qsW properClosed.2
      have := (Equiv.finite_iff
        (coheightZeroSetOrderIsoIrreducibleComponents (X := WXU)).toEquiv).mpr ans
      simp only [finite_coe_iff] at this
      convert this
      ext a b
      exact (subtype_specializes_iff b a).symm

open Classical in
/--
On an locally Noetherian integral scheme, given `f : X.functionField` and `hf : x ≠ 0`,
we define the principal Weil divisor `div f hf` as an algebraic cycle with coefficients in `ℤ`.
-/
noncomputable
def div [IsIntegral X] [nt : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : AlgebraicCycle X ℤ where
    toFun Z := if h : Order.coheight Z = 1
               then Multiplicative.toAdd <| WithZero.unzero (Scheme.ord_ne_zero h hf)
               else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := div_locally_finite f hf

@[simp]
lemma div_eq_zero_of_coheight_ne_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z ≠ 1) : div f hf Z = 0 := dif_neg hZ
@[simp]
lemma div_eq_ord_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z = 1) :
    div f hf Z = Multiplicative.toAdd (WithZero.unzero (Scheme.ord_ne_zero hZ hf)) := dif_pos hZ

/--
TODO: Generlize this beyond just being about cycles with coefficients in `ℤ`.
-/
lemma div_le_iff [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) {D : AlgebraicCycle X ℤ} (hD : ∀ z : X, coheight z ≠ 1 → D z ≥ 0):
    div f hf ≤ D ↔ ∀ z : X, coheight z = 1 → div f hf z ≤ D z := by
  refine ⟨fun h z _ ↦ h z, fun h z ↦ if hz : coheight z = 1 then h z hz else ?_⟩
  simp [div_eq_zero_of_coheight_ne_one _ _ _ hz]
  exact hD z hz

@[simp]
theorem div_homomorphism [IsIntegral X] [h : IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
    div (f * g) (by simp_all) = div f hf + div g hg := by
  ext a
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a from this
  simp only [div, map_mul]
  aesop (add simp unzero_mul)
--#check neg_ne_zero
lemma dumb {α : Type*} [Ring α] (a : α) : -a = -1 * a := neg_eq_neg_one_mul a

@[simp]
theorem div_neg [IsIntegral X] [h : IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) :
    div (- f) (neg_ne_zero.mpr hf) = div f hf := by

  have : (-1 : X.functionField) ≠ 0 := by grind

  have test : (-1 * f) ≠ 0 := by
    simp
    exact ⟨this, hf⟩
    --grind

  suffices div (-1 * f) test = div f hf by simpa [dumb f]
  rw[div_homomorphism (-1) this f hf]
  simp

  --simp [div]
  --exact AlgebraicGeometry.Scheme.ord_of_isUnit
    --have : -1 * f = -f :=
      --have : HasDistribNeg (X.functionField) := sorry
      --@neg_one_mul X.functionField _ sorry f
    --rw[div_homomorphism (-1) (sorry) f hf] at this

    --sorry
  --have : (-1 : X.functionField) ≠ 0 := by grind
  --rw[div_homomorphism (-1) (sorry) f hf]
  --simp
  /-
  TODO: This should be fairly easy with the stuff developed in OrderOfVanishing.Noetherian.
  -/
  sorry

/-
We have also developed some stuff on rational/linear equivalence in the original repo, but it is
still a bit rough at the moment. As it's not really needed for our Riemann-Roch proof, I've
chosen to omit it rather than cleaning it up for now, but I thought it would be good to mention
this as linear equivalence is a fairly glaring omission from any library about divisors.
-/
end AlgebraicCycle
