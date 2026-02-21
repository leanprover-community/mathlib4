/-
Copyright stuff
-/

module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Covering.Quotient

@[expose] public section

noncomputable section

namespace MulAction
-- auxiliar lemmas
-- necessary?

variable {M : Type*} [TopologicalSpace M]
variable {G : Type*} [Group G] [MulAction G M]
         [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
         [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
-- these are all necessary for isCoveringMap_quotientMk

-- isCoveringMap_quotientMk_of_properlyDiscontinuousSMul?
-- should it go in Mathlib.Topology.Covering.Quotient?
/-- If a group `G` acts properly discontinuously on a topological space `M`,
then the quotient map `Quotient.mk _ : M → M⧸G`
is a covering map. -/
lemma isCoveringMap_quotientMk :
    IsCoveringMap (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  IsQuotientCoveringMap.isCoveringMap (G:=_) (f:=_)
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul)

end MulAction

namespace QuotientMk
open MulAction

variable {M : Type*} [TopologicalSpace M]
variable {G : Type*} [Group G] [MulAction G M]
         [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
         [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]

-- where should this go?
-- should it have of_properlyDiscontinuousSMul?
-- or is it needed at all?
/-- If a group `G` acts properly discontinuously on a topological space `M`,
then the quotient map `Quotient.mk : M → M⧸G`
is a local homeomorphism. -/
lemma isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  isCoveringMap_quotientMk.isLocalHomeomorph

/-
from now on where should this go??
-/

/-- A chosen local homeomorphism for the quotient map
`Quotient.mk : M → M⧸G` at a point `p : M`. -/
noncomputable def localHomeomorphAt (p : M) :
    OpenPartialHomeomorph M (orbitRel.Quotient G M) :=
  Classical.choose (isLocalHomeomorph p)
-- this could just be
-- Classical.choose (isCoveringMap_quotientMk.isLocalHomeomorph p)

/-- The point `p` lies in the source of `localHomeomorphAt p`. -/
lemma mem_localHomeomorphAt_source {p : M} :
    p ∈ (localHomeomorphAt (G:=G) p).source :=
  (Classical.choose_spec (isLocalHomeomorph p)).1

/-- The local homeomorphism `localHomeomorphAt p` coincides with
`Quotient.mk : M → M⧸G`. -/
lemma localHomeomorphAt_eq_quotientMk {p : M} :
    localHomeomorphAt (G:=G) p =
      (Quotient.mk _ : M → orbitRel.Quotient G M) :=
  (Classical.choose_spec (isLocalHomeomorph p)).2.symm

/-- The equivalence class `⟦p⟧` lies in the target of `localHomeomorphAt p`. -/
lemma mem_localHomeomorphAt_target {p : M} :
    ⟦p⟧ ∈ (localHomeomorphAt (G:=G) p).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, Set.mem_image]
  refine ⟨p, mem_localHomeomorphAt_source, ?_⟩
  rw [localHomeomorphAt_eq_quotientMk]

/-- A chosen local inverse for the quotient map
`Quotient.mk : M → M⧸G` at a point `p : M`. -/
def localInverseAt (p : M) :
  OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
    (localHomeomorphAt p).symm

/-- The equivalence class `⟦p⟧` lies in the source of `localInverseAt p`. -/
lemma mem_localInverseAt_source {p : M} :
    ⟦p⟧ ∈ (localInverseAt (G:=G) p).source := by
  simp only [localInverseAt, OpenPartialHomeomorph.symm_source]
  exact mem_localHomeomorphAt_target

/-- If a point `k` lies on the source of `localHomeomorphAt p`
and its class `⟦k⟧` lies on the source of `localInverseAt p`,
then `localInverseAt p` sends `⟦k⟧` back to its representative `k`. -/
lemma localInverseAt_apply_other {p k : M}
    (h : k ∈ (localHomeomorphAt (G := G) p).source)
    (h' : ⟦k⟧ ∈ (localInverseAt (G := G) p).source) :
    (localInverseAt (G := G) p) ⟦k⟧ = k := by
  refine (localHomeomorphAt (G:=G) p).injOn ?_ h ?_
  · simp only [localInverseAt,
               OpenPartialHomeomorph.map_target (localHomeomorphAt p) h']
  · simp only [localInverseAt, (localHomeomorphAt p).right_inv h',
               localHomeomorphAt_eq_quotientMk]

/-- The local inverse at `p` sends the class `⟦p⟧` back to `p`. -/
lemma localInverseAt_apply_self {p : M}
    : (localInverseAt (G:=G) p) ⟦p⟧ = p :=
  localInverseAt_apply_other
    (mem_localHomeomorphAt_source)
    (mem_localInverseAt_source)


-- `IMPORTANT NOTE` : we actually don't use this next result

/-- If `k` lies in the source of `localHomeomorphAt p`, and its image
under `localHomeomorphAt p'` lies in the source of `localInverseAt p`,
then the composition `(localHomeomorphAt p').trans (localInverseAt p)`
sends `k` back to `k`. -/
lemma localHomeomorphAt_trans_eq_localInverseAt {p p' k : M}
    (h : k ∈ (localHomeomorphAt (G := G) p).source)
    (h' : (localHomeomorphAt p') k ∈ (localInverseAt (G := G) p).source)
    : ((localHomeomorphAt p').trans (localInverseAt (G := G) p)) k = k
    := by
  simp only [OpenPartialHomeomorph.coe_trans,
             localHomeomorphAt_eq_quotientMk,
             Function.comp_apply] at ⊢ h'
  exact localInverseAt_apply_other h h'

end QuotientMk

end
