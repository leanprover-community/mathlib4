import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.SetTheory.Cardinal.UnivLE


namespace CategoryTheory
open Cardinal Limits

universe k k' w' w v₂ v₁ v u₂ u₁ u

instance univ_regular : Fact (Cardinal.univ.{k}.IsRegular) :=
  ⟨Cardinal.univ_inaccessible.{k}.2.1⟩

/-- Note: making this an instance has a tendency to produce loops. Use with caution. -/
def small_succ_trans (α : Type u) [Small.{k} α] : Small.{k + 1} α :=
  ⟨⟨ULift.{k + 1} (Shrink.{k} α), ⟨equivShrink α |>.trans Equiv.ulift.symm⟩⟩⟩

/-- A `k`-filtered category is one which `IsCardinalFiltered C Cardinal.univ.{k, k + 1}`. -/
@[pp_with_univ]
abbrev IsLevelFiltered (C : Type u) [Category.{v} C] :=
  IsCardinalFiltered C Cardinal.univ.{k, k + 1}

lemma hasCardinalLT_of_univ' (α : Type k) : HasCardinalLT α Cardinal.univ.{k, max k k'} := by
  simpa [HasCardinalLT] using lift_lt_univ' #α

lemma hasCardinalLT_of_univ (α : Type k) : HasCardinalLT α Cardinal.univ.{k, k + 1} := by
  simpa [HasCardinalLT] using lift_lt_univ' #α

  -- exact lift_strictMono.{_, k} (lift_mk_le'.mpr this)
lemma small_of_hasCardinalLT_univ {α : Type v}
  (h : HasCardinalLT α Cardinal.univ.{k, k + 1}) : Small.{k} α := by
  rw [small_iff_lift_mk_lt_univ]
  unfold HasCardinalLT at h
  simp only [lift_univ, gt_iff_lt] at h
  refine lt_of_eq_of_lt ?_ h
  rw [← lift_id (lift #α), lift_lift]

lemma hasCardinalLT_trans_univLE (α : Type u) (h : HasCardinalLT α Cardinal.univ.{k', k' + 1})
    [inst : UnivLE.{k', k}] : HasCardinalLT α Cardinal.univ.{k, k + 1} := by
  have := small_of_hasCardinalLT_univ h
  replace this := Small.trans_univLE α
  have shrink := hasCardinalLT_of_univ (Shrink α)
  exact hasCardinalLT_iff_of_equiv (equivShrink α).symm _ |>.mp shrink

namespace IsLevelFiltered
variable {J : Type u} [Category.{v} J] [IsLevelFiltered.{k} J] {K : Type k}

instance isFiltered_of_isLevelFiltered : IsFiltered J :=
  isFiltered_of_isCardinalDirected J Cardinal.univ.{k, k + 1}

attribute [local instance] small_succ_trans in
instance isLevelFilteredShrink [UnivLE.{k', k}] : IsLevelFiltered.{k'} J :=
  ⟨fun K [_] F h ↦ by
    have : Small.{k'} (Arrow K) := small_of_hasCardinalLT_univ h
    have : Small.{k + 1} K :=
      have := small_of_hasCardinalLT_univ (hasCardinalLT_of_hasCardinalLT_arrow h)
      have := Small.trans_univLE K
      inferInstance
    have : LocallySmall.{k + 1} K := ⟨fun X Y ↦
      have := small_of_injective (Arrow.mk_injective X Y)
      have := Small.trans_univLE (X ⟶ Y)
      inferInstance⟩
    let ε := (Shrink.equivalence K |>.trans <| ShrinkHoms.equivalence _)
    let F' := ε.inverse ⋙ F
    let ε' := Cocones.whiskeringEquivalence ε.symm (F := F)
    convert IsCardinalFiltered.nonempty_cocone F' (self := ‹IsLevelFiltered.{k} J›) ?_
    · exact ⟨fun ⟨c⟩ ↦ ⟨ε'.functor.obj c⟩, fun ⟨c'⟩ ↦ ⟨ε'.inverse.obj c'⟩⟩
    · simp
      unfold HasCardinalLT
      exact hasCardinalLT_trans_univLE (Arrow K) h ⟩


/-- If `S : K → J` is a family of objects of size `k`, this is a choice
of an object in `J` which is the target of a map from all of the objects `S k`. -/
noncomputable abbrev max (S : K → J) :=
  IsCardinalFiltered.max.{k + 1} (κ := Cardinal.univ.{k}) S <| hasCardinalLT_of_univ K

/-- If `S : K → J` is a family of objects of size `k`, this is a choice of map
`S k ⟶ max S` for any `k : K`. -/
noncomputable abbrev toMax (S : K → J) (k : K) : S k ⟶ max S :=
  IsCardinalFiltered.toMax.{k + 1} (κ := Cardinal.univ.{k}) S (hasCardinalLT_of_univ K) k

/-- Given a family of maps `f : K → (j ⟶ j')` in a `k`-filtered category `J` with
`(K : Type k)`, this is an object of J where these morphisms shall be equalized. -/
noncomputable abbrev coeq {j j' : J} (f : K → (j ⟶ j')) : J :=
  IsCardinalFiltered.coeq.{k + 1} (κ := Cardinal.univ.{k}) f <| hasCardinalLT_of_univ K

/-- Given a family of maps `f : K → (j ⟶ j')` in a `k`-filtered category `J` with
`(K : Type k)`, this is a choice of morphism `j' ⟶ coeq f hK`. -/
noncomputable abbrev coeqHom {j j' : J} (f : K → (j ⟶ j')) : j' ⟶ coeq f :=
  IsCardinalFiltered.coeqHom.{k + 1} (κ := Cardinal.univ.{k}) f <| hasCardinalLT_of_univ K

/-- Given a family of maps `f : K → (j ⟶ j')` in a `k`-filtered category `J` with
`(K : Type k)`, this is a morphism `j ⟶ coeq f` which is equal to `f k ≫ coeqHom f`
for all `k : K`. -/
noncomputable abbrev toCoeq {j j' : J} (f : K → (j ⟶ j')) : j ⟶ coeq f :=
  IsCardinalFiltered.toCoeq.{k + 1} (κ := Cardinal.univ.{k}) f (hasCardinalLT_of_univ K)

@[reassoc (attr := simp)]
lemma coeq_condition {j j' : J} (f : K → (j ⟶ j')) (k : K) : f k ≫ coeqHom f = toCoeq f :=
  IsCardinalFiltered.coeq_condition.{k + 1} (κ := Cardinal.univ.{k}) f (hasCardinalLT_of_univ K) k

@[reassoc (attr := simp)]
lemma coeq_condition' {j j' : J} (f : K → (j ⟶ j')) k₁ k₂ :
    f k₁ ≫ coeqHom f = f k₂ ≫ coeqHom f := by
  simp_rw [coeq_condition]

end CategoryTheory.IsLevelFiltered
