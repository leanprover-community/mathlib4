import Mathlib.Order.SuccPred.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.Module.GradedModule


universe u v w z


variable {R : Type u} {M : Type v} {ι : Type w}
[Ring R] [AddCommGroup M] [Module R M] [OrderedAddCommMonoid ι] [PredOrder ι] [Bot ι]

-- better names (hausdorff?)
class FilteredModule (𝓜 : ι → Submodule R M) where
  whole : ⨆ i, 𝓜 i = ⊤
  mono : Monotone 𝓜
  bot : 𝓜 ⊥ = ⊥


namespace FilteredModule

--do same for succOrder (and withTop)
instance instPred {α : Type w} [OrderedAddCommMonoid α] [PredOrder α] [d : DecidableEq α] :
  PredOrder (WithBot α) where
  pred a := match a with
    | none => none
    | some a => WithBot.some (Order.pred a)
  pred_le a := match a with
    | none => sorry
    | some a => by
      simp

      sorry
  min_of_le_pred := sorry
  le_pred_of_lt := sorry
  le_of_pred_lt := sorry

def ofNoBot {α : Type w} [OrderedAddCommMonoid α] [PredOrder α] (𝓜 : α → Submodule R M) :
  WithBot α → Submodule R M := fun a => match a with
  | none => ⊥
  | some a => 𝓜 a

instance instOf {α : Type w} [OrderedAddCommMonoid α] [PredOrder α] (𝓜 : α → Submodule R M)
  (w : ⨆ i, 𝓜 i = ⊤)  (m : Monotone 𝓜) : FilteredModule (ofNoBot 𝓜) where
    whole := sorry
    mono := sorry
    bot := sorry

abbrev pred (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] : Submodule R M := 𝓜 (Order.pred i)

abbrev predι (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] : pred 𝓜 i →ₗ[R] 𝓜 i :=
 Submodule.inclusion <| mono (Order.pred_le i)

abbrev gradedObject (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :=
  (𝓜 i) ⧸ LinearMap.range (predι 𝓜 i)

def gradedObject.mk (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :=
  Submodule.mkQ (LinearMap.range (predι 𝓜 i))

lemma gradedObject.mk_surjective (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  Function.Surjective (gradedObject.mk 𝓜 i) :=
    Submodule.mkQ_surjective (LinearMap.range (predι 𝓜 i))

def aux_ι_map (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :=
  LinearMap.range (predι 𝓜 i)

lemma BRUH (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type z} [AddCommGroup N]
  [Module R N] (𝓝 : ι → Submodule R N) [FilteredModule 𝓝] {f : M →ₗ[R] N} {i : ι}
  (hf : ∀ x ∈ (𝓜 i), f x ∈ (𝓝 i)) :
  (aux_ι_map 𝓜 i ≤ Submodule.comap (LinearMap.restrict f hf) (aux_ι_map 𝓝 i)) := sorry


def gradedHomOfHom (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type z} [AddCommGroup N]
  [Module R N] (𝓝 : ι → Submodule R N) [FilteredModule 𝓝] (f : M →ₗ[R] N) {i : ι}
  (hf : ∀ x ∈ (𝓜 i), f x ∈ (𝓝 i)) : gradedObject 𝓜 i →ₗ[R] gradedObject 𝓝 i :=
    Submodule.mapQ (LinearMap.range (predι 𝓜 i)) (LinearMap.range (predι 𝓝 i))
      (LinearMap.restrict f hf) (BRUH 𝓜 𝓝 _)

lemma gradedHomOfHom_surjOfSurj (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type z} [AddCommGroup N]
  [Module R N] (𝓝 : ι → Submodule R N) [FilteredModule 𝓝] (f : M →ₗ[R] N) {i : ι}
  (hf : ∀ x ∈ (𝓜 i), f x ∈ (𝓝 i)) (hs : Function.Surjective (LinearMap.restrict f hf)) :
  Function.Surjective (gradedHomOfHom 𝓜 𝓝 f hf) := by
    rintro ⟨b, h⟩
    let a := hs ⟨b, h⟩
    let a := gradedObject.mk 𝓝 i

    sorry

abbrev assocGModule (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] := fun i : ι => gradedObject 𝓜 i

-- -- instance instGModule (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] :
-- --   DirectSum.Gmodule (fun i : PUnit => R) (assocGModule 𝓜) where

-- instance instGradedIsFiltered (𝓜 : ι → Submodule R M) [GradedModule 𝓐] : FilteredAlgebra (ofGraded 𝓐) where
--   whole := by
--     rw [Submodule.eq_top_iff']
--     intro x
--     --let h : ∀ i, 𝓐 i ≤ ofGraded 𝓐 i := fun i => ofGraded.le_incl 𝓐 i i (le_refl i)
--     letI := iSup_mono (fun i => ofGraded.le_incl 𝓐 i i (le_refl i))
--     apply this
--     let h : iSup 𝓐 = ⊤ :=
--       sorry
--     simp only [h, Submodule.mem_top]
--   mono := ofGraded.mono 𝓐


-- Function.Surjective.FilteredAlgebra
instance instPushforwardOfFiltered (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type z}
  [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (h : Function.Surjective f) : FilteredModule <| (Submodule.map f).comp 𝓜 where
    whole := by
      simp only [Function.comp_apply, ← Submodule.map_iSup, whole, Submodule.map_top,
        LinearMap.range_eq_top, h]
    mono _ _ h := Submodule.map_mono <| mono h
    bot := by
      simp only [Function.comp_apply, bot, Submodule.map_bot]
--def ofGraded (𝓜 : ι → Submodule R M) [GradedModule 𝓜]


def betweenGraded (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type z} [AddCommGroup N]
  [Module R N] (𝓝 : ι → Submodule R N) [FilteredModule 𝓝] (f : M →ₗ[R] N)
  (hf : ∀ i, ∀ x ∈ (𝓜 i), f x ∈ (𝓝 i)) [DecidableEq ι] :
  DirectSum ι (assocGModule 𝓜) →ₗ[R] DirectSum ι (assocGModule 𝓝) := by
    letI := fun i : ι =>
      LinearMap.comp (DirectSum.lof R ι (assocGModule 𝓝) i) (gradedHomOfHom 𝓜 𝓝 f (hf i))
    apply DirectSum.toModule R ι
    exact this

lemma betweenGraded_surjOfSurj (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type z}
  [AddCommGroup N] [Module R N] (𝓝 : ι → Submodule R N) [FilteredModule 𝓝] (f : M →ₗ[R] N)
  (hf : ∀ i, ∀ x ∈ (𝓜 i), f x ∈ (𝓝 i)) [DecidableEq ι] :
  Function.Surjective <| betweenGraded 𝓜 𝓝 f hf :=
    sorry



end FilteredModule
