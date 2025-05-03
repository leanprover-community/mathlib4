import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Category.Ring.Topology

/-
  An `Under B` version of `Mathlib.Algebra.Category.Ring.Topology`
-/
namespace CommRingCat.HomTopology
open TensorProduct CategoryTheory Topology
universe u
variable {B : CommRingCat.{u}}
variable {R S T : Under B}

scoped instance [TopologicalSpace S] : TopologicalSpace (R ⟶ S) :=
  .induced (fun f ↦ f.right) inferInstance


@[fun_prop]
nonrec lemma continuous_apply' [TopologicalSpace S] (x : R) :
    Continuous (fun f : R ⟶ S ↦ f.right.hom x) :=
  (continuous_apply x).comp continuous_induced_dom

@[fun_prop]
lemma continuous_precomp' [TopologicalSpace T] (f : R ⟶ S) :
    Continuous ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) :=
  continuous_induced_rng.mpr <| (continuous_precomp f.right).comp continuous_induced_dom

@[simps]
def precompHomeo' [TopologicalSpace T] (f : R ≅ S) :
    (S ⟶ T) ≃ₜ (R ⟶ T) where
  continuous_toFun := continuous_precomp' f.hom
  continuous_invFun := continuous_precomp' f.inv
  left_inv _ := by simp
  right_inv _ := by simp

lemma isHomeomorph_precomp' [TopologicalSpace T] (f : R ⟶ S) [IsIso f] :
    IsHomeomorph ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) :=
  (precompHomeo' (asIso f)).isHomeomorph

variable (R S) in
lemma isEmbedding_hom' [TopologicalSpace S] :
    IsEmbedding (fun f : R ⟶ S => f.right) :=
  ⟨.induced _, fun _ _ e ↦ by ext; rw [e]⟩

lemma isEmbedding_precomp_of_surjective'
    [TopologicalSpace T] (f : R ⟶ S) (hf : Function.Surjective f.right) :
    Topology.IsEmbedding ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) := by
  refine IsEmbedding.of_comp (continuous_precomp' _) (IsInducing.induced _).continuous ?_
  suffices IsEmbedding (fun g : S.right ⟶ T.right ↦ f.right ≫ g) from
    (IsEmbedding.of_comp_iff this).mpr <| isEmbedding_hom' S T
  exact isEmbedding_precomp_of_surjective f.right hf

-- lemma isClosedEmbedding_precomp_of_surjective'
--     [TopologicalSpace T] [T1Space T] (f : R ⟶ S) (hf : Function.Surjective f.right) :
--     Topology.IsClosedEmbedding ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) := by
--   refine ⟨isEmbedding_precomp_of_surjective' f hf, ?_⟩
--   -- have : IsClosed (⋂ i : RingHom.ker f.right, { f : R ⟶ T | f i = 0 }) :=
--   --   isClosed_iInter fun x ↦ (isClosed_singleton (x := 0)).preimage (continuous_apply (S := T) x.1)
--   -- convert this
--   -- #check Mathlib.Tactic.convert
--   -- ext x
--   -- simp only [Set.mem_range, Set.iInf_eq_iInter, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall,
--   --   RingHom.mem_ker]
--   -- constructor
--   -- · rintro ⟨g, rfl⟩ a ha; simp [ha]
--   -- · exact fun H ↦ ⟨CommRingCat.ofHom (RingHom.liftOfSurjective f.hom hf ⟨x.hom, H⟩),
--   --     by ext; simp [RingHom.liftOfRightInverse_comp_apply]⟩
--   sorry

end CommRingCat.HomTopology
