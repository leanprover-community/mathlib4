import Mathlib.Algebra.Module.FilteredModule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

universe u v w u₁

open scoped DirectSum

variable {R : Type u} {A : Type v} {ι : Type w}
[CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]
[Bot ι]

class FilteredAlgebra (𝓐 : ι → Submodule R A) extends FilteredModule 𝓐 where
  mul_compat' : ∀ ⦃i j : ι⦄, 𝓐 i * 𝓐 j ≤ 𝓐 (i + j)
  one' : 1 ∈ 𝓐 0

namespace FilteredAlgebra

lemma r_in_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] (r : R) : algebraMap R A r ∈ (𝓐 0) := by
  simp only [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem (𝓐 0) r one'

lemma mul_compat {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} {a b : A} :
  a ∈ 𝓐 i → b ∈ 𝓐 j → a * b ∈ 𝓐 (i + j) := fun h₁ h₂ =>
    mul_compat' <| Submodule.mul_mem_mul h₁ h₂


def instSubAlgebraZero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Subalgebra R A where
  carrier := 𝓐 0
  mul_mem' a b := by
    let h := mul_compat a b
    simp only [add_zero] at h
    exact h
  add_mem' := Submodule.add_mem (𝓐 0)
  algebraMap_mem' r := (r_in_zero 𝓐 r)


def hlMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] (i j : ι) :
  𝓐 i →ₗ[R] 𝓐 j →ₗ[R] 𝓐 (i + j) where
  toFun x := LinearMap.restrict (LinearMap.domRestrict (LinearMap.mul R A) (𝓐 i) x) <|
    fun _ h => mul_compat x.2 h
  map_add' _ _ := by
    ext _
    simp only [map_add, LinearMap.domRestrict_apply, LinearMap.restrict_coe_apply,
      LinearMap.add_apply, LinearMap.mul_apply', AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
  map_smul' _ _ := by
    ext _
    simp only [LinearMapClass.map_smul, LinearMap.domRestrict_apply, LinearMap.restrict_coe_apply,
      LinearMap.smul_apply, LinearMap.mul_apply', RingHom.id_apply, SetLike.val_smul]


abbrev gradedObject (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  FilteredModule.gradedObject 𝓐 i


def lift  (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i →ₗ[R] gradedObject 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) where
  toFun x :=  by
    let p := LinearMap.range (FilteredModule.predι 𝓐 j)
    let q := LinearMap.range (FilteredModule.predι 𝓐 (i + j))
    let h : p ≤ (Submodule.comap ((hlMul 𝓐 i j) x) q) := by
      intro y h
      simp only [Submodule.mem_comap]
      dsimp [hlMul, LinearMap.mul, LinearMap.restrict, LinearMap.codRestrict]

      sorry
    exact Submodule.mapQ p q ((hlMul 𝓐 i j) x) h
  map_add' _ _ := by
    ext _
    simp only [map_add, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.add_apply, Submodule.Quotient.mk_add]
  map_smul' _ _ := by
    ext _
    simp only [LinearMapClass.map_smul, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, RingHom.id_apply]

    sorry



def gMul (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i →ₗ[R] gradedObject 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := by
    let h : FilteredModule.aux_ι_map 𝓐 i ≤ LinearMap.ker (lift 𝓐 i j) := sorry
    exact Submodule.liftQ (FilteredModule.aux_ι_map 𝓐 i) (lift 𝓐 i j) h


-- --instance instAssocGradedIsAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Algebra R

-- abbrev assocGAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] := fun i : ι => gradedObject 𝓐 i

-- instance instGMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : GradedMonoid.GMul (assocGAlgebra 𝓐) where
--   mul x y := lift 𝓐 _ _ x y

-- instance instGOne (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : GradedMonoid.GOne (assocGAlgebra 𝓐) where
--   one := FilteredModule.gradedObject.mk 𝓐 0 (1 : instSubAlgebraZero 𝓐)

-- @[simp]
-- lemma gMul_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (x : assocGAlgebra 𝓐 i),
--   GradedMonoid.GMul.mul x (0 : assocGAlgebra 𝓐 j) = 0 := fun x =>
--     sorry

-- @[simp]
-- lemma zero_gMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (y : assocGAlgebra 𝓐 j),
--   GradedMonoid.GMul.mul (0 : assocGAlgebra 𝓐 i) y = 0 := fun y => sorry

-- lemma gMul_add (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (x : assocGAlgebra 𝓐 i)
--   (y₁ y₂ : assocGAlgebra 𝓐 j),
--   GradedMonoid.GMul.mul x (y₁ + y₂) = GradedMonoid.GMul.mul x y₁ + GradedMonoid.GMul.mul x y₂ := sorry

-- lemma add_gMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (x₁ x₂ : assocGAlgebra 𝓐 i)
--   (y : assocGAlgebra 𝓐 j),
--   GradedMonoid.GMul.mul (x₁ + x₂) y = GradedMonoid.GMul.mul x₁ y + GradedMonoid.GMul.mul x₂ y := sorry

-- lemma one_gMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   ∀ (x : GradedMonoid (assocGAlgebra 𝓐)), 1 * x = x := fun x =>
--     sorry

-- lemma gMul_one (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   ∀ (x : GradedMonoid (assocGAlgebra 𝓐)), x * 1 = x := fun x =>
--     sorry

-- lemma mul_assoc (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   ∀ (x y z : GradedMonoid (assocGAlgebra 𝓐)), x * y * z = x * (y * z) := fun x y z =>
--     sorry


-- def natCast (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ℕ → assocGAlgebra 𝓐 0 :=
--   fun n => FilteredModule.gradedObject.mk 𝓐 0 (n : instSubAlgebraZero 𝓐)

-- lemma natCast_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : natCast 𝓐 0 = 0 := by
--   dsimp [natCast]
--   simp only [Nat.cast_zero, map_zero]

-- lemma natCast_succ (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   ∀ n, natCast 𝓐 (n + 1) = natCast 𝓐 n + GradedMonoid.GOne.one := fun n => by
--   dsimp [natCast, GradedMonoid.GOne.one]
--   simp only [Nat.cast_add, Nat.cast_one, map_add]

-- def intCast (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ℤ → assocGAlgebra 𝓐 0 :=
--   fun n => FilteredModule.gradedObject.mk 𝓐 0 (n : instSubAlgebraZero 𝓐)

-- lemma intCast_ofNat (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   ∀ (n : ℕ), intCast 𝓐 n = natCast 𝓐 n := fun n => by
--   dsimp [intCast, natCast]
--   simp only [Int.cast_natCast]

-- lemma intCast_negSucc_ofNat (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   ∀ (n : ℕ), intCast 𝓐 (Int.negSucc n) = -natCast 𝓐 (n + 1) := fun n => by
--   dsimp [intCast, natCast]
--   simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, map_add, map_neg]

-- instance instGRing (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   DirectSum.GRing (assocGAlgebra 𝓐) where
--     mul_zero := gMul_zero 𝓐
--     zero_mul := zero_gMul 𝓐
--     mul_add := gMul_add 𝓐
--     add_mul := add_gMul 𝓐
--     one_mul := one_gMul 𝓐
--     mul_one := gMul_one 𝓐
--     mul_assoc := mul_assoc 𝓐
--     natCast := natCast 𝓐
--     natCast_zero := natCast_zero 𝓐
--     natCast_succ := natCast_succ 𝓐
--     intCast := intCast 𝓐
--     intCast_ofNat := intCast_ofNat 𝓐
--     intCast_negSucc_ofNat := intCast_negSucc_ofNat 𝓐

-- def toFun (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : R →+ assocGAlgebra 𝓐 0 :=
--   (FilteredModule.gradedObject.mk 𝓐 0).toAddMonoidHom.comp
--     (algebraMap R (instSubAlgebraZero 𝓐)).toAddMonoidHom

-- -- instance instGRing (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
-- --   DirectSum.GRing (assocGAlgebra 𝓐) where
-- --   instCast := sorry

-- instance instGAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
--   DirectSum.GAlgebra R (assocGAlgebra 𝓐) where
--     toFun := toFun 𝓐
--     map_one := by
--       dsimp [toFun, GradedMonoid.GOne.one]
--       erw [RingHom.map_one (algebraMap R (instSubAlgebraZero 𝓐))]
--     map_mul r s :=

--       sorry
--     commutes := sorry
--     smul_def :=
--       sorry


-- abbrev ofGraded (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : ι → Submodule R A := fun i =>
--   ⨆ j : {j : ι | j ≤ i }, 𝓐 j


-- lemma ofGraded.le_incl (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] :
--   ∀ i j, i ≤ j → 𝓐 i ≤ ofGraded 𝓐 j := fun i j h => by
--     letI := le_iSup (fun t : {i : ι | i ≤ j } => 𝓐 t)
--     simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall] at this
--     exact this i h


-- lemma ofGraded.mono (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : Monotone (ofGraded 𝓐) := by
--   intro i j h
--   simp only [iSup_le_iff, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall]
--   intro k h'
--   exact ofGraded.le_incl 𝓐 k j (h'.trans h)


-- -- As written this is not true
-- instance instGradedIsFiltered (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : FilteredAlgebra (ofGraded 𝓐) where
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
--   one' := by
--     letI := ofGraded.le_incl 𝓐 0 0 (le_refl 0)
--     apply this
--     sorry
--   mul_compat' i j := by
--     sorry

-- -- Function.Surjective.FilteredAlgebra

-- -- lemma hone (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁} [Ring B] [Algebra R B]
-- --   (𝓑 : ι → Submodule R B) [FilteredAlgebra 𝓑] (f : A →ₐ[R] B) : ( 0) GradedMonoid.GOne.one = 1

-- -- lemma hmul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁} [Ring B] [Algebra R B]
-- --   (𝓑 : ι → Submodule R B) [FilteredAlgebra 𝓑] (f : A →ₐ[R] B) :
-- --   ∀ {i j : ι} (ai : 𝓐 i) (aj : 𝓐 j), (f (i + j)) (GradedMonoid.GMul.mul ai aj) = (f i) ai * (f j) aj)

-- def betweenGraded (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁} [Ring B] [Algebra R B]
--   (𝓑 : ι → Submodule R B) [FilteredAlgebra 𝓑] (f : A →ₐ[R] B)
--   (hf : ∀ i : ι, ∀ x ∈ (𝓐 i), f x ∈ (𝓑 i)) :
--   DirectSum ι (assocGAlgebra 𝓐) →ₐ[R] DirectSum ι (assocGAlgebra 𝓑) := by
--     let φ := fun i =>
--       (FilteredModule.betweenGraded 𝓐 𝓑 f hf).comp (DirectSum.lof R ι (assocGAlgebra 𝓐) i)
--     apply DirectSum.toAlgebra R (assocGAlgebra 𝓐) φ
--     · dsimp [GradedMonoid.GOne.one]
--       dsimp [φ]
--       dsimp [FilteredModule.betweenGraded]
--       simp only [DirectSum.toModule_lof, LinearMap.coe_comp, Function.comp_apply]

--       sorry
--     ·
--       sorry

-- -- use the module part
-- lemma betweenGraded_surjOfSurj (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁} [Ring B]
--   [Algebra R B] (𝓑 : ι → Submodule R B) [FilteredAlgebra 𝓑] (f : A →ₐ[R] B)
--   (hf : ∀ i : ι, ∀ x ∈ (𝓐 i), f x ∈ (𝓑 i)) : Function.Surjective <| betweenGraded 𝓐 𝓑 f hf :=
--   sorry



-- instance instPushforwardOfFiltered (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁} [Ring B] [Algebra R B]
--   (f : A →ₐ[R] B) (h : Function.Surjective f) : FilteredAlgebra <| (Submodule.map f.toLinearMap).comp 𝓐 where
--     whole := by
--       simp only [Function.comp_apply, ← Submodule.map_iSup, FilteredModule.whole, Submodule.map_top,
--         LinearMap.range_eq_top]
--       intro X
--       exact h X
--     mono _ _ h := Submodule.map_mono <| FilteredModule.mono h
--     one' := by
--       simp only [Function.comp_apply, Submodule.mem_map]
--       exact ⟨1, one', map_one f⟩
--     mul_compat' _ _ := by
--       simp only [Function.comp_apply, ← Submodule.map_mul]
--       apply Submodule.map_mono
--       simp only [FilteredAlgebra.mul_compat']

-- lemma pushforwardOfFiltered_respects (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁}
--   [Ring B] [Algebra R B] (f : A →ₐ[R] B) :
--   ∀ i : ι, ∀ x ∈ (𝓐 i), f x ∈ ((Submodule.map f.toLinearMap).comp 𝓐 i) := fun i x h => by
--     simp only [Function.comp_apply, Submodule.mem_map, AlgHom.toLinearMap_apply]
--     use x

-- lemma pushforwardOfFiltered_respects' (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁}
--   [Ring B] [Algebra R B] (f : A →ₐ[R] B) :
--   ∀ i : ι, ∀ x ∈ (𝓐 i), f x ∈ ((Submodule.map f.toLinearMap).comp 𝓐 i) := fun i x h => by
--     simp only [Function.comp_apply, Submodule.mem_map, AlgHom.toLinearMap_apply]
--     use x

-- -- def objectHom {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {B : Type w} [Ring B] [Algebra R B]
-- --   {𝓑 : ι → Submodule R B} [FilteredAlgebra 𝓑] {f : A →ₐ[R] B} {i : ι}
-- --   (h : Submodule.map f.toLinearMap (𝓐 i) ≤ 𝓑 i) :
-- --   gradedObject 𝓐 i →ₗ[R] gradedObject 𝓑 i where
-- --   toFun := by
-- --     letI := FilteredModule.gradedObject.mk 𝓑 i
-- --     --letI := LinearMap.restrict f h
-- --     sorry
-- --   map_add' := sorry
-- --   map_smul' := sorry


-- -- def toGHom (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type w} [Ring B] [Algebra R B]
-- --   (𝓑 : ι → Submodule R B) [FilteredAlgebra 𝓑] (f : A →ₐ[R] B) :
-- --   (⨁ i, assocGAlgebra 𝓐 i) →ₐ[R] (⨁ i, assocGAlgebra 𝓑 i) where
-- --   toFun := sorry
-- --   map_one' := sorry
-- --   map_add' := sorry
-- --   map_mul' := sorry
-- --   map_zero' := sorry
-- --   commutes' := sorry



-- end FilteredAlgebra
