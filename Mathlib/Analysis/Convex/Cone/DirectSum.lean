import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Algebra.Order.Nonneg.Ring


namespace ConvexCone.Pointed

variable [OrderedSemiring 𝕜] [Nontrivial 𝕜] [AddCommMonoid E] [Module 𝕜 E]

instance : Module { c : 𝕜 // 0 ≤ c } E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

variable {S : ConvexCone 𝕜 E} [hS : Fact S.Pointed]

@[simp]
theorem mem_zero : (0 ∈ S) := hS.elim

instance : Zero S where
  zero := ⟨0, by simp⟩

instance hasNonnegSmul : SMul { c : 𝕜 // 0 ≤ c } S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => by
    use c • x
    cases' eq_or_lt_of_le hc with hzero hpos
    . simp_rw [← hzero, zero_smul, mem_zero]
    . exact S.smul_mem hpos hx

instance hasNsmul : SMul ℕ S where
  smul := fun n x => (n : { c : 𝕜 // 0 ≤ c }) • x


@[simp]
theorem coe_smul (x : S) (n : { c : 𝕜 // 0 ≤ c }) : n • x = n • (x : E) := rfl

@[simp]
theorem coe_nsmul' (x : S) (n : ℕ) : n • x = (n : { c : 𝕜 // 0 ≤ c }) • x := rfl

@[simp]
theorem coe_nsmul'' (x : S) (n : ℕ) : n • (x : E) = (n : { c : 𝕜 // 0 ≤ c }) • (x : E) := by sorry

@[simp]
theorem coe_nsmul (x : S) (n : ℕ) : n • x = n • (x : E) := by simp

instance : AddCommMonoid S :=
  Function.Injective.addCommMonoid (Subtype.val : S → E) Subtype.coe_injective
    rfl
    (by aesop)
    (coe_nsmul)

def subtype : S →+ E where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' := by aesop

@[simp]
theorem coeSubtype : (subtype : S → E) = Subtype.val := rfl

instance : Module { c : 𝕜 // 0 ≤ c } S := by
  apply Function.Injective.module ({ c : 𝕜 // 0 ≤ c }) subtype
  simp[Subtype.coe_injective]
  simp


end ConvexCone.Pointed


-- def ConvexCone.DirectSum (h : ∀ i, Pointed (S i)) : ConvexCone 𝕜 (⨁ i, E i) where
--   carrier := by
--     let f i : S i → E i := fun x => x.1
--     haveI (i : ι) : Zero (S i) := by infer_instance --⟨⟨0, h i⟩⟩
--     -- have hf i : f i 0 = 0 := by
--     --   simp only
--     --   sorry
--     refine' Set.range <| DFinsupp.mapRange f _

--   smul_mem' := by
--     haveI (i : ι) : Zero (S i) := ⟨⟨0, h i⟩⟩
--     rintro c hc a ⟨x, hx⟩
--     simp at *
--     dsimp [DFinsupp.mapRange] at *
--     -- have := DirectSum.mk E x.support'
--     sorry
--     -- use c • x
--   add_mem' := sorry

-- end DirectSum



    /-
    unsolved goals

    case npow
    𝕜: Type ?u.7833
    E: Type ?u.7836
    inst✝²: OrderedSemiring 𝕜
    inst✝¹: AddCommMonoid E
    inst✝: Module 𝕜 E
    S : ConvexCone 𝕜 E
    hS: Fact (ConvexCone.Pointed S)
    ⊢ ∀ (x : { x // x ∈ S }) (n : ℕ), ↑(n • x) = n • ↑x
    -/
    -- . extract_goals

    -- sorry
    -- (by aesop)
    -- (by aesop)
    -- (by rintro ⟨x, hx⟩ n
    --     sorry
    -- )


-- import Mathlib.Analysis.Convex.Cone.Basic
-- import Mathlib.Algebra.Order.Nonneg.Ring

-- variable [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

-- variable {S : ConvexCone 𝕜 E} (hS : S.Pointed)

-- instance Pointed.toAddCommMonoid : AddCommMonoid S := by
--   letI hzero : Zero S := ⟨⟨0, hS⟩⟩
--   letI hsmul : SMul ℕ S := ⟨fun n => match n with
--     -- induction' n with n hn
--     | 0 => fun x => ⟨0, by simpa [ConvexCone.Pointed] using hS⟩
--     | n + 1 => fun x => by {
--         apply Subtype.mk
--         exact S.smul_mem (show 0 < (n + 1 : 𝕜) from sorry) x.2 } ⟩
--   apply Function.Injective.addCommMonoid (Subtype.val : S → E) Subtype.coe_injective
--   . rfl
--   . simp [AddMemClass.coe_add]
--   . exact fun x n => match n with
--     | 0 => by simp only [zero_smul] ; rfl
--     | n + 1 => sorry


-- -- failed to synthesize instance
-- -- AddCommMonoid { x // x ∈ S }
-- instance : Module { c : 𝕜 // 0 ≤ c } S := sorry


-- import Mathlib.Algebra.DirectSum.Module
  -- haveI : Module { c : 𝕜 // 0 ≤ c } E := by
  -- apply Function.Injective.module


--   smul := by aesop
--   one_smul := fun ⟨a, ha⟩ => sorry
--   mul_smul := by aesop
--   smul_zero :=
--   smul_add := _
--   add_smul := _
--   zero_smul := _

-- instance : AddCommMonoid S where
--   add := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, S.add_mem' hx hy⟩
--   add_assoc := by simp [add_assoc]
--   zero := ⟨0, by simpa [ConvexCone.Pointed] using hS ⟩
--   zero_add := fun ⟨a, ha⟩ => by

--   add_zero := fun ⟨a, ha⟩ => sorry
--   nsmul := fun n => by
--     induction' n with n hn
--     . exact (fun _ => ⟨0, by simpa [ConvexCone.Pointed] using hS ⟩)
--     . exact (fun x => x + hn x)
--   nsmul_zero := by aesop
--   nsmul_succ := by aesop
--   add_comm := by simp [add_comm]





-- section DirectSum
-- variable {ι : Type _} [dec_ι : DecidableEq ι]

-- open DirectSum

-- variable {E : ι → Type u} [∀ i, AddCommMonoid (E i)] [∀ i, Module 𝕜 (E i)]

-- variable {S : ∀ i, ConvexCone 𝕜 (E i)}


-- def ConvexCone.DirectSum (h : ∀ i, Pointed (S i)) : ConvexCone 𝕜 (⨁ i, E i) where
--   carrier := by
--     let f i : S i → E i := fun x => x.1
--     haveI (i : ι) : Zero (S i) := by infer_instance --⟨⟨0, h i⟩⟩
--     -- have hf i : f i 0 = 0 := by
--     --   simp only
--     --   sorry
--     refine' Set.range <| DFinsupp.mapRange f _

--   smul_mem' := by
--     haveI (i : ι) : Zero (S i) := ⟨⟨0, h i⟩⟩
--     rintro c hc a ⟨x, hx⟩
--     simp at *
--     dsimp [DFinsupp.mapRange] at *
--     -- have := DirectSum.mk E x.support'
--     sorry
--     -- use c • x
--   add_mem' := sorry

-- end DirectSum
