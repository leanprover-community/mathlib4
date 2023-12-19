import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

open CategoryTheory Limits Simplicial SimplexCategory

variable (X Y : SSet)

namespace CategoryTheory

def isTerminalHom {C : Type _} [Category C] (X Y : C) (hY : IsTerminal Y) :
    IsTerminal (X ⟶ Y) :=
  letI : ∀ (W : Type _), Unique (W ⟶ (X ⟶ Y)) := fun W =>
    { default := fun _ => hY.from _
      uniq := fun a => by ext ; apply hY.hom_ext }
  IsTerminal.ofUnique _

def Functor.isTerminalOfObjIsTerminal {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) (hF : ∀ X : C, IsTerminal (F.obj X)) :
    IsTerminal F :=
  letI : ∀ (G : C ⥤ D), Unique (G ⟶ F) := fun _ => {
    default := {
      app := fun _ => (hF _).from _
      naturality := fun _ _ _ => (hF _).hom_ext _ _ }
    uniq := fun _ => NatTrans.ext _ _ <| funext fun _ => (hF _).hom_ext _ _ }
  IsTerminal.ofUnique _

end CategoryTheory

namespace SimplexCategory

def isTerminalZero : IsTerminal ([0] : SimplexCategory) :=
  letI : ∀ t : SimplexCategory, Unique (t ⟶ [0]) := fun t => {
    default := SimplexCategory.Hom.mk <| OrderHom.const _ 0
    uniq := fun m => SimplexCategory.Hom.ext _ _ <| OrderHom.ext _ _ <|
      funext fun _ => Fin.ext <| by simp }
  IsTerminal.ofUnique _

end SimplexCategory

namespace SSet

universe u

def ptIsTerminal : IsTerminal Δ[0] := Functor.isTerminalOfObjIsTerminal _ <|
  fun t => show IsTerminal (t.unop ⟶ [0]) from isTerminalHom _ _ isTerminalZero

def binaryFan (X : SSet.{0}) : BinaryFan Δ[0] X :=
  BinaryFan.mk (ptIsTerminal.from X) (𝟙 X)

def isLimitBinaryFan (X : SSet.{0}) : IsLimit (binaryFan X) where
  lift := fun (S : BinaryFan _ _) => S.snd
  fac := fun (S : BinaryFan _ _) => by
    rintro ⟨(_|_)⟩
    · apply ptIsTerminal.hom_ext
    · dsimp [binaryFan] ; simp
  uniq := fun (S : BinaryFan _ _) m hm => by
    specialize hm ⟨WalkingPair.right⟩
    simpa [binaryFan] using hm

noncomputable
def leftUnitor (X : SSet.{0}) : Δ[0] ⨯ X ≅ X :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitBinaryFan X)

class IsKan (X : SSet) : Prop where
  cond : ∀ n i (f : Λ[n,i] ⟶ X), ∃ (g : Δ[n] ⟶ X), f = hornInclusion _ _ ≫ g

def d0 : Δ[0] ⟶ Δ[1] := standardSimplex.map (δ 0)
def d1 : Δ[0] ⟶ Δ[1] := standardSimplex.map (δ 1)

def D0 : Δ[1] ⟶ Δ[2] := standardSimplex.map (δ 0)
def D1 : Δ[1] ⟶ Δ[2] := standardSimplex.map (δ 1)
def D2 : Δ[1] ⟶ Δ[2] := standardSimplex.map (δ 2)

lemma D1_comp_d1 : d1 ≫ D1 = d1 ≫ D2 := by
  have := @δ_comp_δ_self 0 1
  apply_fun (fun a => standardSimplex.map a) at this
  assumption

lemma D1_comp_d0 : d0 ≫ D1 = d0 ≫ D0 := rfl

lemma D2_comp_d0 : d0 ≫ D2 = d1 ≫ D0 := by
  have := @δ_comp_δ 0 0 1 (Nat.zero_le 1)
  apply_fun (fun a => standardSimplex.map a) at this
  assumption

--map n simplex into n+1 boundary through j-th d map
def intoBoundary (n : ℕ) (j : Fin (n + 2)) : Δ[n] ⟶ ∂Δ[n + 1] where
  app k x := ⟨(standardSimplex.map (δ j)).app k x, fun h => by
    simpa using (show j ∈ Set.range (Fin.succAbove j) from Set.range_comp_subset_range _ _ (h j))⟩

--map n simplex into n+1 horn through j-th d map
--better way to say j ≠ i, maybe j ∈ {i}ᶜ
def intoHorn (n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i) : Δ[n] ⟶ Λ[n + 1, i] where
  app k x := ⟨(standardSimplex.map (δ j)).app k x, by
    rw [Set.ne_univ_iff_exists_not_mem]
    use j
    intro h
    cases h with
     | inl h =>
      simpa using (show j ∈ Set.range (Fin.succAbove j) from Set.range_comp_subset_range _ _ h)
     | inr h => exact hj h⟩

lemma factor_through_horn {n : ℕ} {i j : Fin (n + 2)} {hj : j ≠ i} (g : Δ[n+1] ⟶ X) :
  standardSimplex.map (δ j) ≫ g = (intoHorn n i j hj) ≫ hornInclusion _ _ ≫ g := rfl

--relevant d maps as factored through horns
def hornD0 : Δ[1] ⟶ Λ[2, 1] := intoHorn 1 1 0 zero_ne_one

def hornD2 : Δ[1] ⟶ Λ[2, 1] := intoHorn 1 1 2 (by simp)

def HornD0 : Δ[1] ⟶ Λ[2, 2] := intoHorn 1 2 0 (by simp)

def HornD1 : Δ[1] ⟶ Λ[2, 2] := intoHorn 1 2 1 (by simp)

@[simp]
lemma hornD2_comp_d0 : d0 ≫ hornD2 = d1 ≫ hornD0 := by
  have := D2_comp_d0
  ext k x
  apply_fun (fun a => a.app k x) at this
  change (hornD2).app k (d0.app k x) = (hornD0).app k (d1.app k x)
  dsimp [hornD0, hornD2, intoHorn]
  congr

structure Path {X : SSet.{0}} (a b : Δ[0] ⟶ X) where
  p : Δ[1] ⟶ X
  hp0 : d0 ≫ p = a
  hp1 : d1 ≫ p = b

def Path.rfl {X : SSet.{0}} (a : Δ[0] ⟶ X) : Path a a where
  p := ptIsTerminal.from _ ≫ a
  hp0 := by slice_lhs 1 2 => simp
  hp1 := by slice_lhs 1 2 => simp

lemma rangeδ (n : ℕ) (i : Fin (n + 2)) : Set.range (δ i) = {i}ᶜ := Fin.range_succAbove i

--- given 0 ≤ i ≤ n+1, and x : k → n+1 which does not have i in the image, want y : k → n by forgetting the i
def predAbove (n : ℕ) (i : Fin (n + 2)) (k : SimplexCategoryᵒᵖ) (x : Δ[n+1].obj k) : Fin (len k.unop + 1) →o Fin (n+1) where
  toFun := (Fin.predAbove i) ∘ (asOrderHom x)
  monotone' := Monotone.comp (Fin.predAbove_right_monotone _) (asOrderHom x).monotone

--not right, dont want to need hi. so can use this for range of d0, d1, but not d2 :(
lemma range_d (n : ℕ) (i : Fin (n + 2)) (hi : i.val < n + 1) (k : SimplexCategoryᵒᵖ) (x : (Δ[n+1]).obj k) :
  x ∈ Set.range ((standardSimplex.map (δ i)).app k) ↔ Set.range (asOrderHom x) ⊆ {i}ᶜ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      refine subset_trans ?_ (subset_of_eq (Fin.range_succAbove i))
      intro j hj
      apply Set.range_comp_subset_range _ _
      simpa only [Set.mem_range, Function.comp_apply]
    · intro h
      refine ⟨Hom.mk (predAbove n i k x), ?_⟩
      dsimp [predAbove, standardSimplex, δ]
      ext l
      have gg : (Fin.castSucc (i : Fin (n+1))) = i := by
        ext
        rw [← Fin.coe_castSucc i]
        simp only [Fin.coe_castSucc, Fin.coe_ofNat_eq_mod, Nat.mod_succ_eq_iff_lt]
        exact hi
      have goal : (asOrderHom x) l ≠ Fin.castSucc i := by
        rw [gg]
        apply h
        simp only [Set.mem_range, exists_apply_eq_apply]
      have := Fin.succAbove_predAbove goal
      simp at this ⊢
      rw [gg] at this
      rw [this]
      rfl

-- if (x : Δ[2].obj k) does not have 0 in its image as an order hom, (i.e. (asOrderHom x) ⊆ {0}ᶜ) then we can
-- consider it as an element y of (Δ[1].obj k) which maps to x via d0
-- i.e. get Fin (len k.unop + 1) → Fin (2), from Fin (len k.unop + 1) →o Fin (2 + 1), since 0 not in the image
/-
def predAbove0 (k : SimplexCategoryᵒᵖ) (x : Δ[2].obj k) : Fin (len k.unop + 1) →o Fin 2 where
  toFun := (Fin.predAbove (0 : Fin 2)) ∘ (asOrderHom x)
  monotone' := Monotone.comp (Fin.predAbove_right_monotone _) (asOrderHom x).monotone

lemma range_d0 (k : SimplexCategoryᵒᵖ) (x : Δ[2].obj k) :
  x ∈ Set.range ((standardSimplex.map (δ 0)).app k) ↔ Set.range (asOrderHom x) ⊆ {0}ᶜ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      refine subset_trans ?_ (subset_of_eq (Fin.range_succAbove 0))
      intro j hj
      apply Set.range_comp_subset_range _ _
      simpa only [Set.mem_range, Function.comp_apply]
    · intro h
      refine ⟨Hom.mk (predAbove0 k x), ?_⟩
      dsimp [predAbove0, standardSimplex, δ]
      ext l
      have goal : (asOrderHom x) l ≠ Fin.castSucc 0 := by
        apply h
        simp only [Set.mem_range, exists_apply_eq_apply]
      have := Fin.succAbove_predAbove goal
      simp only [Fin.castSucc_zero, ne_eq, Fin.zero_succAbove, len_mk, Hom.toOrderHom_mk,
        OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, OrderHom.coe_mk, Function.comp_apply,
        Fin.succAboveEmb_apply] at this ⊢
      rw [this]
      rfl
-/

lemma range_d0 (k : SimplexCategoryᵒᵖ) (x : Δ[2].obj k) :
  x ∈ Set.range ((standardSimplex.map (δ 0)).app k) ↔ Set.range (asOrderHom x) ⊆ {0}ᶜ := range_d 1 0 (by simp) k x

lemma range_d1 (k : SimplexCategoryᵒᵖ) (x : Δ[2].obj k) :
  x ∈ Set.range ((standardSimplex.map (δ 1)).app k) ↔ Set.range (asOrderHom x) ⊆ {1}ᶜ := range_d 1 1 (by simp) k x

def castPred2 (k : SimplexCategoryᵒᵖ) (x : Δ[2].obj k) : Fin (len k.unop + 1) →o Fin 2 where
  toFun := (Fin.castPred) ∘ (asOrderHom x)
  monotone' := Monotone.comp (Fin.castPred_monotone) (asOrderHom x).monotone

lemma range_d2 (k : SimplexCategoryᵒᵖ) (x : Δ[2].obj k) :
  x ∈ Set.range ((standardSimplex.map (δ 2)).app k) ↔ Set.range (asOrderHom x) ⊆ {2}ᶜ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      refine subset_trans ?_ (subset_of_eq (Fin.range_succAbove 2))
      intro j hj
      apply Set.range_comp_subset_range _ _
      simpa only [Set.mem_range, Function.comp_apply]
    · intro h
      refine ⟨Hom.mk (castPred2 k x), ?_⟩
      dsimp [castPred2, standardSimplex, δ]
      ext l
      simp
      have a : Fin 3 := (asOrderHom x) l
      have : (asOrderHom x) l = 0 ∨ (asOrderHom x) l = 1 := by --this should be easy
        have := h (Set.mem_range_self l)
        --fin_cases a
        --left ; rfl
        --right ; rfl
        sorry
      cases this with
      | inl h =>
        rw [h]
        simp only [Fin.castPred_zero, ne_eq, Fin.succAbove_ne_zero_zero]
        rw [← h]
        rfl
      | inr h =>
        rw [h]
        simp only [Fin.castPred_one]
        change _ = ((asOrderHom x) l : ℕ)
        rw [h]
        rfl

-- these next two proofs can definitely be golfed, and should be modified

-- an element of the horn Λ[2,1] is in the image of d0 or the image of d2
lemma partition1 (k : SimplexCategoryᵒᵖ) (x : Λ[2, 1].obj k) :
  (x ∈ Set.range ((hornD0).app k)) ∨ (x ∈ Set.range ((hornD2).app k)) := by
  obtain ⟨x ,hx⟩ := x
  rw [Set.ne_univ_iff_exists_not_mem] at hx
  obtain ⟨a, ha⟩ := hx
  rw [Set.mem_union, not_or] at ha
  fin_cases a
  · have : Set.range (asOrderHom x) ⊆ {0}ᶜ := by
      rw [Set.subset_compl_comm, Set.singleton_subset_iff]
      exact ha.1
    left
    rw [← range_d0] at this
    refine ⟨Exists.choose this, by
    dsimp [hornD0, intoHorn]
    congr
    exact Exists.choose_spec this⟩
  · exfalso ; exact ha.2 rfl
  · have : Set.range (asOrderHom x) ⊆ {2}ᶜ := by
      rw [Set.subset_compl_comm, Set.singleton_subset_iff]
      exact ha.1
    right
    rw [← range_d2] at this
    refine ⟨Exists.choose this, by
    dsimp [hornD2, intoHorn]
    congr
    exact Exists.choose_spec this⟩

-- an element of the horn Λ[2,2] is in the image of d0 or the image of d1
lemma partition2 (k : SimplexCategoryᵒᵖ) (x : Λ[2, 2].obj k) :
  (x ∈ Set.range ((HornD0).app k)) ∨ (x ∈ Set.range ((HornD1).app k)) := by
  obtain ⟨x ,hx⟩ := x
  rw [Set.ne_univ_iff_exists_not_mem] at hx
  obtain ⟨a, ha⟩ := hx
  rw [Set.mem_union, not_or] at ha
  fin_cases a
  · have : Set.range (asOrderHom x) ⊆ {0}ᶜ := by
      rw [Set.subset_compl_comm, Set.singleton_subset_iff]
      exact ha.1
    left
    rw [← range_d0] at this
    refine ⟨Exists.choose this, by
    dsimp [HornD0, intoHorn]
    congr
    exact Exists.choose_spec this⟩
  · have : Set.range (asOrderHom x) ⊆ {1}ᶜ := by
      rw [Set.subset_compl_comm, Set.singleton_subset_iff]
      exact ha.1
    right
    rw [← range_d1] at this
    refine ⟨Exists.choose this, by
    dsimp [HornD1, intoHorn]
    congr
    exact Exists.choose_spec this⟩
  · exfalso ; exact ha.2 rfl

def HornEmb1 : (Λ[2, 1] ⟶ X) → (Δ[1] ⟶ X) × (Δ[1] ⟶ X) := fun f => ⟨hornD0 ≫ f, hornD2 ≫ f⟩

def HornEmb2 : (Λ[2, 2] ⟶ X) → (Δ[1] ⟶ X) × (Δ[1] ⟶ X) := fun f => ⟨HornD0 ≫ f, HornD1 ≫ f⟩

lemma HornEmb1Inj : Function.Injective (HornEmb1 X) := fun f g h => by
  ext k x
  rcases partition1 k x with ⟨y,hy⟩ | ⟨y,hy⟩
  · apply_fun (fun a => (a.1).app k y) at h ; rwa [← hy]
  · apply_fun (fun a => (a.2).app k y) at h ; rwa [← hy]

lemma HornEmb2Inj : Function.Injective (HornEmb2 X) := fun f g h => by
  ext k x
  rcases partition2 k x with ⟨y,hy⟩ | ⟨y,hy⟩
  · apply_fun (fun a => (a.1).app k y) at h ; rwa [← hy]
  · apply_fun (fun a => (a.2).app k y) at h ; rwa [← hy]

--alternate
def HornEmb1' : (Λ[2, 1] ⟶ X) → {z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X) // d1 ≫ z.1 = d0 ≫ z.2 } :=
  fun f => ⟨⟨hornD0 ≫ f, hornD2 ≫ f⟩, by slice_rhs 1 2 => rw [hornD2_comp_d0]⟩

-- would like to use rcases partition1 k x, but cant. becomes a problem in l2 and r1, r2
noncomputable
def HornEmb1Inv' : {z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X) // d1 ≫ z.1 = d0 ≫ z.2 } → (Λ[2, 1] ⟶ X) := fun z => {
  app := by
    rintro k x
    by_cases x ∈ Set.range (hornD0.app k)
    · exact z.val.1.app k (Exists.choose h)
    · exact z.val.2.app k (Exists.choose (Or.resolve_left (partition1 k x) h))
  naturality := sorry -- seems annoying
}

-- these need to be tidied
@[simp]
lemma l1 {k : SimplexCategoryᵒᵖ} {x : Λ[2,1].obj k} {h : x ∈ Set.range (hornD0.app k)} {z} :
  (HornEmb1Inv' X z).app k x = z.val.1.app k (Exists.choose h) := by
    dsimp [HornEmb1Inv']
    aesop

@[simp]
lemma l2 {k : SimplexCategoryᵒᵖ} {x : Λ[2,1].obj k} {h : x ∈ Set.range (hornD2.app k)} {z} :
  (HornEmb1Inv' X z).app k x = z.val.2.app k (Exists.choose h) := by
    dsimp [HornEmb1Inv']
    have : x ∉ Set.range (hornD0.app k) := sorry -- immediate if i redo partition1
    aesop

-- not sure about this, think also requires redo of partition
@[simp]
lemma r1 (z) : (hornD0 ≫ (HornEmb1Inv' X z)) = z.val.1 := by
  ext k x
  change (HornEmb1Inv' X z).app k (hornD0.app k x) = _
  have : (hornD0.app k x) ∈ Set.range (hornD0.app k) := Set.mem_range_self x
  have b := Exists.choose_spec this
  rw [← b]
  dsimp [HornEmb1Inv']
  simp
  suffices : Exists.choose this = x ; rw [this]
  aesop
  sorry

@[simp]
lemma r2 (z) : (hornD2 ≫ (HornEmb1Inv' X z)) = z.val.2 := sorry

noncomputable
def HornEmb1Equiv {X : SSet.{0}}: (Λ[2, 1] ⟶ X) ≃ {z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X) // d1 ≫ z.1 = d0 ≫ z.2 } where
  toFun := HornEmb1' X
  invFun := HornEmb1Inv' X
  left_inv f := by
    ext k x
    rcases partition1 k x with h | h
    · rw [l1] ; slice_rhs 1 2 => rw [← Exists.choose_spec h]; rfl
    · rw [l2] ; slice_rhs 1 2 => rw [← Exists.choose_spec h]; rfl
  right_inv z := by simp only [HornEmb1', r1, r2]

/-
noncomputable
def HornEmb1Inv {X : SSet.{0}} (z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X)) : Λ[2,1] ⟶ X := {
      app := by
        rintro k x
        by_cases x ∈ Set.range (hornD0.app k)
        · exact z.1.app k (Exists.choose h)
        · exact z.2.app k (Exists.choose (Or.resolve_left (partition1 k x) h))
      naturality := by -- seems awful
        rintro k m α
        ext x
        cases (partition1 k x) with
        | inl h => sorry
        | inr h => sorry
    }

lemma ofInv {X : SSet.{0}} (z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X)) (hz : d1 ≫ z.1 = d0 ≫ z.2) :
  HornEmb1 X (HornEmb1Inv z) = z := by sorry

lemma HornEmb1Range : Set.range (HornEmb1 X) = {z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X) // d1 ≫ z.1 = d0 ≫ z.2 } := by
  rw [Set.coe_eq_subtype]
  congr
  ext z
  refine ⟨?_, fun hz => ⟨HornEmb1Inv z, ofInv z hz⟩⟩
  · rintro ⟨x,hz⟩
    have h1 : hornD0 ≫ x = z.1 := by
      apply_fun (fun a => a.1) at hz
      exact hz
    have h2 : hornD2 ≫ x = z.2 := by
      apply_fun (fun a => a.2) at hz
      exact hz
    rw [← h1, ← h2]
    have := hornD2_comp_d0.symm
    apply_fun (fun a => a ≫ x) at this
    assumption

noncomputable
def HornEmb1Equiv {X : SSet.{0}}: (Λ[2, 1] ⟶ X) ≃ {z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X) // d1 ≫ z.1 = d0 ≫ z.2 } := by
  rw [← HornEmb1Range]
  exact Equiv.ofInjective _ (HornEmb1Inj X)
-/

lemma need0 {X : SSet.{0}} (z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X)) (hz : d1 ≫ z.1 = d0 ≫ z.2) :
  hornD0 ≫ HornEmb1Equiv.invFun ⟨z,hz⟩ = z.1 := r1 _ _

lemma need2 {X : SSet.{0}} (z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X)) (hz : d1 ≫ z.1 = d0 ≫ z.2) :
  hornD2 ≫ HornEmb1Equiv.invFun ⟨z,hz⟩ = z.2 := r2 _ _

-- the unique hom determined by (p₀.p, p₂.p) ∈ {z : (Δ[1] ⟶ X) × (Δ[1] ⟶ X) // d1 ≫ z.1 = d0 ≫ z.2 }
noncomputable
def transHom {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] (p₀ : Path a b) (p₂ : Path b c) :
  (Λ[2,1] ⟶ X) := HornEmb1Equiv.invFun ⟨⟨p₀.p, p₂.p⟩, by rw [p₀.hp1, p₂.hp0]⟩

lemma transHom_compHorn0 {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] (p₀ : Path a b) (p₂ : Path b c) :
  hornD0 ≫ (transHom p₀ p₂) = p₀.p := need0 _ _

lemma transHom_compHorn2 {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] (p0 : Path a b) (p2 : Path b c) :
  hornD2 ≫ (transHom p0 p2) = p2.p := need2 _ _

noncomputable
def Path.trans {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b c → Path a c := by
    intro p₀ p₂
    let g := Exists.choose (IsKan.cond _ _ (transHom p₀ p₂))
    have hg := Exists.choose_spec (IsKan.cond _ _ (transHom p₀ p₂))
    refine ⟨D1 ≫ g, ?_, ?_⟩
    · change d0 ≫ hornD0 ≫ hornInclusion _ _ ≫ g = a
      rw [← hg, transHom_compHorn0]
      exact p₀.hp0
    · have := D1_comp_d1
      apply_fun (fun a => a ≫ g) at this
      change d1 ≫ D1 ≫ g = d1 ≫ D2 ≫ g at this
      rw [this]
      change d1 ≫ hornD2 ≫ hornInclusion _ _ ≫ g = c
      rw [← hg, transHom_compHorn2]
      exact p₂.hp1

-- symm will be easy to do once ive completed trans, just holding off so it doesnt get too cluttered
noncomputable
def symmHom {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] :
  Path a b → (Λ[2,2] ⟶ X) := sorry
    --rintro ⟨p, h0, h1⟩
    --apply HornEmbInv X 1 2
    --rintro ⟨j, hj : j ≠ 2⟩
    --by_cases j = 1
    --exact p
    --have : j = 0 := sorry
    --exact standardSimplex.map (σ 0) ≫ a

@[simp]
lemma symmHom_compHorn0 {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] (p : Path a b) :
  HornD0 ≫ (symmHom p) = p.p := sorry

@[simp]
lemma symmHom_compHorn1 {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] (p : Path a b) :
  HornD1 ≫ (symmHom p) = standardSimplex.map (σ 0) ≫ a := sorry

noncomputable
def Path.symm {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b a := by
    intro p
    let g := Exists.choose (IsKan.cond _ _ (symmHom p))
    have hg := Exists.choose_spec (IsKan.cond _ _ (symmHom p))
    refine ⟨D2 ≫ g, ?_, ?_⟩
    · have := D2_comp_d0
      apply_fun (fun a => a ≫ g) at this
      change d0 ≫ D2 ≫ g = d1 ≫ HornD0 ≫ hornInclusion _ _ ≫ g at this
      rw [this, ← hg, symmHom_compHorn0]
      exact p.hp1
    · have := D1_comp_d1
      apply_fun (fun a => a ≫ g) at this
      change d1 ≫ HornD1 ≫ hornInclusion _ _ ≫ g = d1 ≫ D2 ≫ g at this
      rw [← this, ← hg, symmHom_compHorn1]
      have aux := @δ_comp_σ_succ 0 0
      apply_fun (fun x => (standardSimplex.map x) ≫ a) at aux
      change d1 ≫ standardSimplex.map (σ 0) ≫ a = standardSimplex.map (𝟙 ([0] : SimplexCategory)) ≫ a at aux
      rw [aux]
      ext
      change a.app _ ((standardSimplex.map (𝟙 ([0] : SimplexCategory))).app _ _) = _
      dsimp [standardSimplex]
      simp only [OrderHom.id_comp, Hom.mk_toOrderHom]

/-
example (X Y : SSet) (n) : (ProdObjIso X Y n).hom ≫ Limits.prod.fst = (Limits.prod.fst (X := X) (Y := Y)).app n := by
  dsimp [ProdObjIso]
  aesop
-/

noncomputable
def ProdObjIso {X Y : SSet} (n) : (X ⨯ Y).obj n ≅ (X.obj n × Y.obj n) :=
  show ((evaluation _ _).obj n).obj (X ⨯ Y) ≅ _ from
  preservesLimitIso _ _ ≪≫ Limits.HasLimit.isoOfNatIso
    (Limits.pairComp X Y ((evaluation SimplexCategoryᵒᵖ Type).obj n))
    ≪≫ (Types.binaryProductIso _ _)

def Prod (X Y : SSet) : SSet where
  obj n := X.obj n × Y.obj n
  map f a := (X.map f a.1, Y.map f a.2)

@[simp]
def proj1 {X Y : SSet} : (Prod X Y) ⟶ X where
  app _ a := a.1

@[simp]
def proj2 {X Y : SSet} : (Prod X Y) ⟶ Y where
  app _ a := a.2

@[simps! pt]
def binProdCone (X Y : SSet.{0}) : BinaryFan X Y :=
  BinaryFan.mk (proj1) (proj2)

@[simp]
theorem binProdCone_fst (X Y : SSet) : (binProdCone X Y).fst = proj1 :=
  rfl

@[simp]
theorem binProdCone_snd (X Y : SSet) : (binProdCone X Y).snd = proj2 :=
  rfl

@[simps]
def binProdLim (X Y : SSet) : IsLimit (binProdCone X Y) where
  lift (s : BinaryFan X Y) := {
    app := fun n x => ((s.fst).app n x, (s.snd).app n x)
    naturality := fun j k g => by
      ext a
      simp [FunctorToTypes.naturality]
      congr
  }
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq s t ht := by
    simp only [← ht ⟨WalkingPair.right⟩, ← ht ⟨WalkingPair.left⟩]
    congr

def binProdLimCone (X Y : SSet) : Limits.LimitCone (pair X Y) :=
  ⟨_, binProdLim X Y⟩

noncomputable def binProdIso (X Y : SSet) : X ⨯ Y ≅ Prod X Y :=
  limit.isoLimitCone (binProdLimCone X Y)

def IHom (X Y : SSet) : SSet where
  obj n := Prod (standardSimplex.obj n.unop) X ⟶ Y
  map {m n} f F := {
    app := fun k a => F.app k ((standardSimplex.map f.unop).app k a.1, a.2)
    naturality := fun j k g => by
      ext a
      exact congr_fun (F.naturality g) (a.1 ≫ f.unop, a.2)
  }
  map_id _ := by
    dsimp only [standardSimplex]
    aesop_cat

example (X Y Z : SSet) (h : X ≅ Z) : (X ⟶ Y) ≅ (Z ⟶ Y) := ((yoneda.obj Y).mapIso h.op).symm

/- easier way? -/
noncomputable def HomIsoProd {X Y : SSet} : (X ⟶ Y) ≅ (Prod Δ[0] X ⟶ Y) :=
  ((yoneda.obj Y).mapIso ((leftUnitor X).symm ≪≫ (binProdIso Δ[0] X)).op).symm

noncomputable
def IHomZero {X Y : SSet} : (X ⟶ Y) ≅ (IHom X Y) _[0] := HomIsoProd ≪≫ (eqToIso rfl)

def bruh (X Y : SSet) : (Δ[0] ⟶ IHom X Y) ≃ (IHom X Y) _[0] := yonedaEquiv

def homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) :=
  Path (yonedaEquiv.invFun (IHomZero.hom f)) (yonedaEquiv.invFun (IHomZero.hom g))

/-
TODO: Define this in terms of paths.

structure homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) where
  F : Δ[1] ⨯ X ⟶ Y
  F0 : (leftUnitor X).inv ≫ (prod.map d0 (𝟙 X)) ≫ F = f
  F1 : (leftUnitor X).inv ≫ (prod.map d1 (𝟙 X)) ≫ F = g
-/

--class HomotopyInvariant {X : SSet.{0}} (motive : ⦃a b : pt ⟶ X⦄ → Path a b → Sort u) where
--  ind : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ⦃x y : pt ⟶ X⦄ → (p : Path x y) → motive p
--  ind_rfl : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ind rfl (Path.rfl x) = rfl x
