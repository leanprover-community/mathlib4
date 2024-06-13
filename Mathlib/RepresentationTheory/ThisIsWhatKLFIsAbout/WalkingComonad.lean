import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.WithTerminal
import Mathlib.CategoryTheory.Bicategory.SingleObj
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.ComposableArrows

open CategoryTheory

namespace ComposableArrows

variable {C : Type*} [Category C] {n : ℕ}

-- I think I've strayed far from the light
lemma hom_ext (F G : ComposableArrows C n) (h : F = G) :
    eqToHom (h ▸ rfl) ≫ F.hom = G.hom ≫ eqToHom (h ▸ rfl) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

namespace Postcomp

variable (F : ComposableArrows C n) (X : C)

def obj (f : Fin (n + 1) → C) : Fin (n + 1 + 1) → C :=
  Fin.snoc f X

variable {X}

@[simp]
lemma obj_zero {n : ℕ} (f : Fin (n + 1) → C) : obj X f 0 = f 0 := by
  rw [← Fin.castSucc_zero]
  exact Fin.snoc_castSucc _ _ _

@[simp]
lemma obj_last {n : ℕ} (f : Fin (n + 1) → C) : obj X f (Fin.last (n + 1)) = X := by
  simp only [obj]
  convert Fin.snoc_last _ _

lemma obj_init {n : ℕ} (f : Fin (n + 1) → C) (i : Fin (n + 1)) :
    obj X f i.castSucc = f i := by
  simp only [obj]
  exact @Fin.snoc_castSucc (n + 1) (fun _ => C) X f i

lemma obj_init' {n : ℕ} (f : Fin (n + 1) → C) (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    obj X f i = f (i.castPred hi) := by
  convert obj_init f (i.castPred hi)

lemma obj_init'' {n : ℕ} (f : Fin (n + 1) → C) (i : ℕ) (hi : i < n + 1 := by valid) :
    obj X f ⟨i, by linarith⟩ = f ⟨i, by linarith⟩ :=
  obj_init f ⟨i, hi⟩

lemma obj_init_last {n : ℕ} (f : Fin (n + 1) → C) :
    obj X f ⟨n, by linarith⟩ = f (Fin.last n) := by
  convert obj_init' f _ _
  simp [Fin.ne_iff_vne]

variable (f : F.right ⟶ X)

def map {n : ℕ} (F : ComposableArrows C n) (f : F.right ⟶ X)
    (i j : Fin (n + 1 + 1)) (hij : i ≤ j) :
    obj X F.obj i ⟶ obj X F.obj j :=
  if hi : i = Fin.last (n + 1) then eqToHom (by rw [hi] at hij; rw [hi, Fin.last_le_iff.1 hij])
    else if hj : j = Fin.last (n + 1) then
      eqToHom (obj_init' _ _ hi) ≫ F.map' i (j - 1) sorry sorry ≫ eqToHom (by simp [hj])
      ≫ f ≫ eqToHom (by rw [hj, obj_last])
    else eqToHom (obj_init' _ _ hi) ≫ F.map' i j sorry sorry ≫ eqToHom (obj_init' _ _ hj).symm

@[simp]
lemma map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _ := by
  unfold map
  split_ifs with h
  · rfl
  · simp only [ComposableArrows.map', homOfLE_refl, CategoryTheory.Functor.map_id]
    erw [Category.id_comp]
    simp only [eqToHom_trans, eqToHom_refl]

@[simp]
lemma map_last_last :
    map F f (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _) =
      eqToHom (obj_init _ _) ≫ f ≫ eqToHom (obj_last _).symm := by
  unfold map
  rw [dif_neg (ne_of_lt <| Fin.castSucc_lt_last _), dif_pos rfl]
  simp only [Fin.val_last, Nat.add_succ_sub_one, Nat.add_zero, ComposableArrows.map',
    Fin.coe_castSucc, homOfLE_refl, CategoryTheory.Functor.map_id, eqToHom_refl, Category.id_comp,
    Fin.castSucc_mk]
  erw [Category.id_comp]

@[simp]
lemma map_last_last' :
    map F f ⟨n, by linarith⟩ (Fin.last (n + 1)) (Fin.le_last _) =
      eqToHom (obj_init _ _) ≫ f ≫ eqToHom (obj_last _).symm := by
  convert map_last_last F f

@[simp]
lemma map_last_last'' :
    map F f ⟨n, by linarith⟩ ⟨n + 1, by linarith⟩ (Fin.le_last _) =
      eqToHom (obj_init _ _) ≫ f ≫ eqToHom (obj_last _).symm := by
  convert map_last_last F f

@[simp]
lemma map_castSucc_last (j : Fin (n + 1)) :
    map F f j.castSucc (Fin.last (n + 1)) (le_of_lt <| Fin.castSucc_lt_last _)
      = eqToHom (obj_init' _ _ <| ne_of_lt <| Fin.castSucc_lt_last _)
      ≫ F.map' j n sorry sorry ≫ f ≫ eqToHom (obj_last _).symm := by
  simp [map, dif_neg (ne_of_lt <| Fin.castSucc_lt_last _), dif_pos rfl]

@[simp]
lemma map_lt_last (j : ℕ) (hj : j < n + 1 := by valid) :
    map F f ⟨j, by linarith⟩ (Fin.last (n + 1)) (le_of_lt hj)
      = eqToHom (obj_init' _ _ <| ne_of_lt hj)
      ≫ F.map' j n sorry sorry ≫ f ≫ eqToHom (obj_last _).symm := by
  convert map_castSucc_last F f ⟨j, by linarith⟩

@[simp]
lemma map_lt_lt (i j : ℕ) (hi : i < n + 1 := by valid) (hj : j < n + 1 := by valid)
    (hij : i ≤ j := by valid) :
    map F f ⟨i, by linarith⟩ ⟨j, by linarith⟩ hij =
      eqToHom (obj_init'' _ _ hi) ≫ F.map' i j sorry sorry
      ≫ eqToHom (obj_init'' _ _ hj).symm := by
  simp [map, dif_neg, Fin.last, ne_of_lt hj, ne_of_lt hi]

lemma map_comp {i j k : Fin (n + 2)} (hij : i ≤ j := by valid) (hjk : j ≤ k := by valid) :
    map F f i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk := by
  unfold map
  split_ifs with hi hj hk hk hj hj
  · simp only [eqToHom_trans]
  · exfalso
    subst hi
    exact hj (Fin.last_le_iff.1 hij)
  · exfalso
    subst hi
    exact hj (Fin.last_le_iff.1 hij)
  · subst hj hk
    simp
  · subst hk
    simp [← F.map_comp_assoc]
  · exfalso
    subst hj
    exact hk (Fin.last_le_iff.1 hjk)
  · simp [← F.map_comp_assoc]

end Postcomp

variable (F : ComposableArrows C n) {X : C}

/-- "Postcomposition" of `F : ComposableArrows C n` by a morphism `f : F.right ⟶ X`. -/
@[simps]
def postcomp {X : C} (f : F.right ⟶ X) : ComposableArrows C (n + 1) where
  obj := Postcomp.obj X F.obj
  map g := Postcomp.map F f _ _ (leOfHom g)
  map_id := Postcomp.map_id F f
  map_comp g g' := Postcomp.map_comp F f (leOfHom g) (leOfHom g')

theorem postcomp_map' (f : F.right ⟶ X) (i j : Fin (n + 1 + 1)) (hij : i ≤ j) :
    (postcomp F f).map' i j hij = Postcomp.map F f i j hij := rfl

@[simp]
theorem postcomp_left (f : F.right ⟶ X) :
    (postcomp F f).left = F.left :=
  Postcomp.obj_init'' F.obj 0 (by linarith)

@[simp]
theorem postcomp_right (f : F.right ⟶ X) :
    (postcomp F f).right = X :=
  Postcomp.obj_last _

theorem postcomp_hom (f : F.right ⟶ X) :
    (postcomp F f).hom = eqToHom (postcomp_left _ _)
      ≫ F.hom ≫ f ≫ eqToHom (postcomp_right _ _).symm :=
  Postcomp.map_lt_last F f 0 <| by linarith

#check Iso.inv_comp_eq
open ComposableArrows

noncomputable def mkOfObjOfMapSuccPrecomp (obj : Fin (n + 1) → C)
    (mapSucc : (i : Fin n) → obj i.castSucc ⟶ obj i.succ)
    (X : C) (f : X ⟶ obj 0) :
    precomp (mkOfObjOfMapSucc obj mapSucc) f
      ≅ mkOfObjOfMapSucc (Fin.cons X obj) (Fin.cons f mapSucc) :=
  isoMk (Fin.cases (Iso.refl _) (fun _ => Iso.refl _)) fun i => by
    induction' i with i _
    · intro h0
      simp [-map', mkOfObjOfMapSucc_map_succ, ← Fin.mk_one]
    · intro hi
      simp [-map', mkOfObjOfMapSucc_map_succ, Fin.cons]

/-
@[simp]
noncomputable def ohmyfuckinggod (obj : Fin (n + 1) → C)
    (mapSucc : (i : Fin n) → obj i.castSucc ⟶ obj i.succ)
    (X : C) (f : (mkOfObjOfMapSucc obj mapSucc).right ⟶ X) (i : Fin (n + 1)) :
  @Fin.snoc (n + 1) (fun _ => C) obj X i.castSucc
    ⟶ @Fin.snoc (n + 1) (fun _ => C) obj X i.succ :=
  if h : i = Fin.last n then
    eqToHom (by simp only [h, Fin.snoc_castSucc, mkOfObjOfMapSucc_obj]; rfl)
    ≫ f ≫ eqToHom (by simp [h])
  else eqToHom (by simp [h]) ≫ mapSucc (i.castPred h)
    ≫ eqToHom (by simp [Fin.snoc, dif_pos, Fin.val_lt_last h]; rfl)

lemma mkOfObjOfMapSucc_postcomp (obj : Fin (n + 1) → C)
    (mapSucc : (i : Fin n) → obj i.castSucc ⟶ obj i.succ)
    (X : C) (f : (mkOfObjOfMapSucc obj mapSucc).right ⟶ X) :
    postcomp (mkOfObjOfMapSucc obj mapSucc) f
      = mkOfObjOfMapSucc (Fin.snoc obj X) (ohmyfuckinggod _ mapSucc _ f) := by
  refine ComposableArrows.ext ?_ ?_
  · intro i
    by_cases h : i = Fin.last (n + 1)
    · simp_all
    · simp_all [Postcomp.obj, Fin.snoc]
  · intro i hi
    unfold ohmyfuckinggod
    simp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, postcomp_obj, postcomp_map,
      mkOfObjOfMapSucc_obj, eqToHom_refl, Category.comp_id, Category.id_comp,
      mkOfObjOfMapSucc_map_succ]
    rcases em (n = i) with ⟨rfl, h₁⟩
    · rw [dif_pos]
      · simp
      · rfl
    · rw [dif_neg]
      · rw [Postcomp.map_lt_lt _ _ _ _ hi]
        · simp only [Int.reduceNeg, Int.reduceMul, Int.rawCast, Int.cast_id, Nat.rawCast, Nat.cast_id,
            Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd, Int.ofNat_eq_coe, eq_mp_eq_cast,
            id_eq, mkOfObjOfMapSucc_obj, mkOfObjOfMapSucc_map_succ, Fin.castSucc_mk, Fin.succ_mk,
            Nat.succ_eq_add_one]
          rfl
        · simp_all [Fin.ne_iff_vne, ne_comm]
-/
lemma mkOfObjOfMapSucc_postcomp' (obj : Fin (n + 1) → C) (obj' : Fin (n + 2) → C)
    (mapSucc : (i : Fin n) → obj i.castSucc ⟶ obj i.succ)
    (mapSucc' : (i : Fin (n + 1)) → obj' i.castSucc ⟶ obj' i.succ)
    (X : C) (f : obj (Fin.last n) ⟶ X)
    (hobj₁ : ∀ i : Fin (n + 1), obj i = obj' i.castSucc)
    (hobj₂ : obj' (Fin.last (n + 1)) = X)
    (hmap₁ : ∀ i : Fin n, eqToHom (by simp [hobj₁]) ≫ mapSucc i
      = mapSucc' i.castSucc ≫ eqToHom (by simp [← hobj₁, ← Fin.castSucc_fin_succ]))
    (hmap₂ : eqToHom (by simp [← hobj₁]) ≫ f = mapSucc' (Fin.last n) ≫ eqToHom (by simp [hobj₂])) :
    postcomp (mkOfObjOfMapSucc obj mapSucc) f = mkOfObjOfMapSucc obj' mapSucc' := by
  refine ComposableArrows.ext ?_ ?_
  · intro i
    rcases em (i = Fin.last (n + 1)) with ⟨rfl, hi⟩
    · simp_all only [Fin.succ_last, Nat.succ_eq_add_one, postcomp_obj, Postcomp.obj_last,
        mkOfObjOfMapSucc_obj]
    · rw [← Fin.castSucc_castPred i]
      simp_all only [Fin.succ_last, Nat.succ_eq_add_one, postcomp_obj, Postcomp.obj,
        Fin.snoc_castSucc, mkOfObjOfMapSucc_obj]
      assumption
      done
  · intro i hin
    simp_all only [Fin.succ_last, Nat.succ_eq_add_one, id_eq, Int.Nat.cast_ofNat_Int, postcomp_obj,
      postcomp_map, mkOfObjOfMapSucc_obj, mkOfObjOfMapSucc_map_succ]
    rcases em (i = Fin.last n) with ⟨rfl, hi⟩
    · simp_all only [← eqToIso.hom, ← Iso.eq_inv_comp, eqToIso.inv, Fin.val_last,
        Postcomp.map_last_last'', Fin.castSucc_mk, mkOfObjOfMapSucc_obj, Category.assoc]
      simp_all only [eqToIso.hom, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rfl
    · rw [Postcomp.map_lt_lt _ _ _ _ hin sorry]
      simp_all only [← eqToIso.hom, ← Iso.eq_inv_comp, eqToIso.inv, Int.rawCast, Int.cast_id,
        Nat.rawCast, Nat.cast_id, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.ofNat_eq_coe,
        Fin.val_last, eq_mp_eq_cast, id_eq, mkOfObjOfMapSucc_obj, mkOfObjOfMapSucc_map_succ,
        Fin.castSucc_mk, Fin.succ_mk, Nat.succ_eq_add_one, Category.assoc]
      simp only [Int.reduceNeg, Int.reduceMul, Int.reduceAdd, eqToIso.hom, eqToHom_trans,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-
noncomputable def mkOfObjOfMapSuccPostcomp (obj : Fin (n + 1) → C)
    (mapSucc : (i : Fin n) → obj i.castSucc ⟶ obj i.succ)
    (X : C) (f : (mkOfObjOfMapSucc obj mapSucc).right ⟶ X) :
    postcomp (mkOfObjOfMapSucc obj mapSucc) f
      ≅ mkOfObjOfMapSucc (Fin.snoc obj X) (ohmyfuckinggod _ mapSucc _ f) :=
  eqToIso (mkOfObjOfMapSucc_postcomp _ _ _ _)
-/
variable {n : ℕ} (i : Fin (n + 2))

#check Fin.castSucc
#check (i + 1)
#synth Category (Fin n)
open Simplicial
#check ComposableArrows
#check Function.iterate_add_eq_iterate

variable {p : Fin (n + 1)} {i j : Fin n}

noncomputable def idfkδ (m n : ℕ) (i : (j : Fin n) → Fin (m + j + 2)) :
    ComposableArrows SimplexCategory n :=
  ComposableArrows.mkOfObjOfMapSucc (fun k => [m + k]) fun k =>
    SimplexCategory.δ (i k)

noncomputable def idfkσ (m n : ℕ) (i : (j : Fin n) → Fin (m + j + 1)) :
    ComposableArrows SimplexCategoryᵒᵖ n :=
  ComposableArrows.mkOfObjOfMapSucc (fun k => Opposite.op [m + k]) fun k =>
    (SimplexCategory.σ (i k)).op

noncomputable def idfkδ' (m n : ℕ) (i : (j : Fin (m - n)) → Fin (m + j + 2)) :
    ComposableArrows SimplexCategory (m - n) :=
  ComposableArrows.mkOfObjOfMapSucc (fun k => [m + k]) fun k =>
    SimplexCategory.δ (i k)

open ComposableArrows
theorem mono_gen (m n : ℕ) (f : ([m] : SimplexCategory) ⟶ [m + n]) [Mono f] :
    ∃ (i : (j : Fin n) → Fin (m + j + 2)),
      f = (idfkδ m n i).hom := by
  induction' n with n hn
  · use 0
    simp only [Nat.add_zero, idfkδ, Nat.reduceAdd, Fin.coe_castSucc, Pi.zero_apply]
    have : f = (mk₀ ([m] : SimplexCategory)).hom := by
      rw [SimplexCategory.eq_id_of_mono f]
      rfl
    rw [this]
    congr
    exact ext₀ rfl
  · have huh : ¬Function.Surjective f.toOrderHom := by
      apply mt <| Fintype.card_le_of_surjective f.toOrderHom
      simp only [not_le, SimplexCategory.len_mk, Fintype.card_fin, add_lt_add_iff_right,
        lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]
    rcases not_forall.1 huh with ⟨j, hj⟩
    rw [← SimplexCategory.factor_δ_spec f j <| not_exists.1 hj]
    letI : Mono (SimplexCategory.factor_δ f j) :=
      mono_of_mono_fac (SimplexCategory.factor_δ_spec f j <| not_exists.1 hj)
    sleep 1
    rcases hn (SimplexCategory.factor_δ f j) with ⟨k, hk⟩
    use Fin.snoc k j
    rw [hk]
    have := postcomp_hom (idfkδ m n k) (SimplexCategory.δ j)
    simp_rw [← eqToIso.hom, ← Iso.inv_comp_eq, ← Category.assoc, ← Iso.comp_inv_eq] at this
    rw [← this, eqToIso.inv, Iso.comp_inv_eq, eqToIso.hom]
    refine hom_ext (postcomp (idfkδ m n k) (SimplexCategory.δ j))
      (idfkδ m (n + 1) (Fin.snoc k j)) ?_
    exact mkOfObjOfMapSucc_postcomp' _ _ _ _ _ _ (fun _ => rfl) rfl (fun _ => by simp) <| by simp

/-
def hmmm {P : (m n : SimplexCategory) → (m ⟶ n) → Sort*}
    (Pid : ∀ (n : SimplexCategory), P n n (𝟙 _))
    (Pcomp : ∀ {m n o} (f : m ⟶ n) (g : n ⟶ o), P m n f → P n o g → P m o (f ≫ g))
    (Pδ : ∀ {n} (i : Fin (n + 2)), P [n] [n + 1] (SimplexCategory.δ i))
    (Pσ : ∀ {n} (i : Fin (n + 1)), P [n + 1] [n] (SimplexCategory.σ i)) (m n : SimplexCategory)
    (f : m ⟶ n) : P m n f := by
  let F := Classical.choice <| Limits.HasStrongEpiMonoFactorisations.has_fac f
  rcases F with ⟨⟨j, a, b, hab⟩, he, hm, hh⟩
-/

end ComposableArrows
