import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.Tactic.Attr.Register

universe v u

open CategoryTheory

namespace Rep

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
variable (A : Rep k G)

@[simps]
noncomputable def applyAsHom (g : G) : A ⟶ A where
  hom := ModuleCat.ofHom (A.ρ g)
  comm _ := by ext; simp [← Module.End.mul_apply, ← map_mul, Std.Commutative.comm]

noncomputable def finiteCyclicComplex.d (g : G) (n : ℕ) : A ⟶ A :=
  match n with
  | 0 => applyAsHom A g - 𝟙 A
  | 1 => norm A
  | (n + 2) => finiteCyclicComplex.d g n

@[simp]
lemma finiteCyclicComplex.d_even (g : G) (n : ℕ) (hn : Even n) :
    d A g n = applyAsHom A g - 𝟙 A :=
  match n with
  | 0 => by aesop
  | 1 => by aesop
  | (n + 2) => d_even g n (by revert hn; simp [parity_simps])

@[simp]
lemma finiteCyclicComplex.d_odd (g : G) (n : ℕ) (hn : Odd n) :
    d A g n = norm A :=
  match n with
  | 0 => by aesop
  | 1 => by aesop
  | (n + 2) => d_odd g n (by revert hn; simp [parity_simps])

lemma finiteCyclicComplex.d_comp_d (g : G) (n : ℕ) :
    d A g (n + 1) ≫ d A g n = 0 :=
  match n with
  | 0 => by ext; simp [sub_eq_add_neg]
  | 1 => by ext; simp [sub_eq_add_neg]
  | (n + 2) => finiteCyclicComplex.d_comp_d g n

noncomputable def finiteCyclicComplex (g : G) :
    ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun _ => A) (finiteCyclicComplex.d A g) fun n =>
    finiteCyclicComplex.d_comp_d A g n

variable (k)

noncomputable abbrev C (n : ℕ) := leftRegular k (Multiplicative <| Fin (n + 1))

variable (n : ℕ)
open Multiplicative

open Finsupp

variable {k n} in
lemma coeff_eq_of_mem_ker
    (x : C k n) (hx : (applyAsHom (C k n) (ofAdd 1)).hom x - x = 0)
    (i : Multiplicative <| Fin (n + 1)) :
    x i = x 1 := by
  refine Multiplicative.rec (fun i => ?_) i
  refine Fin.inductionOn i ?_ ?_
  · rfl
  · intro i hi
    rw [← hi]
    have := Finsupp.ext_iff.1 hx (ofAdd i.succ)
    simp [sub_eq_zero, ← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub, -ofAdd_sub] at this
    rw [← this]
    congr
    rw [sub_eq_iff_eq_add]
    norm_num

lemma exactness (x : C k n) (hx : (applyAsHom (C k n) (ofAdd 1)).hom x - x = 0) :
    ∃ y : C k n, (C k n).norm.hom y = x := by
  use single 1 (x 1)
  ext j
  simp [Representation.norm, coeff_eq_of_mem_ker _ hx]

lemma norm_apply :
    ConcreteCategory.hom (C k n).norm.hom =
      (LinearMap.lsmul k _).flip ((C k n).norm.hom (single 1 1)) ∘ₗ
      Finsupp.linearCombination _ (fun _ => 1) := by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective (· * i)
    (Group.mulRight_bijective i) (by aesop) (by aesop)

lemma coeff_sum_of_norm_eq_zero (x : C k n) (hx : (C k n).norm.hom x = 0) :
    x.linearCombination k (fun _ => (1 : k)) = 0 := by
  rw [norm_apply] at hx
  simpa [norm, Representation.norm] using Finsupp.ext_iff.1 hx 1

lemma norm_eq_zero_of_coeff_sum (x : C k n) (hx : x.linearCombination k (fun _ => (1 : k)) = 0) :
    (C k n).norm.hom x = 0 := by
  rw [norm_apply]
  ext
  simp_all

lemma _root_.Fin.neg_one : -(1 : Fin (n + 1)) = Fin.last n := by
  apply add_right_cancel (b := 1)
  norm_num

lemma _root_.Fin.succ_neg_one : (-(1 : Fin (n + 1))).succ = Fin.last (n + 1) := by
  rw [Fin.neg_one]
  norm_num

lemma _root_.Fin.succ_sub_one (i : Fin n) :
    i.succ - 1 = i.castSucc := by
  rw [sub_eq_iff_eq_add]
  norm_num

@[to_additive]
theorem _root_.Fin.partialProd_of_succ_eq {n : ℕ} {M : Type*} [Monoid M] {f : Fin n → M}
    (j : Fin n) {i : Fin (n + 1)} (hij : j.succ = i) :
    Fin.partialProd f i = Fin.partialProd f (Fin.castSucc j) * f j :=
  hij ▸ Fin.partialProd_succ _ _

@[to_additive]
lemma _root_.Fin.partialProd_castSucc {n : ℕ} {M : Type*} [Monoid M]
    {f : Fin (n + 1) → M} {i : Fin (n + 1)} :
    Fin.partialProd (f ∘ Fin.castSucc) i = Fin.partialProd f i.castSucc := by
  refine i.inductionOn ?_ ?_
  · simp
  · intro i hi
    simp_all [Fin.partialProd_succ]

lemma _root_.Fin.partialSum_last (x : Fin (n + 1) → k) :
    Fin.partialSum x (Fin.last (n + 1)) = ∑ i, x i := by
  induction' n with n hn
  · rw [Fin.partialSum_of_succ_eq 0] <;> simp
  · have := hn (x ∘ Fin.castSucc)
    rw [Fin.partialSum_castSucc] at this
    rw [Fin.partialSum_of_succ_eq (Fin.last (n + 1)) (by aesop),
      Fintype.sum_eq_add_sum_subtype_ne _ (Fin.last (n + 1)), add_comm, this, add_right_inj]
    exact Finset.sum_bijective (fun i => Subtype.mk i.castSucc (Fin.castSucc_ne_last _))
      ⟨fun _ _ _ => by simp_all, fun x => ⟨x.1.castPred x.2, by simp⟩⟩ (by aesop) (by aesop)

lemma exactness₂ (x : C k n) (hx : (C k n).norm.hom x = 0) :
    ∃ y : C k n, (applyAsHom (C k n) (ofAdd 1)).hom y - y = x := by
  let Y : (Fin (n + 1)) →₀ k := Finsupp.equivFunOnFinite.symm
    (-Fin.partialSum (x ∘ ofAdd) ∘ Fin.succ ∘ toAdd)
  use Y
  ext i
  refine i.rec fun i => i.cases ?_ ?_
  · simp [← ofAdd_neg, Y, equivFunOnFinite, Fin.succ_neg_one]
    rw [Fin.partialSum_last]
    rw [Fin.partialSum_of_succ_eq 0]
    · rw [norm_apply] at hx
      replace hx := Finsupp.ext_iff.1 hx 1
      simp_all [Representation.norm, linearCombination]
      rw [Finsupp.sum_fintype (h := by simp)] at hx
      rw [← hx]
      exact Finset.sum_bijective ofAdd ofAdd.bijective (by simp) (by simp)
    · rfl
  · intro i
    simp_all [← ofAdd_neg, Y, equivFunOnFinite, neg_add_eq_sub]
    rw [Fin.succ_sub_one]
    rw [sub_eq_neg_add]
    rw [i.succ_castSucc]
    rw [Fin.partialSum_right_neg]
    rfl

lemma exactness₃ (x : C k n) (hx : x.linearCombination k (fun _ => (1 : k)) = 0) :
    ∃ y : C k n, (applyAsHom (C k n) (ofAdd 1)).hom y - y = x := by
  exact exactness₂ _ _ _ (norm_eq_zero_of_coeff_sum _ _ _ hx)

open ZeroObject

@[simps!]
noncomputable def finiteCyclicResolution.π (g : G) :
    finiteCyclicComplex (leftRegular k G) g ⟶
      (ChainComplex.single₀ (Rep k G)).obj (trivial k G k) :=
  ((finiteCyclicComplex _ g).toSingle₀Equiv _).symm
    ⟨leftRegularHom _ 1, (leftRegularHomEquiv _).injective <| by
      simp [finiteCyclicComplex, ChainComplex.of, sub_eq_add_neg, leftRegularHomEquiv]⟩

open ShortComplex Representation

theorem lol (g : G) (m : ℕ) :
    (finiteCyclicComplex (leftRegular k G) g).ExactAt (m + 3) ↔
    (finiteCyclicComplex (leftRegular k G) g).ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (m + 4) (m + 3) (m + 2) (by simp) (by simp)]
  rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
  sorry

lemma finiteCyclicResolution.zModQuasiIsoAt (m : ℕ) :
    QuasiIsoAt (finiteCyclicResolution.π k (ofAdd (1 : ZMod (n + 1)))) m := by
  match m with
  | 0 =>
    simp [π]
    rw [ChainComplex.quasiIsoAt₀_iff, quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
      simp
      rw [ShortComplex.moduleCat_exact_iff]
      intro (x : _ →₀ k) hx
      have := exactness₃ k n x (by simpa using hx)
      rcases this with ⟨y, hy⟩
      use y
      simp [finiteCyclicComplex, ChainComplex.of]
      simp [sub_eq_add_neg] at hy ⊢
      exact hy
    · rw [Rep.epi_iff_surjective]
      intro x
      use single 1 x
      simp [finiteCyclicComplex, ChainComplex.of, finiteCyclicComplex.d,
        ChainComplex.toSingle₀Equiv]
  | 1 =>
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x : _ →₀ k) hx
    have := exactness k n x (by simpa [finiteCyclicComplex, ChainComplex.of, sub_eq_add_neg] using hx)
    clear hx
    simp [finiteCyclicComplex, ChainComplex.of, sub_eq_add_neg]
    exact this
  | 2 =>
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
    rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)]
    apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x : _ →₀ k) hx
    have := exactness₂ k n x (by simpa [finiteCyclicComplex, ChainComplex.of, sub_eq_add_neg] using hx)
    clear hx
    simp_all [finiteCyclicComplex, ChainComplex.of, sub_eq_add_neg]
    exact this
  | (m + 3) =>
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
    rw [HomologicalComplex.exactAt_iff' _ (m + 4) (m + 3) (m + 2) (by simp) (by simp)]
    have := zModQuasiIsoAt (m + 1)
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)] at this
    rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)] at this
    simp_all [finiteCyclicComplex, ChainComplex.of]
    sorry


lemma finiteCyclicResolution.quasiIsoAt (g : G) (n : ℕ) :
    QuasiIsoAt (finiteCyclicResolution.π k g) n :=
  sorry

noncomputable def finiteCyclicResolution (g : G) :
    ProjectiveResolution (trivial k G k) where
  complex := finiteCyclicComplex (leftRegular k G) g
  projective _ := inferInstanceAs <| Projective (leftRegular k G)
  π := finiteCyclicResolution.π k g
  quasiIso := { quasiIsoAt := finiteCyclicResolution.quasiIsoAt k g }

end Rep
