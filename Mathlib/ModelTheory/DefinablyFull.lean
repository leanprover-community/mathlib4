/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
module

public import Mathlib.ModelTheory.Definability
public import Mathlib.ModelTheory.ElementaryChain
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.ModelTheory.Satisfiability

/-!
# Definably full structures

This file constructs large models in which every parameter-definable unary set is either finite or
has the same cardinality as the model.

## Main definitions

- `FirstOrder.Language.UnaryDefinablyFull`: Every infinite parameter-definable unary set has the
  cardinality of the ambient structure.
- `FirstOrder.Language.DefinablyFull`: Every infinite parameter-definable finite-arity set has the
  cardinality of the ambient structure.

## Main results

- `FirstOrder.Language.Theory.exists_elementaryExtension_card_eq_with_full_unary_realizations`
  constructs a one-step elementary extension fully realizing every infinite unary formula over the
  base model.
- `FirstOrder.Language.Theory.exists_model_of_card_definably_full` constructs a definably full
  model of any prescribed infinite cardinality in a countable language.
-/

@[expose] public section

universe u v w z

namespace FirstOrder

namespace Language

open scoped Cardinal

/-- Every infinite unary set definable with parameters from `A` has the cardinality of `M`. -/
def UnaryDefinablyFull
    (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ (A X : Set M), A.Definable₁ L X → X.Infinite → #X = #M

/-- Every infinite finite-arity set definable with parameters from `A` has the cardinality of
`M`. -/
def DefinablyFull (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ (A : Set M) {n : ℕ} (S : Set (Fin n → M)), A.Definable L S → S.Infinite → #S = #M

/-- A structure is definably full if it is unary definably full. -/
theorem definablyFull_of_unary
    {L : Language.{u, v}} {M : Type w} [L.Structure M] [Infinite M]
    (h : UnaryDefinablyFull L M) :
    DefinablyFull L M := by
  simp only [UnaryDefinablyFull, DefinablyFull] at ⊢ h
  intro A n S hSD hSI
  let P (i : Fin n) := (fun x : Fin n → M ↦ x i) '' S
  have hP : ∃ i : Fin n, (P i).Infinite := by
    contrapose! hSI
    exact Set.forall_finite_image_eval_iff.mp hSI
  rcases hP with ⟨i, hPiI⟩
  have hPiD : A.Definable₁ L (P i) := by
    simp only [P, Set.Definable₁]
    convert hSD.image_comp fun _ : Fin 1 ↦ i
    ext x
    simp [funext_iff]
  specialize h A (P i) hPiD hPiI
  apply le_antisymm
  · trans #(Fin n → M)
    · exact Cardinal.mk_set_le S
    · rw [Cardinal.mk_pi, Cardinal.prod_const]
      simpa using Cardinal.power_nat_le (Cardinal.aleph0_le_mk M)
  · simpa [← h] using Cardinal.mk_image_le

namespace Formula

variable {L : Language.{u, v}} {M : Type*} [L.Structure M]

/-- Unary realizations indexed by `Fin 1` are equivalent to their underlying elements. -/
def finOneRealizationsEquiv (φ : L.Formula (Fin 1)) :
    {x : Fin 1 → M | φ.Realize x} ≃ {x : M | φ.Realize fun _ ↦ x} := by
  refine (Equiv.funUnique (Fin 1) M).subtypeEquiv ?_
  intro v
  simp only [Set.mem_ofPred_eq, Equiv.funUnique_apply, Fin.default_eq_zero, Fin.isValue]
  congr!

end Formula

namespace Theory

open Cardinal Set

variable {L : Language.{u, v}} (T : L.Theory)

/-- Given a model `M` of cardinality `κ`, constructs an elementary extension `N` of cardinality
`κ` in which every infinite unary formula with parameters in `M` has `κ` realizations. -/
theorem exists_elementaryExtension_card_eq_with_full_unary_realizations
    {κ : Cardinal.{w}} (M : ModelType.{u, v, w} T) (hM : #M = κ)
    (hκ : ℵ₀ ≤ κ) (hL : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ (N : ModelType.{u, v, w} T) (e : M ↪ₑ[L] N),
      #N = κ ∧
        ∀ {β : Type z} (ψ : L.Formula (β ⊕ Fin 1)) (b : β → M),
          Set.Infinite {x : Fin 1 → M | ψ.Realize (Sum.elim b x)} →
            #({x : Fin 1 → N | ψ.Realize (Sum.elim (e ∘ b) x)}) = κ := by
  classical
  /-
  For each infinite unary formula over `M`, add `κ` many constants intended to be distinct
  realizations of that formula.
  -/
  let F := {φ : L[[M]].Formula (Fin 1) // Set.Infinite {x : M | φ.Realize fun _ ↦ x}}
  have hFcard : #F ≤ Cardinal.lift.{max u v} κ := (Cardinal.mk_subtype_le _).trans <|
    Formula.card_le_withConstants.trans <| by
      simpa [hM] using
        ⟨hκ, add_le_of_le (aleph0_le_lift.mpr hκ)
          (one_le_lift_iff.mpr (one_le_aleph0.trans hκ))
          (add_le_of_le (aleph0_le_lift.mpr hκ) hL le_rfl)⟩
  let I := κ.out
  let fL := L[[M]].lhomWithConstants (F × I)
  let L' := L[[M]][[F × I]]
  have hL'card : Cardinal.lift.{w} L'.card ≤ Cardinal.lift.{max u v w} κ := by
    simp only [card_withConstants, lift_id, mk_prod, lift_add, lift_lift, lift_mul, L']
    rw [Cardinal.lift_id'.{w, max u v}, Cardinal.lift_umax.{w, max u v}]
    have hκ' := aleph0_le_lift.mpr hκ
    exact add_le_of_le hκ' (add_le_of_le hκ' hL (le_of_eq (congrArg _ hM)))
      (mul_le_of_le hκ' hFcard (by simp [I]))
  let subst : F → I → L[[M]][[F × I]].Sentence :=
    fun φ i ↦ (fL.onFormula φ.1).subst (fun _ ↦ (L[[M]].con (φ, i)).term)
  let T₁ := fL.onTheory (L.elementaryDiagram M)
  let T₂ (S : Set (F × I)) := (fun p : F × I ↦ subst p.1 p.2) '' S
  let T₃ (S : Set (F × I)) :=
    ⋃ φ : F, L[[M]].distinctConstantsTheory (S ∩ {p : F × I | p.1 = φ})
  let Γ (s : Finset (F × I)) : L'.Theory := T₁ ∪ T₂ s ∪ T₃ s
  /-
  A finite fragment is satisfiable in `M`: for each formula occurring in the fragment, assign
  its finitely many new constants to distinct elements of its infinite realization set.
  -/
  have hΓ (s : Finset (F × I)) : (Γ s).IsSatisfiable := by
    let sφi (φ : F) : Finset I := ({v : F × I | v ∈ s ∧ v.1 = φ}.image Prod.snd).toFinset
    have hsφi : ∀ v ∈ s, v.2 ∈ sφi v.1 := by simp [sφi]
    let rs : F → Set M := fun φ ↦ {x | φ.1.Realize fun _ ↦ x}
    have hrs (φ : F) : (rs φ).Infinite := φ.2
    let valOn : s → M := fun v ↦ by
      let f := (hrs v.1.1).natEmbedding
      let n := (sφi v.1.1).equivFin ⟨v.1.2, hsφi v v.2⟩ |>.toNat
      exact (f n).1
    have hrealize (v : s) : v.1.1.1.Realize fun _ ↦ valOn v := by
      change valOn v ∈ rs v.1.1
      simp [valOn, rs]
    have hdistinct (φ : F) (i j : I) (hi : (φ, i) ∈ s) (hj : (φ, j) ∈ s)
        (hval : valOn ⟨(φ, i), hi⟩ = valOn ⟨(φ, j), hj⟩) : i = j := by
      simp only [Fin.toNat_eq_val, valOn] at hval
      exact Subtype.ext_iff.mp <| (sφi φ).equivFin.injective <|
        Fin.ext <| (hrs φ).natEmbedding.injective (Subtype.ext hval)
    letI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
    let val : F × I → M := Function.extend ((↑) : s → F × I) valOn default
    have hval (v : s) : val v = valOn v := by simp [val]
    letI : (constantsOn (F × I)).Structure M := constantsOn.structure val
    have hcon (p : F × I) : (L[[M]].con p : M) = val p := rfl
    have hT₁ : M ⊨ T₁ :=
      (LHom.onTheory_model fL (L.elementaryDiagram ↑M)).mpr model_completeTheory
    have hT₂ : M ⊨ T₂ s := by
      rw [model_iff]
      rintro ψ ⟨v, hv, rfl⟩
      simp only [subst, Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst,
        Term.realize_constants, hcon, LHom.onFormula]
      rw [LHom.realize_onBoundedFormula fL]
      simpa only [Formula.Realize, ← hval] using hrealize ⟨v, hv⟩
    have hT₃ : M ⊨ T₃ s := by
      simp only [distinctConstantsTheory, model_iff, mem_iUnion, mem_image, mem_inter_iff, mem_prod,
        SetLike.mem_coe, mem_ofPred_eq, mem_compl_iff, mem_diagonal_iff, ne_eq, Prod.exists,
        ↓existsAndEq, and_true, Prod.mk.injEq, not_and, forall_const, forall_exists_index, and_imp,
        T₃]
      intro ψ φ i j hi hj hij rfl
      simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
        Term.realize_constants, hcon]
      contrapose! hij
      exact hdistinct φ i j hi hj (by simpa [← hval] using hij)
    haveI : M ⊨ Γ s := (hT₁.union hT₂).union hT₃
    exact Model.isSatisfiable M
  /-
  The finite theories are directed by inclusion, and their union is the theory containing every
  realization and distinctness requirement.
  -/
  have hΓ' : Directed (· ⊆ ·) Γ :=
    Monotone.directed_le fun s t hst ↦ by
      simp only [Γ, T₂, T₃]
      exact union_subset_union (union_subset_union subset_rfl (image_mono hst))
        (iUnion_mono fun _ ↦ distinctConstantsTheory_mono
          (inter_subset_inter hst subset_rfl))
  let Sigma := T₁ ∪ T₂ univ ∪ T₃ univ
  have Sigma_eq_iUnion : Sigma = ⋃ s, Γ s := by
    simp only [Sigma, Γ]
    rw [Set.iUnion_union_distrib, Set.iUnion_union_distrib, iUnion_const]
    have hT₂ : T₂ Set.univ = ⋃ s : Finset (F × I), T₂ s := by
      simp only [image_univ, ← image_iUnion, T₂]
      rw [Set.iUnion_eq_univ_iff.mpr fun x ↦ ⟨{x}, by simp⟩, image_univ]
    have hT₃ : T₃ Set.univ = ⋃ s : Finset (F × I), T₃ s := by
      simp only [univ_inter, T₃]
      refine subset_antisymm ?_ (iUnion_subset fun s ↦
        iUnion_mono fun φ ↦ distinctConstantsTheory_mono inter_subset_right)
      refine iUnion_subset fun φ ↦ ?_
      rw [distinctConstantsTheory_eq_iUnion]
      refine iUnion_subset fun s ↦ ?_
      refine subset_iUnion₂_of_subset
        (s.map (Function.Embedding.subtype fun p : F × I ↦ p.1 = φ)) φ ?_
      rw [inter_eq_left.mpr (by
        simp only [Finset.coe_map, Function.Embedding.subtype_apply, Function.Embedding.coe_subtype,
          image_subset_iff, preimage_ofPred_eq]
        exact fun x _ ↦ x.2)]
      simp
    simp [hT₂, hT₃]
  /- Compactness for directed unions now supplies a model of all the requirements at once. -/
  obtain ⟨P⟩ := Sigma_eq_iUnion ▸ (isSatisfiable_directed_union_iff hΓ').mpr hΓ
  letI : L[[M]].Structure P := fL.reduct P
  letI : L.Structure P := (L.lhomWithConstants M).reduct P
  haveI : P ⊨ L.elementaryDiagram M := (LHom.onTheory_model fL _).mp <|
    Theory.Model.mono P.is_model fun _ hψ ↦ Or.inl (Or.inl hψ)
  let eP : M ↪ₑ[L] P := ElementaryEmbedding.ofModelsElementaryDiagram L M P
  have hPcard : Cardinal.lift.{max u v w} κ ≤ Cardinal.lift.{w} #P :=
    hM ▸ lift_mk_le'.mpr ⟨eP, eP.injective⟩
  /-
  The compactness model may be too large. Downward Löwenheim–Skolem gives an elementary submodel
  `N` of cardinality `κ`, which still satisfies the whole expanded theory.
  -/
  obtain ⟨N, ⟨e'⟩, hNcard⟩ :=
    L'.exists_elementaryEmbedding_card_eq_of_le P κ hκ hL'card hPcard
  letI : L[[M]].Structure N := fL.reduct N
  letI : L.Structure N := (L.lhomWithConstants M).reduct N
  have hNSigma : N ⊨ Sigma := (e'.theory_model_iff Sigma).mpr P.is_model
  have hNT₂ : N ⊨ T₂ univ :=
    Theory.Model.mono hNSigma fun _ hψ ↦ Or.inl (Or.inr hψ)
  have hNT₃ : N ⊨ T₃ univ := Theory.Model.mono hNSigma fun _ hψ ↦ Or.inr hψ
  haveI : N ⊨ L.elementaryDiagram M := (LHom.onTheory_model fL _).mp <|
    Theory.Model.mono hNSigma fun _ hψ ↦ Or.inl (Or.inl hψ)
  let eN : M ↪ₑ[L] N := ElementaryEmbedding.ofModelsElementaryDiagram L M N
  haveI : N ⊨ T := (eN.theory_model_iff T).mp (ModelType.is_model M)
  haveI : Nonempty N := by
    simpa [← Cardinal.mk_ne_zero_iff, hNcard, ← Cardinal.one_le_iff_ne_zero] using
      one_le_aleph0.trans hκ
  haveI : (L.lhomWithConstantsMap ⇑eN).IsExpansionOn ↑N :=
    LHom.lhomWithConstantsMap_isExpansionOn_of_eq _ fun _ ↦ rfl
  refine ⟨ModelType.of T N, eN, by simpa, ?_⟩
  intro β ψ b hψb
  /-
  Recode `ψ` with the parameters `b` as a unary formula in the language with constants from `M`.
  Its realization set is still infinite.
  -/
  let φ : L[[M]].Formula (Fin 1) :=
    BoundedFormula.constantsVarsEquiv.symm (ψ.relabel (Sum.map b id))
  have hφI : {x : M | φ.Realize fun _ ↦ x}.Infinite := by
    rw [← infinite_coe_iff, ← φ.finOneRealizationsEquiv.infinite_iff, infinite_coe_iff]
    convert hψb with v
    simp only [Formula.Realize, Formula.relabel, ← BoundedFormula.realize_constantsVarsEquiv,
      _root_.Equiv.apply_symm_apply, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, φ]
    congr!
    ext (_ | _) <;> rfl
  have hφN :
      #({x : N | ((L.lhomWithConstantsMap ⇑eN).onFormula φ).Realize fun _ ↦ x}) = κ := by
    let rsN : Set N :=
      {x | ((L.lhomWithConstantsMap ⇑eN).onFormula φ).Realize fun _ ↦ x}
    change #rsN = κ
    refine le_antisymm ((mk_subtype_le rsN).trans_eq hNcard) ?_
    let φ' : F := ⟨φ, hφI⟩
    rw [← mk_out κ]
    /-
    The constants indexed by `(φ', i)` give `κ` realizations by `T₂`, and `T₃` makes the resulting
    map injective.
    -/
    have hφI' (i : I) : (L[[M]].con (φ', i) : N) ∈ rsN := by
      simp [T₂] at hNT₂
      simpa only [rsN, φ', Set.mem_ofPred_eq, subst, Sentence.Realize, Formula.Realize,
        BoundedFormula.realize_subst, Term.realize_constants, LHom.onFormula,
        LHom.realize_onBoundedFormula] using
        hNT₂ (subst φ' i) φ' i rfl
    let f : I → rsN := fun i ↦ ⟨(L[[M]].con (φ', i) : N), hφI' i⟩
    refine Cardinal.mk_le_of_injective (f := f) ?_
    intro i j hij
    simp only [T₃] at hNT₃
    have hNT₃' := (L[[M]].model_distinctConstantsTheory _).mp <| Theory.Model.mono hNT₃ <|
      subset_iUnion_of_subset φ' fun ⦃a⦄ h ↦ h
    simp only [Subtype.mk.injEq, f] at hij
    exact congrArg Prod.snd <| hNT₃' (by simp) (by simp) hij
  rw [← ((L.lhomWithConstantsMap ⇑eN).onFormula φ).finOneRealizationsEquiv.cardinal_eq]
    at hφN
  change #({x : Fin 1 → N | ψ.Realize (Sum.elim (eN ∘ b) x)}) = κ
  convert hφN with v
  simp only [(L.lhomWithConstantsMap ⇑eN).realize_onFormula, φ]
  simp only [Formula.Realize, Formula.relabel, ← BoundedFormula.realize_constantsVarsEquiv,
    _root_.Equiv.apply_symm_apply, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
    Fin.cast_refl, Function.comp_id, Fin.natAdd_zero]
  congr!
  ext (_ | _) <;> rfl

/-- An infinite theory in a countable language has a definably full model of every infinite
cardinality. -/
theorem exists_model_of_card_definably_full
    {κ : Cardinal.{w}} (hL : L.card ≤ ℵ₀)
    (hT : ∃ M : ModelType.{u, v, max u v} T, Infinite M) (hκ : ℵ₀ ≤ κ) :
    ∃ M : ModelType.{u, v, w} T, #M = κ ∧ L.DefinablyFull M := by
  obtain ⟨M₀, hM₀card⟩ :=
    Theory.exists_model_card_eq hT κ hκ
      ((lift_le_aleph0.mpr hL).trans (aleph0_le_lift.mpr hκ))
  let Stage := {M : ModelType.{u, v, w} T | #M = κ}
  have hLκ : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ :=
    (lift_le_aleph0.mpr hL).trans (aleph0_le_lift.mpr hκ)
  /- Apply the one-step construction to every model of cardinality `κ`. -/
  have hsucc :
      ∀ s : Stage, ∃ t : Stage, ∃ e : s.1 ↪ₑ[L] t.1,
        ∀ {β : Type w} (ψ : L.Formula (β ⊕ Fin 1)) (b : β → s.1),
          Set.Infinite {x : Fin 1 → s.1 | ψ.Realize (Sum.elim b x)} →
            #({x : Fin 1 → t.1 | ψ.Realize (Sum.elim (e ∘ b) x)}) = κ := by
    intro s
    obtain ⟨N, e, hNcard, hfull⟩ :=
      exists_elementaryExtension_card_eq_with_full_unary_realizations.{u, v, w, w}
        T s.1 s.2 hκ hLκ
    exact ⟨⟨N, hNcard⟩, e, hfull⟩
  choose next nextEmb nextFull using hsucc
  /-
  Iterating the chosen extensions along `ℕ` produces an elementary chain in which every unary
  formula over one stage is fully realized at the next stage.
  -/
  let stage : ℕ → Stage :=
    fun n ↦ Nat.rec ⟨M₀, hM₀card⟩ (fun _ s ↦ next s) n
  let M : ℕ → Type w := fun n ↦ (stage n).1
  letI chainStruct : ∀ n, L.Structure (M n) :=
    fun n ↦ (stage n).1.struc
  let f : ∀ n, M n ↪ₑ[L] M (n + 1) := fun n ↦ by
    simpa [M, stage, chainStruct] using nextEmb (stage n)
  let C := ElementaryChain.ofNatSucc M f
  haveI : Nonempty C.Limit := Nonempty.map (C.toLimit 0) M₀.instNonempty
  haveI : C.Limit ⊨ T := C.limit_models T ⟨0, M₀.is_model⟩
  /- The limit has cardinality `κ`, since all stages do and `κ` is infinite. -/
  have hCκ : #C.Limit = κ := by
    apply C.mk_limit_eq_of_forall_lift_mk_eq κ (le_of_eq_of_le rfl hκ)
    intro i
    cases i with
    | zero => simpa [C, M, f, ElementaryChain.ofNatSucc, stage]
    | succ n =>
      simp only [lift_uzero]
      exact (next (Nat.rec ⟨M₀, hM₀card⟩ (fun _ s ↦ next s) n)).2
  refine ⟨ModelType.of T C.Limit, hCκ, ?_⟩
  change L.DefinablyFull C.Limit
  letI : Infinite C.Limit := infinite_iff.mpr <| hκ.trans_eq hCκ.symm
  apply definablyFull_of_unary
  unfold UnaryDefinablyFull
  intro A X hAX hXI
  /-
  Replace the parameters defining `X` by a finite set, then move all of them into one common stage
  of the chain.
  -/
  rw [Definable₁, definable_iff_finitely_definable] at hAX
  rcases hAX with ⟨A₀, _, φ, hφ⟩
  obtain ⟨i, v, hiv⟩ := C.exists_finite_common_stage fun a : A₀ ↦ a.1
  let ψ : L.Formula (A₀ ⊕ Fin 1) := BoundedFormula.constantsVarsEquiv φ
  /-
  Elementarity transfers the infinitude of `X` back to the corresponding realization set at
  stage `i`.
  -/
  have hψI : {x : Fin 1 → (stage i).1 | ψ.Realize (Sum.elim v x)}.Infinite := by
    erw [← (C.toLimitElementary i).infinite_realizations_iff ψ v]
    change {x : Fin 1 → C.Limit | ψ.Realize (Sum.elim (C.toLimit i ∘ v) x)}.Infinite
    convert_to {x : Fin 1 → C.Limit | x 0 ∈ X}.Infinite using 1
    · rw [hφ]
      ext x
      change ψ.Realize (Sum.elim (C.toLimit i ∘ v) x) ↔ φ.Realize x
      simpa only [ψ, hiv] using!
        BoundedFormula.realize_constantsVarsEquiv (φ := φ) (v := x)
    · refine hXI.preimage (f := fun x : Fin 1 → C.Limit ↦ x 0) ?_
      simp only [Fin.isValue, range_eval, subset_univ]
  specialize nextFull (stage i) ψ v hψI
  /-
  The next stage contains `κ` realizations. Embedding them into the limit and identifying the
  resulting realization set with `X` gives the required lower cardinal bound.
  -/
  apply le_antisymm (mk_set_le X)
  let b : A₀ → C.Limit := C.toLimitElementary (i + 1) ∘ f i ∘ v
  calc
    #C.Limit = κ := hCκ
    _ = _ := nextFull.symm
    _ ≤ #↑{x : Fin 1 → C.Limit | ψ.Realize (Sum.elim b x)} := by
      simpa [lift_id, b] using!
        (C.toLimitElementary (i + 1)).mk_realizations_le ψ
          (f i ∘ v)
    _ = #{x : Fin 1 → C.Limit | x 0 ∈ X} := by
      rw [hφ]
      congr! with x
      simp only [Formula.Realize, SetLike.coe_sort_coe, ← BoundedFormula.realize_constantsVarsEquiv,
        ψ, b]
      congr! with a
      change C.toLimit (i + 1) (f i (v a)) = (a : C.Limit)
      simpa [← congrFun hiv a, C] using! C.toLimit_map (Nat.le_succ i) (v a)
    _ = _ :=
      Cardinal.mk_congr <| (Equiv.funUnique (Fin 1) C.Limit).subtypeEquiv fun _ ↦ by simp

end Theory

end Language

end FirstOrder
