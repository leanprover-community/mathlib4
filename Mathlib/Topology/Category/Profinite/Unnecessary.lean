import Mathlib.Topology.Category.Profinite.Nobeling

namespace LinearIndependent

variable {ι₁ : Type _} {ι₂ : Type _} (R : Type _) (M₁ : Type _) (M₂ : Type _)
  [Ring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

instance : Module R (M₁ × M₂) := inferInstance

def ProdInl : M₁ →ₗ[R] M₁ × M₂ :=
{ toFun := fun m ↦ (m, 0)
  map_add' := by
    intro x y
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply, Prod.smul_mk, smul_zero] }

def ProdInr : M₂ →ₗ[R] M₁ × M₂ :=
{ toFun := fun m ↦ (0, m)
  map_add' := by
    intro x y
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply, Prod.smul_mk, smul_zero] }

lemma injective_prodInl : LinearMap.ker (ProdInl R M₁ M₂) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y h
  dsimp [ProdInl] at h
  rw [Prod.ext_iff] at h
  exact h.1

lemma injective_prodInr : LinearMap.ker (ProdInr R M₁ M₂) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y h
  dsimp [ProdInr] at h
  rw [Prod.ext_iff] at h
  exact h.2

variable {R M₁ M₂} (v₁ : ι₁ → M₁) (v₂ : ι₂ → M₂)

lemma sum_prod : LinearIndependent R v₁ → LinearIndependent R v₂ →
    LinearIndependent R (Sum.elim ((ProdInl R M₁ M₂) ∘ v₁)
    ((ProdInr R M₁ M₂) ∘ v₂))  := by
  intro h₁ h₂
  apply sum_type
  · rwa [LinearMap.linearIndependent_iff (ProdInl R M₁ M₂) (injective_prodInl R M₁ M₂)]
  · rwa [LinearMap.linearIndependent_iff (ProdInr R M₁ M₂) (injective_prodInr R M₁ M₂)]
  · rw [Submodule.disjoint_def]
    intro f hf₁ hf₂
    rw [mem_span_set] at hf₁ hf₂
    obtain ⟨c₁, ⟨hc₁, hsum₁⟩⟩ := hf₁
    obtain ⟨c₂, ⟨hc₂, hsum₂⟩⟩ := hf₂
    ext
    <;> dsimp
    · rw [Prod.ext_iff] at hsum₂
      rw [← hsum₂.1]
      have : (Finsupp.sum c₂ fun mi r ↦ r • mi).fst =
          LinearMap.fst R M₁ M₂ (Finsupp.sum c₂ fun mi r ↦ r • mi) := rfl
      rw [this, map_finsupp_sum]
      rw [← @Finsupp.sum_zero _ _ _ _ _ c₂]
      apply Finsupp.sum_congr
      intro x hx
      dsimp
      obtain ⟨y,hy⟩ := hc₂ hx
      dsimp [ProdInr] at hy
      rw [← hy]
      simp only [smul_zero]
    · rw [Prod.ext_iff] at hsum₁
      rw [← hsum₁.2]
      have : (Finsupp.sum c₁ fun mi r ↦ r • mi).snd =
          LinearMap.snd R M₁ M₂ (Finsupp.sum c₁ fun mi r ↦ r • mi) := rfl
      rw [this, map_finsupp_sum]
      rw [← @Finsupp.sum_zero _ _ _ _ _ c₁]
      apply Finsupp.sum_congr
      intro x hx
      dsimp
      obtain ⟨y,hy⟩ := hc₁ hx
      dsimp [ProdInl] at hy
      rw [← hy]
      simp only [smul_zero]

end LinearIndependent

namespace ModuleCat

variable {I : Type _} {J : Type _} {R : Type _} [Ring R] {N P : ModuleCat R} {v : I → N} {w : J → P}

open CategoryTheory
open CategoryTheory.Limits

lemma hom_inv_id_apply (e : P ≅ N) (x : P) : e.inv (e.hom x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← e.hom_inv_id]
  rfl

lemma inv_hom_id_apply (e : P ≅ N) (x : N) : e.hom (e.inv x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← e.inv_hom_id]
  rfl

lemma iso_inv_inj (e : P ≅ N) : Function.Injective e.inv := by
  apply Function.HasLeftInverse.injective
  use e.hom
  intro a
  exact inv_hom_id_apply e a

lemma iso_hom_inj (e : P ≅ N) : Function.Injective e.hom := by
  apply Function.HasLeftInverse.injective
  use e.inv
  intro a
  exact hom_inv_id_apply e a

@[simp]
lemma biprod.inl_fst_apply (x : N) :
    (biprod.fst : N ⊞ P ⟶ N) ((biprod.inl : N ⟶ N ⊞ P) x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← biprod.inl_fst]
  rfl

@[simp]
lemma biprod.inl_snd_apply (x : N) :
    (biprod.snd : N ⊞ P ⟶ P) ((biprod.inl : N ⟶ N ⊞ P) x) = 0 := by
  rw [← forget_map]
  rw [← forget_map]
  rw [← types_comp_apply ((forget (ModuleCat R)).map _)
    ((forget (ModuleCat R)).map _) x]
  simp only [← CategoryTheory.Functor.map_comp]
  simp only [BinaryBicone.inl_snd, forget_map]
  rfl

@[simp]
lemma biprod.inr_fst_apply (x : P) :
    (biprod.fst : N ⊞ P ⟶ N) ((biprod.inr : P ⟶ N ⊞ P) x) = 0 := by
  rw [← forget_map]
  rw [← forget_map]
  rw [← types_comp_apply ((forget (ModuleCat R)).map _)
    ((forget (ModuleCat R)).map _) x]
  simp only [← CategoryTheory.Functor.map_comp]
  simp only [BinaryBicone.inr_fst, forget_map]
  rfl

@[simp]
lemma biprod.inr_snd_apply (x : P) :
    (biprod.snd : N ⊞ P ⟶ P) ((biprod.inr : P ⟶ N ⊞ P) x) = x := by
  apply Eq.symm _
  nth_rw 2 [← ModuleCat.id_apply x]
  rw [← biprod.inr_snd]
  rfl

section LinearIndependent

variable (hv : LinearIndependent R v) (hw : LinearIndependent R w)

lemma linearIndependent_sum_prod : LinearIndependent R
    (Sum.elim ((biprod.inl : N ⟶ N ⊞ P) ∘ v) ((biprod.inr : P ⟶ N ⊞ P) ∘ w)) := by
  have hN : (LinearIndependent.ProdInl R N P : N → N × P)  =
    (biprodIsoProd N P).hom ∘ (biprod.inl : N ⟶ N ⊞ P)
  · dsimp [LinearIndependent.ProdInl]
    ext n
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      nth_rw 1 [← ModuleCat.id_apply n,  ← biprod.inl_fst]
      rfl
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      rw [← forget_map biprod.snd]
      rw [← forget_map, ← types_comp_apply ((forget (ModuleCat R)).map _)
        ((forget (ModuleCat R)).map _) n]
      simp only [← CategoryTheory.Functor.map_comp]
      simp only [BinaryBicone.inl_snd, forget_map]
      rfl
  have hP : (LinearIndependent.ProdInr R N P : P → N × P) =
    (biprodIsoProd N P).hom ∘ (biprod.inr : P ⟶ N ⊞ P)
  · dsimp [LinearIndependent.ProdInl]
    ext n
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      rw [← forget_map biprod.fst]
      rw [← forget_map, ← types_comp_apply ((forget (ModuleCat R)).map _)
        ((forget (ModuleCat R)).map _) n]
      simp only [← CategoryTheory.Functor.map_comp]
      simp only [BinaryBicone.inr_fst, forget_map]
      rfl
    · simp only [Function.comp_apply]
      rw [biprodIsoProd_hom_apply]
      dsimp
      nth_rw 1 [← ModuleCat.id_apply n,  ← biprod.inr_snd]
      rfl
  have h := LinearIndependent.sum_prod v w hv hw
  rw [hN, hP, Function.comp.assoc, Function.comp.assoc, ← forget_map, ← forget_map,
     ← Sum.comp_elim ((forget (ModuleCat R)).map (biprodIsoProd N P).hom) _ _] at h
  have h_inj : LinearMap.ker (biprodIsoProd N P).hom = ⊥
  · rw [LinearMap.ker_eq_bot]
    exact iso_hom_inj (biprodIsoProd N P)
  rw [← LinearMap.linearIndependent_iff _ h_inj]
  exact h

end LinearIndependent

section Span

variable {M : ModuleCat R} {u : I ⊕ J → M} {f : N ⟶ M} {g : M ⟶ P}

lemma span_exact (hse : Exact f g) (huv : u ∘ Sum.inl = f ∘ v)
    (huw : g ∘ u ∘ Sum.inr = w) (hv : ⊤ ≤ Submodule.span R (Set.range v))
    (hw : ⊤ ≤ Submodule.span R (Set.range w)) : ⊤ ≤ Submodule.span R (Set.range u) := by
  intro m _
  have hgm : g m ∈ Submodule.span R (Set.range w) := hw Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  rw [← huw] at hm
  set m' : M := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j)) with hm'
  have hmm : g m = g m'
  · rw [← hm]
    dsimp
    rw [map_finsupp_sum]
    simp only [map_smul]
  have hsub : m - m' ∈ LinearMap.range f
  · rw [exact_iff] at hse
    rw [hse]
    simp only [LinearMap.mem_ker, map_sub]
    rw [hmm]
    simp only [sub_self]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ Submodule.span R (Set.range v) := hv Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsupp_sum] at hnm
  have hmmm : m = m - m' + m'
  · simp only [sub_add_cancel]
  rw [hmmm]
  rw [← hnm, hm']
  simp only [map_smul]
  have huv_apply : ∀ a, f (v a) = u (Sum.inl a)
  · intro a
    have : f (v a) = (f ∘ v) a := by rfl
    rw [this, ← huv]
    rfl
  have hn' : (Finsupp.sum cn fun a b ↦ b • f (v a)) = (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a))
  · congr
    ext a b
    rw [huv_apply]
  rw [hn']
  apply Submodule.add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

end Span

end ModuleCat

namespace Finsupp

open Finset Function

open BigOperators

variable {α M : Type _} [Zero M]

noncomputable
instance (r : Finset α) (p : α → Prop) : Fintype ({x | x ∈ r ∧ p x}) := by
  haveI : ∀ a, Decidable (p a) := fun a ↦ Classical.dec _
  have : Fintype {x : r // p x.val} := Subtype.fintype _
  let f : {x | x ∈ r ∧ p x} → {x : r // p x.val} := fun x ↦ ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
  have hf : f.Injective
  · intro a b hab
    rw [Subtype.ext_iff, Subtype.ext_iff] at hab
    exact Subtype.ext hab
  exact Fintype.ofInjective f hf

/--
`erase' s f` is the finitely supported function equal to `f` except at `a ∈ s` where it is
equal to `0`.
-/
noncomputable
def erase' (s : Set α) (f : α →₀ M) : α →₀ M where
  support := {x | x ∈ f.support ∧ x ∉ s}.toFinset
  toFun a :=
    haveI : Decidable (a ∈ s) := Classical.dec _
    if a ∈ s then 0 else f a
  mem_support_toFun a := by
    classical
    simp only [mem_support_iff, ne_eq, Set.mem_toFinset, Set.mem_setOf_eq, ite_eq_left_iff, not_forall,
      exists_prop]
    rw [and_comm]

end Finsupp

namespace NobelingProof

variable (I : Type u) [LinearOrder I] [IsWellOrder I (·<·)] (C : Set ((WithTop I) → Bool))

def Q' (o : Ordinal) : Prop :=
o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop) →
  ∀ C, IsClosed C → Support C ⊆ {j : WithTop I | ord I j < o} →
  ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval C))

variable {I}

lemma GoodProducts.spanEmpty :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval (∅ : Set (WithTop I → Bool)))) := by
  rw [top_le_iff]
  rw [Submodule.eq_bot_of_subsingleton ⊤]
  rw [Submodule.eq_bot_of_subsingleton (Submodule.span ℤ (Set.range (eval ∅)))]

noncomputable
def el (o : Ordinal) : WithTop I := if h : o < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)
  then Ordinal.enum _ o h else ⊤

lemma zeroLTTop : 0 < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop) := by
  rw [Ordinal.pos_iff_ne_zero]
  intro h
  simp only [Ordinal.type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty] at h

noncomputable
def ezero: Products (WithTop I) := ⟨[el 0], by simp only [List.chain'_singleton]⟩

lemma elZeroIsBot (i : WithTop I) : el 0 ≤ i := by
  have h₁ : 0 < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)
  · rw [Ordinal.pos_iff_ne_zero]
    intro h
    rw [Ordinal.type_eq_zero_iff_isEmpty] at h
    simp only [not_isEmpty_of_nonempty] at h
  have : el 0 = Ordinal.enum ((·<·) : WithTop I → WithTop I → Prop) 0 h₁
  · dsimp [el]
    rw [dite_eq_iff]
    left
    use h₁
  · rw [this]
    have h := Ordinal.enum_zero_le h₁ i
    simp only [not_lt] at h
    assumption

lemma leEzeroSingleton : { m : Products (WithTop I) | m < ezero} = {⟨[], List.chain'_nil⟩ } := by
  ext ⟨m, hm⟩
  refine' ⟨_,_⟩
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [ltIffLex]
    dsimp [ezero]
    intro h
    apply Subtype.eq
    dsimp
    induction m with
    | nil => rfl
    | cons i m _ =>
      simp
      by_cases hi : el 0 = i
      · rw [hi, List.Lex.cons_iff] at h
        exact List.Lex.not_nil_right _ _ h
      · have : List.Lex (·<·) [el 0] [i]
        · rw [← List.Lex.singleton_iff]
          rw [lt_iff_le_and_ne]
          exact ⟨elZeroIsBot i, hi⟩
        · have ht : List.Lex (·<·) (i :: m) [i] := transLex _ _ _ h this
          rw [List.Lex.cons_iff] at ht
          exact List.Lex.not_nil_right _ _ ht
  · simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [ltIffLex]
    dsimp [ezero]
    intro h
    cases h
    exact List.nil_lt_cons _ _

lemma GoodProducts.spanSingleton :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval ({fun _ ↦ false} : Set (WithTop I → Bool)))) := by
  have hpe : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil} ⊆
    (Set.range (eval ({fun _ ↦ false} : Set (WithTop I → Bool))))
  · dsimp [eval]
    simp only [Set.image_singleton, Set.singleton_subset_iff, Set.mem_range,
      Subtype.exists, exists_prop]
    use enil
    exact ⟨nilIsGood, rfl⟩
  refine' le_trans _ (Submodule.span_mono hpe)
  rw [nilSpanTop]

lemma chain'_cons_of_chain'_and_chain'_cons {l m : List (WithTop I)} {a : WithTop I} (hml : m < l)
    (hl : (a::l).Chain' (·>·)) (hm : m.Chain' (·>·)) : (a::m).Chain' (·>·) := by
  induction hml with
  | nil =>
    · simp only [List.chain'_singleton]
  | cons _ _ =>
    · simp only [List.chain'_cons]
      simp only [List.chain'_cons] at hl
      exact ⟨hl.1, by assumption⟩
  | rel h =>
    · simp only [gt_iff_lt, List.chain'_cons]
      simp only [gt_iff_lt, List.chain'_cons]  at hl
      exact ⟨lt_trans h hl.1, hm⟩

lemma Products.isGood_cons {l : List (WithTop I)} {a : WithTop I}
    (hla : (a::l).Chain' (·>·)) : isGood C ⟨a::l,hla⟩ →
    isGood C ⟨l,List.Chain'.sublist hla (List.tail_sublist (a::l))⟩ := by
  rw [← not_imp_not]
  intro h
  dsimp [isGood] at *
  simp only [not_not] at *
  rw [evalCons]
  rw [mem_span_set] at h
  obtain ⟨c, ⟨hc, hsum⟩⟩ := h
  rw [← hsum, Finsupp.mul_sum]
  simp_rw [mul_smul_comm]
  apply Submodule.finsupp_sum_mem
  intro f hf
  apply Submodule.smul_mem
  simp only [← Finsupp.mem_support_iff] at hf
  have := hc hf
  obtain ⟨⟨m,cm⟩,hm⟩ := this
  have hma : List.Chain' (·>·) (a :: m) := chain'_cons_of_chain'_and_chain'_cons hm.1 hla cm
  rw [← hm.2, ← evalCons C hma]
  apply Submodule.subset_span
  use ⟨a :: m, hma⟩
  refine' ⟨_,rfl⟩
  simp only [Set.mem_setOf_eq]
  apply List.Lex.cons
  exact hm.1

lemma DirectedSubmodules (o : Ordinal) : Directed (· ≤ ·) (fun e ↦
    Submodule.span ℤ (ModProducts.smaller C e.val) :
    {o' // o' < o} → Submodule ℤ (LocallyConstant { i // i ∈ C } ℤ)) := by
  let f : {o' // o' < o} → Set (LocallyConstant { i // i ∈ C } ℤ) :=
    fun e ↦ ModProducts.smaller C e.val
  let g : Set (LocallyConstant {i // i ∈ C} ℤ) → Submodule ℤ (LocallyConstant {i // i ∈ C} ℤ) :=
    fun s ↦ Submodule.span ℤ s
  suffices : Directed (· ≤ ·) (g ∘ f)
  · exact this
  have : Directed (· ⊆ ·) f := DirectedS C o
  refine' Directed.mono_comp _ _ this
  intro _ _ h
  exact Submodule.span_mono h

instance nonempty_downset {o : Ordinal} (ho : Ordinal.IsLimit o) : Nonempty {o' // o' < o} := by
  use 0
  simp only [Ordinal.pos_iff_ne_zero]
  exact ho.1

section JointlySurjective

open CategoryTheory
open CategoryTheory.Limits

lemma IzeroLTTop : 0 < Ordinal.type ((·<·) : (WithTop I) → (WithTop I) → Prop) := by
  rw [Ordinal.pos_iff_ne_zero, Ordinal.type_ne_zero_iff_nonempty]
  exact inferInstance

instance ICofiltered {o : Ordinal} (ho : o.IsLimit) :
    IsCofiltered {i : WithTop I // ord I i < o}ᵒᵖ :=
{ Nonempty := by
    use Ordinal.enum _ 0 IzeroLTTop
    dsimp [ord]
    simp only [Ordinal.typein_enum]
    rw [Ordinal.pos_iff_ne_zero]
    exact ho.1
  cone_objs := by
    intro i j
    cases (le_total i.unop j.unop)
    · use j
      use (homOfLE (by assumption : i.unop ≤ j.unop)).op
      use (homOfLE (le_refl j.unop)).op
      trivial
    · use i
      use (homOfLE (le_refl i.unop)).op
      use (homOfLE (by assumption : j.unop ≤ i.unop)).op
      trivial
  cone_maps := by
    intro i j f g
    suffices : f = g
    · rw [this]
      use i
      use 𝟙 i
    simp only [eq_iff_true_of_subsingleton]  }

instance ResCompact (o : Ordinal) (hC : IsClosed C) : CompactSpace (Res C o) := by
  rw [← isCompact_iff_compactSpace]
  exact (isClosed_Res C o hC).isCompact

lemma ResOnSubsetsId (o : Ordinal) : ResOnSubsets C (le_refl o) = id := by
  ext ⟨f,hf⟩ i
  dsimp [ResOnSubsets, ProjOrd]
  split_ifs
  · rfl
  · obtain ⟨g, ⟨_,hg⟩⟩ := hf
    dsimp [ProjOrd] at hg
    rw [← congr_fun hg i]
    split_ifs
    rfl

lemma ResOnSubsetsComp {o₁ o₂ o₃ : Ordinal} (h₁₂ : o₁ ≤ o₂) (h₂₃ : o₂ ≤ o₃) :
    ResOnSubsets C h₁₂ ∘ ResOnSubsets C h₂₃ = ResOnSubsets C (le_trans h₁₂ h₂₃) := by
  ext ⟨f,hf⟩ i
  dsimp [ResOnSubsets, ProjOrd]
  split_ifs with h₁ h₂
  · rfl
  · obtain ⟨g, ⟨_,hg⟩⟩ := hf
    dsimp [ProjOrd] at hg
    rw [← congr_fun hg i]
    split_ifs
    · exfalso
      apply h₂
      exact lt_of_lt_of_le h₁ h₁₂
    · rfl
  · rfl

lemma ordILE {i j : WithTop I} (h : i ≤ j) : ord I i ≤ ord I j := by
  dsimp [ord]
  rwa [Ordinal.typein_le_typein, not_lt]

noncomputable
def OrdToProfinite (o : Ordinal) (hC : IsClosed C) :
    {i : WithTop I // ord I i < o}ᵒᵖ ⥤ Profinite.{u} :=
{ obj := fun i ↦ @Profinite.of (Res C (ord I i.unop)) _ (ResCompact _ _ hC) _ _
  map := fun h ↦ ⟨ResOnSubsets C (ordILE (leOfHom h.unop)), (continuous_ResOnSubsets _ _)⟩
  map_id := by
    intro e
    dsimp
    simp_rw [ResOnSubsetsId]
    rfl
  map_comp := by
    intro e₁ e₂ e₃ h₁₂ h₂₃
    dsimp
    congr
    simp only [ContinuousMap.coe_mk]
    rw [ResOnSubsetsComp] }

noncomputable
def OrdCone (o : Ordinal) (hC : IsClosed C) :
    Cone (OrdToProfinite C o hC) :=
{ pt := @Profinite.of {i // i ∈ C} _ (CCompact C hC) _ _
  π :=
  { app := fun i ↦ ⟨ResOnSubset C (ord I i.unop), continuous_ResOnSubset _ _⟩
    naturality := by
      intro e₁ e₂ h
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      congr
      simp only [ContinuousMap.coe_mk]
      dsimp [OrdToProfinite]
      rw [resOnSubsets_eq] } }

lemma succ_le_type {o o' : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop)) (ho' : o' < o) :
    Order.succ o' < Ordinal.type (·<· : WithTop I → WithTop I → Prop) :=
lt_of_lt_of_le (ho.2 o' ho') hto

noncomputable
def ISucc {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    {i : WithTop I} (hi : ord I i < o) : {i // ord I i < o} :=
{ val := Ordinal.enum (·<·) (Order.succ (ord I i)) (succ_le_type ho hto hi)
  property := by
    dsimp [ord] at *
    simp only [Ordinal.typein_enum]
    exact ho.2 _ hi }

lemma ord_lt_succ {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    {i : WithTop I} (hi : ord I i < o) : ord I i < ord I (ISucc ho hto hi).val := by
  dsimp [ord, ISucc]
  simp only [Ordinal.typein_enum, Order.lt_succ_iff_not_isMax, gt_iff_lt, not_isMax,
    not_false_eq_true]

noncomputable
def OrdConeIsLimitLiftFunAux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (s : Cone (OrdToProfinite C o hC)) : s.pt → ((WithTop I) → Bool) :=
fun x i ↦ if h : ord I i < o then (s.π.app (Opposite.op (ISucc ho hto h)) x).val i
  else false

lemma le_of_leOrd {o : Ordinal} {i j : {i // ord I i < o}} (h : ord I i.val ≤ ord I j.val) :
    i ≤ j := by
  dsimp [ord] at h
  simp only [Ordinal.typein_le_typein, not_lt] at h
  exact h

def HomOfLEOrd {o : Ordinal} {i j : {i // ord I i < o}} (h : ord I i.val ≤ ord I j.val) : i ⟶ j :=
homOfLE (le_of_leOrd h)

lemma ordConeIsLimitLiftFunAux_mem {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) (x : s.pt) :
    OrdConeIsLimitLiftFunAux C ho hto hC s x ∈ C := by
  dsimp [OrdConeIsLimitLiftFunAux]
  have : C = Res C o := supportResEq C o hsC
  rw [Set.ext_iff] at this
  rw [this]
  dsimp [Res, ProjOrd]
  simp only [Set.mem_image]
  have hs := fun i ↦ (s.π.app i x).prop
  dsimp [Res] at hs
  simp only [Set.mem_image] at hs
  let f' := fun i ↦ (hs (Opposite.op i)).choose
  have hf' := fun i ↦ (hs (Opposite.op i)).choose_spec
  let f : WithTop I → Bool :=
    fun i ↦ if h : ord I i < o then f' (ISucc ho hto h) i else false
  use f
  refine' ⟨_,_⟩
  · let S : {i // ord I i < o} → Set {i // ord I i < o} := fun i ↦ {j | ord I i.val ≤ ord I j.val}
    have h0 : ord I (Ordinal.enum _ 0 IzeroLTTop) < o
    · dsimp [ord]
      simp only [Ordinal.typein_enum, Ordinal.pos_iff_ne_zero]
      exact ho.1
    let b : Filter {i // ord I i < o} := Filter.generate (Set.range S)
    have hb : b.NeBot
    · rw [Filter.generate_neBot_iff]
      intro t hts ht
      simp only [Set.nonempty_sInter]
      rw [Set.subset_range_iff_exists_image_eq] at hts
      obtain ⟨r,hr⟩ := hts
      rw [← hr, Set.finite_image_iff] at ht
      · by_cases hre : Set.Nonempty r
        · have hmax := Set.exists_max_image r id ht hre
          obtain ⟨a, ha⟩ := hmax
          use a
          intro w hw
          rw [← hr] at hw
          obtain ⟨w',hw⟩ := hw
          rw [← hw.2]
          dsimp [ord]
          simp only [Ordinal.typein_le_typein, Subtype.coe_lt_coe, not_lt]
          exact ha.2 w' hw.1
        · use ⟨(Ordinal.enum _ 0 IzeroLTTop), h0⟩
          intro w hw
          rw [Set.not_nonempty_iff_eq_empty] at hre
          rw [hre] at hr
          simp only [ge_iff_le, Set.image_empty] at hr
          rw [← hr] at hw
          exfalso
          exact Set.not_mem_empty w hw
      · intro i _ j _ hsij
        dsimp at hsij
        rw [Set.ext_iff] at hsij
        have hsi := hsij i
        have hsj := hsij j
        simp at hsi hsj
        have hij := le_antisymm hsj hsi
        dsimp [ord] at hij
        simp [Ordinal.typein_inj] at hij
        exact Subtype.ext hij
    have hf : Filter.Tendsto f' b (nhds f)
    · rw [nhds_pi, Filter.tendsto_pi]
      intro i
      rw [Filter.tendsto_def]
      intro U hU
      have hf := mem_of_mem_nhds hU
      dsimp at hf
      split_ifs at hf with h
      · dsimp
        rw [Filter.mem_generate_iff]
        simp only [exists_and_left, exists_prop]
        use {S (ISucc ho hto h)}
        refine' ⟨Set.finite_singleton _,_,_⟩
        · intro W hW
          use (ISucc ho hto h)
          simp only [Set.mem_singleton_iff] at hW
          rw [hW]
        · simp only [Set.sInter_singleton]
          intro j hj
          simp only [Set.mem_preimage]
          simp only [Set.mem_setOf_eq] at hj
          suffices : f' j i ∈ U
          · exact this
          suffices : f' (ISucc ho hto h) i = f' j i
          · rw [← this]
            exact hf
          suffices : ∀ y,
            ((y ∈ C ∧ (ProjOrd (ord I (ISucc ho hto h).val) y =
            ((forget Profinite).map (s.π.app (Opposite.op (ISucc ho hto h))) x).val)) →
            y i = f' j i)
          · specialize this (f' (ISucc ho hto h))
            exact this (hf' (ISucc ho hto h))
          rintro y ⟨_, hy⟩
          suffices : ∀ z,
            ((z ∈ C ∧ (ProjOrd (ord I j.val) z =
            ((forget Profinite).map (s.π.app (Opposite.op j)) x).val)) →
            y i = z i)
          · specialize this (f' j)
            exact this (hf' j)
          rintro z ⟨_, hz⟩
          have hy' := congr_fun hy i
          have hz' := congr_fun hz i
          dsimp [ProjOrd] at hy' hz'
          split_ifs at hy' hz' with h₁ h₂
          · rw [hy', hz']
            have hsw := Cone.w s (HomOfLEOrd hj).op
            rw [← hsw]
            dsimp [OrdToProfinite, ResOnSubsets, ProjOrd]
            simp only [FunctorToTypes.map_comp_apply, Profinite.forget_ContinuousMap_mk,
              ite_eq_left_iff, not_lt]
            intro hord
            exfalso
            simp only [← not_lt] at hord
            exact hord (ord_lt_succ _ _ _)
          · exfalso
            apply h₂
            exact lt_of_lt_of_le (ord_lt_succ _ _ _) hj
          · exfalso
            exact h₁ (ord_lt_succ _ _ _)
          · exfalso
            exact h₁ (ord_lt_succ _ _ _)
      · dsimp
        rw [Filter.mem_generate_iff]
        simp only [exists_and_left, exists_prop]
        use {S ⟨(Ordinal.enum _ 0 IzeroLTTop), h0⟩}
        refine' ⟨Set.finite_singleton _,_,_⟩
        · intro W hW
          use ⟨(Ordinal.enum _ 0 IzeroLTTop), h0⟩
          simp only [Set.mem_singleton_iff] at hW
          rw [hW]
        · simp only [Set.sInter_singleton]
          intro j hj
          simp only [Set.mem_preimage]
          simp only [Set.mem_setOf_eq] at hj
          suffices : f' j i ∈ U
          · exact this
          suffices : f' j i = false
          · rw [this]
            exact hf
          suffices : ∀ z,
            ((z ∈ C ∧ (ProjOrd (ord I j.val) z =
            ((forget Profinite).map (s.π.app (Opposite.op j)) x).val)) →
            z i = false)
          · specialize this (f' j)
            exact this (hf' j)
          rintro z ⟨hzC, hz⟩
          have hz' := congr_fun hz i
          dsimp [ProjOrd] at hz'
          split_ifs at hz' with h₁
          · exfalso
            apply h
            exact lt_trans h₁ j.prop
          · dsimp [Support] at hsC
            simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
            specialize hsC i z hzC
            rw [← not_imp_not] at hsC
            simp only [Bool.not_eq_true] at hsC
            exact hsC h
    exact IsClosed.mem_of_tendsto hC hf (Filter.eventually_of_forall (fun i ↦ (hf' i).1))
  · ext i
    by_cases h : ord I i < o
    · rw [ite_eq_iff]
      left
      refine' ⟨h,_⟩
      apply Eq.symm
      rw [dite_eq_iff]
      left
      use h
      rw [← (hf' (ISucc ho hto h)).2]
      dsimp [ProjOrd]
      split_ifs with h'
      · rfl
      · exfalso
        exact h' (ord_lt_succ _ _ _)
    · rw [ite_eq_iff]
      right
      refine' ⟨h,_⟩
      apply Eq.symm
      rw [dite_eq_iff]
      right
      use h

noncomputable
def OrdConeIsLimitLiftFun {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) : s.pt → {i // i ∈ C} :=
  fun x ↦ ⟨OrdConeIsLimitLiftFunAux C ho hto hC s x, ordConeIsLimitLiftFunAux_mem _ _ _ _ hsC _ x⟩

lemma continuous_ordConeIsLimitLiftFun {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) : Continuous (OrdConeIsLimitLiftFun C ho hto hC hsC s) := by
  rw [continuous_induced_rng]
  have : (Subtype.val ∘ OrdConeIsLimitLiftFun C ho hto hC hsC s) =
      OrdConeIsLimitLiftFunAux C ho hto hC s
  · ext
    rfl
  rw [this]
  refine' continuous_pi _
  intro i
  dsimp [OrdConeIsLimitLiftFunAux]
  split_ifs with h
  · refine' Continuous.comp (continuous_apply _) _
    exact Continuous.comp continuous_subtype_val
      (s.π.app (Opposite.op (ISucc ho hto h))).continuous
  · exact continuous_const

noncomputable
def OrdConeIsLimitLift {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s : Cone (OrdToProfinite C o hC)) : s.pt ⟶ (OrdCone C o hC).pt :=
  ⟨OrdConeIsLimitLiftFun C ho hto hC hsC s, continuous_ordConeIsLimitLiftFun C ho hto hC hsC s⟩

lemma OrdToProfinite_aux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (s: Cone (OrdToProfinite C o hC))
    (x : s.pt) (i j : WithTop I) (hi : ord I i < o)
    (hj : ord I j < o)
    (hs : ord I (ISucc ho hto hj) ≤ ord I i) :
    ((s.π.app { unop := { val := i, property := hi } } ≫ (OrdToProfinite C o hC).map
    (@HomOfLEOrd I _ _ o (ISucc ho hto hj) ⟨i,hi⟩
    hs).op).1 x).1 j =
    ((s.π.app { unop := { val := i, property := hi } }).1 x).1 j := by
  dsimp [OrdToProfinite]
  have : (ResOnSubsets C hs ((s.π.app { unop := { val := i, property := hi } }).1 x)).val j =
      ((s.π.app { unop := { val := i, property := hi } }).1 x).val j
  · dsimp [ResOnSubsets, ProjOrd]
    split_ifs with hjs
    · rfl
    · exfalso
      exact hjs (ord_lt_succ _ _ _)
  exact this

lemma OrdConeIsLimitLiftFun_aux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s: Cone (OrdToProfinite C o hC))
    (x : s.pt) (i j : WithTop I) (hi : ord I i < o) (h : ord I j < ord I i) :
    ((OrdConeIsLimitLiftFun C ho hto hC hsC s) x).val j =
    ((s.π.app { unop := { val := i, property := hi } }).1 x).1 j := by
  dsimp [OrdConeIsLimitLiftFun, OrdConeIsLimitLiftFunAux]
  split_ifs with hj
  · have hs : ord I (ISucc ho hto hj) ≤ ord I i
    · dsimp [ord, ISucc]
      dsimp [ord] at h
      simp only [Ordinal.typein_lt_typein] at h
      simpa only [Ordinal.typein_enum, Order.succ_le_iff, Ordinal.typein_lt_typein]
    let f := (@HomOfLEOrd I _ _ o (ISucc ho hto hj) ⟨i,hi⟩ hs)
    have := Cone.w s f.op
    rw [← this]
    exact OrdToProfinite_aux C ho hto hC s x i j hi hj hs
  · exfalso
    exact hj (lt_trans h hi)

lemma OrdConeIsLimit_fac_aux {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (s: Cone (OrdToProfinite C o hC))
    (x : s.pt) (i : WithTop I) (hi : ord I i < o) :
    (ResOnSubset C (ord I i)) ((OrdConeIsLimitLift C ho hto hC hsC s) x) =
    (s.π.app { unop := { val := i, property := hi } }) x := by
  ext j
  dsimp [ResOnSubset, ProjOrd]
  split_ifs with h
  · dsimp [OrdConeIsLimitLift]
    exact OrdConeIsLimitLiftFun_aux C ho hto hC hsC s x i j hi h
  · have hR := (s.π.app ⟨i,hi⟩ x).prop
    dsimp [Res] at hR
    obtain ⟨g,⟨_,hg⟩⟩ := hR
    dsimp [ProjOrd] at hg
    have hgj := congr_fun hg j
    split_ifs at hgj
    rw [hgj]

lemma OrdConeIsLimit {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o }) : IsLimit (OrdCone C o hC) :=
{ lift := fun s ↦ OrdConeIsLimitLift C ho hto hC hsC s
  fac := by
    rintro s ⟨⟨i,hi⟩⟩
    ext x
    simp only [comp_apply]
    dsimp [OrdCone]
    exact OrdConeIsLimit_fac_aux C ho hto hC hsC s x i hi
  uniq := by
    rintro s ⟨m,hm⟩ h
    dsimp [OrdCone] at m
    congr
    dsimp [OrdConeIsLimitLift, OrdConeIsLimitLiftFun, OrdConeIsLimitLiftFunAux]
    ext x
    apply Subtype.ext_val
    ext i
    dsimp
    split_ifs with hi
    · rw [← h (Opposite.op (ISucc ho hto hi) : {i // ord I i < o}ᵒᵖ)]
      simp only [FunctorToTypes.map_comp_apply]
      dsimp [OrdCone]
      have : (ResOnSubset C (ord I (ISucc ho hto hi)) (m x)).val i = (m x).val i
      · dsimp [ResOnSubset, ProjOrd]
        split_ifs with hi'
        · rfl
        · exfalso
          exact hi' (ord_lt_succ _ _ _)
      exact this.symm
    · have := (m x).prop
      dsimp [Support] at hsC
      simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
      specialize hsC i (m x).val this
      rw [← not_imp_not] at hsC
      simp only [Bool.not_eq_true] at hsC
      exact hsC hi }

lemma comapJointlySurjectiveAuxSubtype {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ (e : {o' // o' < o})
    (g : LocallyConstant {i // i ∈ Res C e.val} ℤ), g.comap (ResOnSubset C e.val) = f := by
  obtain ⟨i, g, h⟩ := @Profinite.exists_locallyConstant {i : WithTop I // ord I i < o}ᵒᵖ _
    (ICofiltered ho) _ (OrdCone C o hC) _
    (OrdConeIsLimit C ho hto hC hsC) f
  use ⟨ord I i.unop.val, i.unop.prop⟩
  use g
  rw [h]
  congr

lemma comapJointlySurjective {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ o', o' < o ∧
    ∃ (g : LocallyConstant {i // i ∈ Res C o'} ℤ), g.comap (ResOnSubset C o') = f := by
  obtain ⟨e, g, h⟩ := comapJointlySurjectiveAuxSubtype C ho hto hC hsC f
  exact ⟨e.val, e.prop,⟨g,h⟩⟩

lemma comapLinearJointlySurjective {o : Ordinal} (ho : o.IsLimit)
    (hto : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop))
    (hC : IsClosed C)
    (hsC : Support C ⊆ { j | ord I j < o })
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ o', o' < o ∧
    ∃ (g : LocallyConstant {i // i ∈ Res C o'} ℤ),
    (LocallyConstant.comapLinear (ResOnSubset C o') (continuous_ResOnSubset _ _) :
    LocallyConstant {i // i ∈ Res C o'} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) g = f :=
  comapJointlySurjective C ho hto hC hsC f

end JointlySurjective

section Successor

variable (hC : IsClosed C) {o : Ordinal}
  (ho : o < Ordinal.type (·<· : WithTop I → WithTop I → Prop))

def rC1' : Set {i // i ∈ C} := {f | f.val ∈ Res (C1 C ho) o}

lemma rC1_subset_C0 : rC1' C ho ⊆ C0' C ho := by
  intro x hx
  refine ⟨Subtype.mem x, ?_⟩
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2]
  dsimp [ProjOrd]
  simp only [ite_eq_right_iff]
  intro h
  dsimp [ord, term] at h
  simp only [Ordinal.typein_enum, lt_self_iff_false] at h

lemma isClosed_rC1' : IsClosed (rC1' C ho) := by
  have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
    (isClosed_Res _ o (isClosed_C1 C hC ho))
  suffices h : rC1' C ho = Subtype.val ⁻¹' (Res (C1 C ho) o)
  · rw [h]
    exact this
  rfl

end Successor

def R (I : Type u) [LinearOrder I] [IsWellOrder I (·<·)] (o : Ordinal) : Prop := Q' I o ∧ P' I o

lemma R_iff_QP (I : Type u) [LinearOrder I] [IsWellOrder I (·<·)] (o : Ordinal) :
  R I o ↔ Q' I o ∧ P' I o := Iff.rfl

lemma GoodProducts.Q0 : Q' I 0 := by
  dsimp [Q']
  intro _ C _ hsC
  dsimp [Support] at hsC
  have : C ⊆ {(fun _ ↦ false)}
  · intro c hc
    simp
    ext x
    simp at hsC
    specialize hsC x c hc
    rw [Bool.eq_false_iff]
    intro ht
    apply Ordinal.not_lt_zero (ord I x)
    exact hsC ht
  rw [Set.subset_singleton_iff_eq] at this
  rcases this
  · subst C
    exact spanEmpty
  · subst C
    exact spanSingleton

lemma GoodProducts.Qmono (o o' : Ordinal) (h : o' < o)
    (ho : o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop)) : Q' I o → Q' I o' := by
  intro hQ
  dsimp [Q'] at *
  intro _ C hC hsC
  specialize hQ ho C hC
  apply hQ
  refine' subset_trans hsC _
  intro j hj
  simp only [Set.mem_setOf_eq] at hj
  exact lt_trans hj h


lemma GoodProducts.Qlimit :
    ∀ (o : Ordinal), Ordinal.IsLimit o → (∀ (o' : Ordinal), o' < o → Q' I o') → Q' I o := by
  intro o ho h
  dsimp [Q'] at *
  intro hto C hC hsC
  have hr : ∀ (s : Set (WithTop I → Bool)), Set.range (eval s) = ModProducts s
  · intro
    rfl
  rw [hr C, ModProducts.union C ho hsC, Submodule.span_iUnion]
  intro f _
  haveI : Nonempty {o' // o' < o} := nonempty_downset ho
  simp only [Submodule.mem_iSup_of_directed _ (DirectedSubmodules C o)]
  dsimp [ModProducts.smaller]
  simp only [Submodule.span_image, Submodule.mem_map, Subtype.exists]
  obtain ⟨o',⟨ho',⟨g, hg⟩⟩⟩ := comapLinearJointlySurjective C ho hto hC hsC f
  use o'
  use ho'
  use g
  refine' ⟨_,hg⟩
  specialize h o' ho' (le_of_lt (lt_of_lt_of_le ho' hto)) (Res C o') (isClosed_Res C o' hC)
    (support_Res_le_o C o')
  rw [hr (Res C o'), top_le_iff] at h
  rw [h]
  exact Submodule.mem_top

end NobelingProof
