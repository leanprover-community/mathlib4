import Mathlib.Algebra.Operad.Clone
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.TensorProduct.Pi

universe u v

variable {α β t : Type*}

open BigOperators

--Defining conjunctive and disjunctive functions
section conjunctive

variable [Min α] [Max α] [Min β] [Max β]

def Conjunctive (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f (min a b) = min (f a) (f b)

@[simp]
theorem conjunctive_min {f : α → β} (a b : α) (h : Conjunctive f) :
  min (f a) (f b) = f (min a b) :=
    Eq.symm (@h a b)

def Disjunctive (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f (max a b) = max (f a) (f b)

@[simp]
theorem disjunctive_max {f : α → β} (a b : α) (h : Disjunctive f) :
  max (f a) (f b) = f (max a b) :=
    Eq.symm (@h a b)

end conjunctive

/- The standard notion of superposition in a clone, for functions. Usually stated for `Fin n`
 and `Fin m` indexed lists of arguments, here we generalize to arbitrary index types α and β.-/
@[reducible]
def function_superpose (a : (α → t) → t) (b : α → (β → t) → t) : (β → t) → t :=
  fun ts ↦ a (Function.swap b ts)

/- The k-indexed family of "k-argument functions from T to T" forms a clone. -/
instance Func_Clone {t : Type*} : Clone (fun k ↦ (Fin k → t) → t) where
  superpose := function_superpose
  proj := fun _ k ts ↦ ts k
  one := fun ts ↦ ts 0

  one_proj := rfl
  superpose_assoc := fun _ _ _ ↦ rfl
  proj_left := fun _ _ ↦ rfl
  proj_right := fun _ ↦ by rfl


section property_clones

/- A function property `p`, applicable to `k` argument functions `t^k → t`, is "superposable"
   iff it is closed under superposition -- `function_superpose`. -/
def superposable_function_property (p : {k : ℕ} → ((Fin k → t) → t) → Prop) : Prop
  := ∀ {n m : ℕ} (a : Subtype (@p (k := n))) (b : Fin n → Subtype (@p (k := m))),
    p (function_superpose a.1 (Subtype.val ∘ b))

/- A function property `p`, applicable to `k` argument functions `t^k → t`, is "projectable"
   if it holds for all projector functions π_k^i. -/
def projectable_function_property (p : {k : ℕ} → ((Fin k → t) → t) → Prop) : Prop
  := ∀ (n : ℕ) (k : Fin n), p (fun ts ↦ ts k)

/- A function property is clonal iff it is both superposable and projectable. -/
def clonal_function_property (t : Type*) (p : {k : ℕ} → ((Fin k → t) → t) → Prop) : Prop :=
  (superposable_function_property p) ∧ (projectable_function_property p)

/- The intersection of two clonal properties is again a clonal property. -/
theorem clonal_property_intersect {p1 p2} (h₁ : clonal_function_property t p1)
    (h₂ : clonal_function_property t p2) : clonal_function_property t (fun ts ↦ p1 ts ∧ p2 ts) :=
  -- Original, ungolfed, as I wrote it:
  -- ⟨fun {n m} a b ↦ by
  --   constructor
  --   · set a' : Subtype p1 := ⟨a.val, a.prop.left⟩ with ha'
  --     set b' : Fin n → Subtype p1 := fun i ↦ ⟨(b i).val, (b i).prop.left⟩ with hb'
  --     have := h₁.left a' b'
  --     rw [ha', hb'] at this
  --     dsimp [Subtype.val] at this
  --     exact this
  --   · set a' : Subtype p2 := ⟨a.val, a.prop.right⟩ with ha'
  --     set b' : Fin n → Subtype p2 := fun i ↦ ⟨(b i).val, (b i).prop.right⟩ with hb'
  --     have := h₂.left a' b'
  --     rw [ha', hb'] at this
  --     dsimp [Subtype.val] at this
  --     exact this
  -- , fun n k ↦ by
  --   constructor
  --   · have := h₁.right n k
  --     dsimp [Subtype.val] at this
  --     exact this
  --   · have := h₂.right n k
  --     dsimp [Subtype.val] at this
  --     exact this⟩
  ⟨fun a b ↦ ⟨
    h₁.1 ⟨_, a.2.1⟩ fun i ↦ ⟨_, (b i).2.1⟩,
    h₂.1 ⟨_, a.2.2⟩ fun i ↦ ⟨_, (b i).2.2⟩⟩,
  fun _ _ ↦ ⟨h₁.2 _ _, h₂.2 _ _⟩⟩

/- The subtype of functions `t^k ↦ t` that obey a clonal property, form a clone. -/
instance clonal_property_clone {p} (h : clonal_function_property t p) :
    Clone (fun k ↦ Subtype (p (k := k))) where

  superpose := fun a b ↦ ⟨function_superpose a.1 (Subtype.val ∘ b), h.1 a b⟩
  proj := fun _ _ ↦ ⟨fun ts ↦ ts _, h.2 _ _⟩
  one := ⟨fun ts ↦ ts 0, h.2 1 0⟩

  one_proj := rfl
  superpose_assoc := fun _ _ _ ↦ rfl
  proj_left := fun _ _ ↦ rfl
  proj_right := fun _ ↦ rfl

/- Monotonicity is a `clonal_function_property` - monotone functions from a clone. -/
theorem clonal_Monotone [Preorder t] : clonal_function_property t (fun {_} ↦ Monotone) :=
  ⟨fun a b _ _ h ↦ a.2 fun _ ↦ (b _).2 h, fun _ _ _ _ h ↦ h _⟩

/- Functions that are *conjunctive* over a preorder form a clone. A function is conjunctive
  is f(min(x,y)) = min(f(x), f(y)), and this extends to pi-types in the natural way. -/
theorem clonal_Conjunctive [Min t] : clonal_function_property t (fun {_} ↦ Conjunctive) :=
  ⟨fun a b _ _ ↦ by
      rw [← a.property]
      dsimp [Pi.instMinForall_mathlib, function_superpose, Function.swap]
      congr!
      rw [← (b _).property]
      rfl, fun _ _ _ _ ↦ rfl⟩

/- Functions that are *disjunctive* over a preorder form a clone. A function is conjunctive
  is f(min(x,y)) = min(f(x), f(y)), and this extends to pi-types in the natural way. -/
theorem clonal_Disjunctive [Max t] : clonal_function_property t (fun {_} ↦ Disjunctive) :=
  ⟨fun a b _ _ ↦ by
      rw [← a.property]
      dsimp [Pi.instMaxForall_mathlib, function_superpose, Function.swap]
      congr!
      rw [← (b _).property]
      rfl, fun _ _ _ _ ↦ rfl⟩

/- States that the multiargument funtion `f`, whose arguments are indexed by the type `α`
  commutes with an endomorphism `φ : t → t` applied argumentwise. -/
def multiarg_CommutesWithEndo {α t : Type*} (φ : t → t) (f : (α → t) → t) : Prop :=
  ∀ ts, φ (f ts) = f (fun i ↦ φ (ts i))

/- For an endomorphism `φ : t → t`, the multiargument functions that commute with `φ` form
  a clone. -/
theorem clonal_CommutesWithEndo (φ : t → t) :
  clonal_function_property t (fun {_} ↦ multiarg_CommutesWithEndo φ) :=
  ⟨fun a b _ ↦ by
    dsimp [function_superpose]
    rw [a.property]
    congr!
    exact (b _).property _, fun _ _ _ ↦ rfl⟩

/- A multiargument function is _essentially unary_ if there is one argument that entirely
  determines the value of the function. -/
def EssentiallyUnary {α t : Type*} (f : (α → t) → t) : Prop :=
  ∃(i : α) (fi : t → t), ∀ts, f ts = fi (ts i)

theorem clonal_EssentiallyUnary : clonal_function_property t (fun {_} ↦ EssentiallyUnary) :=
  ⟨fun a b ↦ by
    rcases a with ⟨_, ⟨ai, fa, ha⟩⟩
    set! bai := b ai with hbai
    rcases bai.2 with ⟨bi, fb, hb⟩
    refine ⟨bi, fa ∘ fb, fun _ ↦ ?_⟩
    dsimp [function_superpose]
    rw [← hb, hbai, ha]
    rfl, fun _ _ ↦ ⟨_, id, fun _ ↦ rfl⟩⟩

/- A multiargument function `f : t^m → t` is `k`-wise P-preserving, for an integer k and a set
  `P ⊆ t`, is defined as follows. Given `k`-tuple `kts` of arguments (each argument
  `ts` of type `t^m`), call it "elementwise in P" if each index `i : Fin m` has at least one
  `(kts j) i ∈ P` for some `j : Fin k`. Then `f` maps tuples that are elementwise in P to a
  1-tuple that is elementwise in P. That is, `∃ j : Fin k` such that `f (kts j) ∈ P`.

  Being `k`-wise P-preserving implies also being `k₂`-wise P-preserving for any `k₂ ≤ k`. There
  is also the extension to `k = ∞`, which says the property holds for all `k`. For this reason,
  we take `k` to be a `WithTop ℕ`. An important case is `k=1`, which simply states that `f`
  applied to a vector of `P` values is also in `P`.

  Here we formalize it (without subsets) by saying that `P` is a predicate `t → Prop`. Although
  the property is normally discussed on functions whose arguments are indexed by `Fin m`, we can
  allow the index to be an arbitrary `α`. -/
def kWisePropPreserving {t : Type*} (k : WithTop ℕ) (P : t → Prop) (f : (α → t) → t) : Prop :=
  let elementwiseP {m : ℕ} (kts : Fin m → (α → t)) := ∀ i, ∃ j, P ((kts j) i)
  ∀ {m : ℕ} (_ : m ≤ k) (kts : Fin m → (α → t)) (_ : elementwiseP kts),
    ∃ j, P (f (kts j))

theorem clonal_kWisePropPreserving (k : WithTop ℕ) (P : t → Prop) :
    clonal_function_property t (fun {_} ↦ kWisePropPreserving k P) :=
  ⟨fun a b _ hm kts h ↦ a.2 hm
    (fun _ _ ↦ (b _).1 (kts _))
    (fun _ ↦ (((b _).2 hm) _) (fun _ ↦ h _)),
  fun _ _ _ _ _ h ↦ h _⟩

/- The Prop that a function from `t^α → t`, written as `(α → t) → t`, is affine: there is a list
  of coefficient `c : t` at each index `i : α`, that determines the changes in `f` when the single
  argument at `i` is changed. This is alternate characterization of affine maps, and equivalent to
  `AffineMap t (α → t) t`  when the ring is commutative, as proved in
  `multiargAffine_iff_AffineMap`. -/
def multiargAffine [Fintype α] [DecidableEq α] [Ring t] (f : (α → t) → t) : Prop :=
  ∀ i, ∃ c, ∀ xs y, f xs - (f (Function.update xs i y)) = c * (xs i - y)

lemma Finset.sum_Fin_succ [AddCommMonoid t] {n} (f : Fin n.succ → t) :
    (∑ i : Fin n.succ, f i) = f n + (∑ i : Fin n, f i) :=
  sorry

lemma Function.update_lincomb [CommRing t] {k} (xs : Fin k → t) (i : Fin k) (y : t) :
    Function.update xs i y = xs + fun j => if i = j then y - xs i else 0 := by
  funext j
  by_cases hji : j = i
  · rw [hji]; simp
  · rw [Function.update_noteq hji]
    simp [Ne.symm hji]

/- For a multiargAffine function whose indices are indexed by Fin k, the function is the
  sum of its evaluation at zero and its coefficient terms. -/
theorem multiargAffine_eq_sum [CommRing t] {k} (f : (Fin k → t) → t) (hf : multiargAffine f) :
  ∀ ts, f ts = f 0 + ∑ j : Fin k, Classical.choose (hf j) * (ts j) := by
    induction k
    case zero =>
      suffices f finZeroElim = f ![] by simpa
      rfl
    case succ k' hk' =>
      intro ts

      --define a new function f', which is like f but pretends the last argument is always 0.
      let droplast (ts : Fin (k'.succ) → t) : Fin k' → t := fun i' ↦
        (if hi' : i'.1 < k' then ts ⟨i'.1, by linarith⟩ else 0)
      let padzero (ts : Fin k' → t) : Fin (k'.succ) → t := fun i' ↦
        (if hi' : i'.1 < k' then ts ⟨i'.1, by linarith⟩ else 0)

      obtain ⟨cks, hcks⟩ := hf k'.succ
      let f' : (Fin k' → t) → t := fun ts' ↦ f (padzero ts') + cks * (ts k')

      have hf'_maA : multiargAffine f' := by -- need to prove our f' function was multiargAffine
        sorry <;> {
        unfold_let
        dsimp [multiargAffine] --do that by giving coefficients
        rintro ⟨i, hik'⟩
        obtain ⟨c, hc⟩ := hf ⟨i, Nat.lt.step hik'⟩ --for most indices, the coefficient was the same as f
        use c
        intro xs y
        replace hc := hc (padzero xs) y
        dsimp at hc
        simp only [Fin.is_lt, dif_pos hik'] at hc
        rw [← hc]
        simp only [add_sub_add_right_eq_sub]
        congr! with x
        dsimp [Function.update]
        simp only [Fin.mk.injEq, eq_rec_constant, dite_eq_ite]
        by_cases hx1i : x.1 = i
        next =>
          simp only [ite_true, dite_true, hik', hx1i]
          rw [if_pos (Fin.eq_mk_iff_val_eq.mpr hx1i)]
        next =>
          by_cases hx1k : x.1 < k'
          <;> simp only [ite_false, dite_false, dite_true, hx1k, hx1i]
          <;> rw [if_neg (Fin.ne_of_vne hx1i)]
        }

      --use our f' function in the inductive hypothesis
      have hf' := hk' f' hf'_maA (droplast ts)
      have hff' : f ts = f' (droplast ts) := by
        dsimp
        have hfiu : (fun (i' : Fin (Nat.succ k')) => if ↑i' < k' then if ↑i' < k' then
            ts i' else 0 else 0)
            = Function.update ts k' 0 := by
          sorry <;> {
          funext x
          dsimp [Function.update]
          split_ifs with h₁ h₂ h₂
          · simp [h₂] at h₁
          · rfl
          · simp only [eq_rec_constant]
          · obtain ⟨x,hx⟩ := x
            simp only [not_lt] at h₁
            have : x = k' := by linarith (config := {splitNe := true})
            simp [this] at h₂
            exact (h₂ rfl).rec
          }
        -- rw [hfiu]
        -- obtain ⟨ck', hck'⟩ := hf k'
        -- replace hck' := sub_zero (ts k') ▸ hck' ts 0
        sorry
        -- rw [← hck']
      have hff'₂ : f 0 = f' 0 := by
        -- simp only [Fin.cast_nat_eq_last, Pi.zero_apply, dite_eq_ite, ite_self]
        sorry
      rw [hff', hff'₂, hf']
      congr 1
      rw [Finset.sum_Fin_succ]
      sorry

#print multiargAffine_eq_sum

/- A function is `multiargIsAffine` iff there is an equivalent AffineMap -/
theorem multiargAffine_iff_AffineMap [CommRing t] {k} (f : (Fin k → t) → t) :
  (multiargAffine f) ↔ (∃ (a : AffineMap t (Fin k → t) t), a = f) := by
    constructor
    · intro hf
      constructor; swap
      · apply AffineMap.mk' f
        case p => exact 0
        case f' =>
          apply LinearMap.mk _ _
          · apply AddHom.mk _ _
            · exact fun x ↦ f x - f 0
            · intro x y
              have hf₂ := multiargAffine_eq_sum f hf
              rw [hf₂ (x + y), hf₂ x, hf₂ y]
              simp only [Pi.add_apply, add_sub_cancel']
              simp_rw [← Finset.sum_add_distrib, mul_add]
          · simp only [RingHom.id_apply, smul_eq_mul]
            intro r x
            rw [multiargAffine_eq_sum f hf (r • x), multiargAffine_eq_sum f hf x]
            simp only [Pi.smul_apply, smul_eq_mul, add_sub_cancel']
            simp_rw [mul_comm, Finset.mul_sum, ← mul_assoc]
        case h =>
          intro
          dsimp
          ring_nf
      · apply AffineMap.coe_mk'
    · rintro ⟨a, ha⟩ i
      use a (fun j ↦ ite (i=j) 1 0) - a 0
      intros
      rw [← ha, a.decomp, Function.update_lincomb]
      simp only [Pi.add_apply, map_add, add_sub_add_right_eq_sub, sub_add_cancel', map_zero,
        zero_add, add_sub_cancel]
      rw [← LinearMap.map_neg, mul_comm, ← smul_eq_mul, ← a.linear.map_smul]
      dsimp [Neg.neg, HSMul.hSMul, SMul.smul]
      congr! 2
      rw [apply_ite Neg.neg]
      simp only [neg_sub, neg_zero, mul_ite, mul_one, mul_zero]

def IsAffineMap [CommRing t] {k} (f : (Fin k → t) → t) : Prop :=
  ∃ a : AffineMap t (Fin k → t) t, a = f

/- Affine maps form a clone. -/
-- theorem clonal_AffineMap [CommRing t] : clonal_function_property t multiargAffine :=
--   ⟨fun {n m} a b i ↦ by
--     obtain ⟨av, ha⟩ := a
--     eta_reduce at ha
--     use ∑ j : Fin n, (Classical.choose (ha j)) * (Classical.choose ((b j).2 i))
--     intro xs y
--     dsimp [function_superpose]
--     have ha₁ := fun j ↦ Classical.choose_spec (ha j)
--     have hbj := fun j ↦ Classical.choose_spec ((b j).2 i)
--     have haσ := multiargAffine_eq_sum av ha
--     rw [ha₁ j]
--     -- conv =>
--     --   rhs
--     --   arg 1
--     --   arg 2
--     --   intro j
--     --   tactic => have := ha₁ j
--     --   rw [←  _ y]
--     -- set b_coeffs := fun j ↦ Classical.choose ((b j).2 i) with def_b_coeffs
--     -- have hb_coeffs : (∀j,
--     --   ∀ xs y, (b j).1 xs - (b j).1 (Function.update xs i y) = (b_coeffs j) * (xs i - y)
--     -- ) := by
--     --   intro j xs ys
--     --   dsimp [def_b_coeffs]
--     --   apply Classical.choose_spec (p := fun c ↦ ∀ xs ys,
--     --     ↑(b j) xs - ↑(b j) (Function.update xs i ys) = c * (xs i - ys))
--     --   sorry
--     sorry,
--    fun n k i ↦ if hki : k = i
--     then ⟨1, by rw [hki]; simp⟩
--     else ⟨0, by simp [Function.update_noteq hki]⟩
--   ⟩

/- Functions that are `IsAffineMap` form a clone-/
-- theorem clonal_IsAffineMap [CommRing t] : clonal_function_property t IsAffineMap :=
--   ⟨fun {m n} a b ↦ by
--   dsimp [IsAffineMap]
--   -- let bprod := b
--   sorry,
--   fun n k ↦ ⟨AffineMap.mk' (fun ts => ts k) ⟨⟨fun ts => ts k, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
--     0 (fun _ ↦ eq_add_of_sub_eq rfl)
--   , rfl⟩⟩

-- def LinearMap.pi_sum [Fintype α] [Ring R] [AddCommMonoid M] [Module R M]
--     (fs : α → (M →ₗ[R] R)) : (α → M) →ₗ[R] R := by
--   apply LinearMap.mk
--   case toAddHom =>
--     sorry
--   case map_smul' =>
--     sorry

-- def AffineMap.pi_sum [Fintype α] [Ring R] [AddCommGroup M] [Module R M]
--     (fs : α → (M →ᵃ[R] R)) : (α → M) →ᵃ[R] R := by
--   sorry

-- def AffineMap.pi [Ring R] [AddCommGroup V1] [Module R V1] [AddTorsor V1 P1]
--   [AddCommGroup V2] [Module R V2] [AddTorsor V2 P2]
--     (fs : α → (P1 →ᵃ[R] P2)) : P1 →ᵃ[R] (α → P2) where
--   toFun := fun m a ↦ (fs a).1 m
--   linear := LinearMap.pi (AffineMap.linear ∘ fs)
--   map_vadd' := fun _ _ ↦ funext fun a ↦ (fs a).3 _ _


variable {k V1 P1 V2 P2 ι : Type*}
  [Ring k] [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1]
  [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2]

variable {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

/- `AffineMap`s form a clone. -/
instance clone_AffineMap [Ring t] : Clone (fun {k} ↦ AffineMap t (Fin k → t) t) where
  superpose := fun {n m} a bs ↦ by
    have bprod : (Fin m → t) →ᵃ[t] Fin n → t := AffineMap.pi bs
    exact AffineMap.comp a bprod
  proj := fun n k ↦ AffineMap.mk' (fun ts => ts k) ⟨⟨fun ts => ts k, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    0 (fun _ ↦ eq_add_of_sub_eq rfl)
  one := AffineMap.mk' (fun ts => ts 0) ⟨⟨fun ts => ts 0, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    0 (fun _ ↦ eq_add_of_sub_eq rfl)

  one_proj := rfl
  superpose_assoc := fun _ _ _ ↦ rfl
  proj_left := fun _ _ ↦ rfl
  proj_right := fun _ ↦ rfl


local notation "FuncWithProperty[ " t "," p "]" => (fun k ↦ @Subtype ((Fin k → t) → t) p)

/- Monotone functions form a clone. -/
instance Monotone_Clone [Preorder t] : Clone FuncWithProperty[t, Monotone] :=
  clonal_property_clone clonal_Monotone

/- Functions that are *conjunctive* over a preorder form a clone. A function is conjunctive
  is f(min(x,y)) = min(f(x), f(y)), and this extends to pi-types in the natural way. -/
instance Conjunctive_Clone [Min t] : Clone FuncWithProperty[t, Conjunctive] :=
  clonal_property_clone clonal_Conjunctive

/- Functions that are *disjunctive* over a preorder form a clone. A function is conjunctive
  is f(min(x,y)) = min(f(x), f(y)), and this extends to pi-types in the natural way. -/
instance Disjunctive_Clone [Max t] : Clone FuncWithProperty[t, Disjunctive] :=
  clonal_property_clone clonal_Disjunctive

/- Functions t^k → t that commute with a fixed function (φ : t → t) form a clone. -/
instance Commute_with_φ_Clone (φ : t → t) :
    Clone FuncWithProperty[t, multiarg_CommutesWithEndo φ] :=
  clonal_property_clone (clonal_CommutesWithEndo φ)

/- Functions t^k → t that only depend on one argument form a clone -/
instance EssentiallyUnary_Clone : Clone FuncWithProperty[t, EssentiallyUnary] :=
  clonal_property_clone clonal_EssentiallyUnary

/- Functions that map k-tuples that elementwise obey P to at least one element that obeys P,
 form a clone. See `kWisePropPreserving` for the precise definition. -/
instance kWisePropPreserving_Clone (k : WithTop ℕ) (P : t → Prop) :
 Clone FuncWithProperty[t, kWisePropPreserving k P] :=
  clonal_property_clone (clonal_kWisePropPreserving k P)

end property_clones
