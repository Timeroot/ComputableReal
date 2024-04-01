import Mathlib

--============
--silly lemmas
theorem abs_ite_le [inst : LinearOrderedAddCommGroup α] (x : α) :
    abs x = if 0 ≤ x then x else -x := by
  split_ifs <;> simp_all
  next h =>
    exact LT.lt.le h

namespace Trunc

/- Any constant two-argument function lifts to a function out of the truncation. -/
def lift₂ (f : α → β → γ) (c : ∀ a b : α, ∀ c d : β, f a c = f b d) :
    Trunc α → Trunc β → γ :=
  Quot.lift₂ f (fun a b₁ b₂ _ ↦ c a a b₁ b₂) (fun a₁ a₂ b _ ↦ c a₁ a₂ b b)

/-- A function `f : α → β → γ` defines a function `map f : Trunc α → Trunc β`. -/
def map₂ (f : α → β → γ) (q : Trunc α) (r : Trunc β) : Trunc γ :=
  lift₂ (fun a b ↦ Trunc.mk (f a b)) (fun _ _ _ _ ↦ Trunc.eq _ _) q r

end Trunc

namespace CauSeq

variable [LinearOrderedField α] {a b : CauSeq α abs}

theorem sup_equiv_of_equivs (ha : a ≈ c) (hb : b ≈ c) : a ⊔ b ≈ c := by
  intro n hn
  obtain ⟨i₁, hi₁⟩ := ha n hn
  obtain ⟨i₂, hi₂⟩ := hb n hn
  use max i₁ i₂
  intro j hj
  replace hi₁ := hi₁ j (Nat.max_le.mp hj).1
  replace hi₂ := hi₂ j (Nat.max_le.mp hj).2
  dsimp at hi₁ hi₂ ⊢
  rw [sup_eq_max, max_def]
  rw [abs_ite_le] at hi₁ hi₂ ⊢
  split_ifs at hi₁ hi₂ ⊢
  all_goals linarith

theorem equiv_sup_of_equivs (ha : c ≈ a) (hb : c ≈ b) : c ≈ a ⊔ b :=
  Setoid.symm (sup_equiv_of_equivs (Setoid.symm ha) (Setoid.symm hb))

theorem inf_equiv_of_equivs (ha : a ≈ c) (hb : b ≈ c) : a ⊓ b ≈ c := by
  --if we had a version of `neg_inf` for CauSeq this could be easily
  --reduced to `sup_equiv_of_equivs`.
  intro n hn
  obtain ⟨i₁, hi₁⟩ := ha n hn
  obtain ⟨i₂, hi₂⟩ := hb n hn
  use max i₁ i₂
  intro j hj
  replace hi₁ := hi₁ j (Nat.max_le.mp hj).1
  replace hi₂ := hi₂ j (Nat.max_le.mp hj).2
  dsimp at hi₁ hi₂ ⊢
  rw [inf_eq_min, min_def]
  rw [abs_ite_le] at hi₁ hi₂ ⊢
  split_ifs at hi₁ hi₂ ⊢
  all_goals linarith

theorem equiv_inf_of_equivs (ha : c ≈ a) (hb : c ≈ b) : c ≈ a ⊓ b :=
  Setoid.symm (inf_equiv_of_equivs (Setoid.symm ha) (Setoid.symm hb))

/-- Dropping the first n terms of a Cauchy sequence to get a new sequence. -/
def drop (a : CauSeq α abs) (n : ℕ) : CauSeq α abs :=
  ⟨fun k ↦ a.val (n+k), fun _ hq ↦ Exists.casesOn (cauchy₂ a hq)
    fun i hi ↦ ⟨i,
      fun _ hj ↦ hi _ (le_add_of_le_right hj) _ (Nat.le_add_left i n)⟩⟩

/-- Dropping elements from a Cauchy sequence gives an equivalent one. -/
theorem drop_equiv_self (a : CauSeq α abs) (n : ℕ) : a.drop n ≈ a :=
  fun _ hq ↦ Exists.casesOn (cauchy₂ a hq)
    fun i hi ↦ ⟨i, fun _ hj ↦ hi _ (le_add_of_le_right hj) _ hj⟩

section Rat

def apply (a : CauSeq ℚ abs) (f : ℚ → ℚ) (hf : Continuous f) : CauSeq ℚ abs :=
  ⟨f ∘ a.1, by
    -- let x := Real.mk a
    intro ε hε
    rw [continuous_iff_continuousAt] at hf
    dsimp [ContinuousAt] at hf
    simp_rw [LinearOrderedAddCommGroup.tendsto_nhds] at hf
    rify at hf
    -- let ⟨i, hi⟩ := a.2 ε hε
    -- use i
    -- intro j hj
    -- replace hi := hi j hj
    -- replace hf := hf (f (a i)) ε hε
    -- dsimp [Filter.Eventually] at hf
    -- by_contra hg; revert hf
    -- simp only [imp_false, not_forall]
    -- simp only [ge_iff_le, Function.comp_apply, not_exists, not_forall, not_lt, exists_prop] at hg
    -- -- have := nhds x
    -- have := tendsto_zero_iff_abs_tendsto_zero
    -- simp at hf
    -- cases hf
    -- δ
    sorry
  ⟩

theorem equiv_apply (a b : CauSeq ℚ abs) (f : ℚ → ℚ) (hf : Continuous f) (hab : a ≈ b) :
    a.apply f hf ≈ b.apply f hf :=
  sorry

end Rat

end CauSeq

namespace Continuous

lemma continuous_embed (fq : ℚ → ℚ) (fr : ℝ → ℝ) (hfr : ∀q, fq q = fr q) (hf₂ : Continuous fr) :
    Continuous fq :=
  sorry

end Continuous

--end silly lemmas
--================

/-- Type class for sequences that converge to a given real, x -/
class HasComputableℝSeq (x : ℝ) :=
  lb : CauSeq ℚ (abs : ℚ → ℚ)
  ub : CauSeq ℚ (abs : ℚ → ℚ)
  hlb : ∀n, lb n ≤ x
  hub : ∀n, ub n ≥ x
  heq : lb ≈ ub

namespace HasComputableℝSeq

local notation "qabs" => (abs : ℚ → ℚ)

-- theorem lb_equiv_self (hx : HasComputableℝSeq x) : CauSeq.Completion.mk hx.lb = x.cauchy := by
  -- rw [← Quotient.out_equiv_out]
  -- intro ε hε
  -- obtain ⟨i₁, hi₁⟩ := hx.heq (ε/2) (half_pos hε)
  -- obtain ⟨i₂, hi₂⟩ := (Quotient.out x.cauchy).2 (ε/2) (half_pos hε)
  -- let i := max i₁ i₂
  -- use i
  -- intro j hj
  -- replace hi₁ := hi₁ j (le_of_max_le_left hj)
  -- replace hi₂ := hi₂ j (le_of_max_le_right hj)
  -- push_cast
  -- have hs₁ : (↑(Quotient.out (CauSeq.Completion.mk (lb x))) : ℕ → ℚ) j = lb x j := by
  --   suffices ↑(Quotient.out (CauSeq.Completion.mk (lb x))) = ↑(lb x) by
  --     rw
  --   simp
  --   sorry
  -- have hs₂ := hx.hlb j
  -- have hs₃ := hx.hub j
  -- rw [abs_ite_le] at hi₁ hi₂ ⊢
  -- split_ifs at hi₁ hi₂ ⊢
  -- <;> try linarith
  -- simp
  -- sorry

-- theorem lb_eq_self (hx : HasComputableℝSeq x) : Real.mk hx.lb = x := by
--   rw [Real.mk, lb_equiv_self]

-- theorem ub_eq_self (hx : HasComputableℝSeq x) : Real.mk hx.lb = x :=
  -- sorry

theorem lb_le_ub (hx : HasComputableℝSeq x) : ∀n, hx.lb n ≤ hx.ub n :=
  fun n ↦ Rat.cast_le.mp (le_trans (hx.hlb n) (hx.hub n))


variable {x y : ℝ} (q : ℚ)

def computable_ofRat : HasComputableℝSeq q :=
  ⟨CauSeq.const qabs q, CauSeq.const qabs q, fun _ ↦ rfl.le, fun _ ↦ rfl.le, Real.mk_eq.mp rfl⟩

instance instComputableRat : HasComputableℝSeq q :=
  computable_ofRat q

instance instComputableInt (n : ℤ) : HasComputableℝSeq n :=
  computable_ofRat n

instance instComputableNat (n : ℕ) : HasComputableℝSeq n :=
  computable_ofRat n

-- instance instComputableOfNat : (n : ℕ) → (i : OfNat ℝ n) → HasComputableℝSeq (
--     @OfNat.ofNat ℝ n i : ℝ) :=
--   fun {n i} ↦ ⟨CauSeq.const qabs (OfNat.ofNat n (self := i)), CauSeq.const qabs n, fun _ ↦ by
--     rw [OfNat.ofNat]
--     simp
--     sorry--exact?,
--     ,fun _ ↦ rfl.le, sorry⟩

/-- Ideally this should be captured by instComputableOfNat, but the instance inference
 seems broken -- but covering 1 seems nice and worth having. -/
instance instComputableOfNat1 : HasComputableℝSeq
    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOneReal))
     :=
  ⟨CauSeq.const qabs 1, CauSeq.const qabs 1, fun _ ↦ by simp, fun _ ↦ by simp, Real.mk_eq.mp rfl⟩

def computableAdd (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) : HasComputableℝSeq (x + y) where
  lb := hx.lb + hy.lb
  ub := hx.ub + hy.ub
  hlb n := by push_cast; exact add_le_add (hx.hlb n) (hy.hlb n)
  hub n := by push_cast; exact add_le_add (hx.hub n) (hy.hub n)
  heq := CauSeq.add_equiv_add hx.heq hy.heq

instance instHasComputableAdd [hx : HasComputableℝSeq x] [hy : HasComputableℝSeq y] : HasComputableℝSeq (x + y) :=
  computableAdd hx hy

def computableNeg (hx : HasComputableℝSeq x) : HasComputableℝSeq (-x) where
  lb := -hx.ub
  ub := -hx.lb
  hlb n := by
    rw [CauSeq.neg_apply, Rat.cast_neg, neg_le_neg_iff]
    exact hx.hub n
  hub n := by
    rw [CauSeq.neg_apply, Rat.cast_neg, ge_iff_le, neg_le_neg_iff]
    exact hx.hlb n
  heq := CauSeq.neg_equiv_neg (Setoid.symm hx.heq)

instance instHasComputableNeg [hx : HasComputableℝSeq x] : HasComputableℝSeq (-x) :=
  computableNeg hx

def computableSub (_ : HasComputableℝSeq x) (_ : HasComputableℝSeq y) : HasComputableℝSeq (x - y) :=
  (inferInstance : HasComputableℝSeq (x + (-y)))

instance instHasComputableSub [hx : HasComputableℝSeq x] [hy : HasComputableℝSeq y] : HasComputableℝSeq (x - y) :=
  computableSub hx hy

def computeableℚFunMono (hx : HasComputableℝSeq x) (fq : ℚ → ℚ) (fr : ℝ → ℝ) (hfr : ∀q, fq q = fr q)
    (hf₁ : Monotone fr) (hf₂ : Continuous fr) : HasComputableℝSeq (fr x) where
  lb := hx.lb.apply fq (hf₂.continuous_embed fq hfr)
  ub := hx.ub.apply fq (hf₂.continuous_embed fq hfr)
  hlb n := (hfr _).symm ▸ (hf₁ (hx.hlb n))
  hub n := (hfr _).symm ▸ (hf₁ (hx.hub n))
  heq := CauSeq.equiv_apply hx.lb hx.ub fq (hf₂.continuous_embed fq hfr) hx.heq

def computeableℚFunAnti (hx : HasComputableℝSeq x) (fq : ℚ → ℚ) (fr : ℝ → ℝ) (hfr : ∀q, fq q = fr q)
    (hf₁ : Antitone fr) (hf₂ : Continuous fr) : HasComputableℝSeq (fr x) := neg_neg x ▸
  computeableℚFunMono instHasComputableNeg (fq∘Neg.neg) (fr∘Neg.neg)
    (fun q ↦ by have := hfr (-q); rwa [Rat.cast_neg] at this)
    (hf₁.comp monotone_id.neg)
    (hf₂.comp ContinuousNeg.continuous_neg)

--Faster one for rational multiplcation
def lb_mul_q [hx : HasComputableℝSeq x] : CauSeq ℚ qabs :=
  if q ≥ 0 then hx.lb * CauSeq.const qabs q else hx.ub * CauSeq.const qabs q

def ub_mul_q [hx : HasComputableℝSeq x] : CauSeq ℚ qabs :=
  if q ≥ 0 then hx.ub * CauSeq.const qabs q else hx.lb * CauSeq.const qabs q

-- /- Multiplication of two computable sequences. Can't just use CauSeq mul because that
--  no longer gives correct upper/lower bounds. -/
-- def HasComputableℝSeqMul [hx : HasComputableℝSeq x] : HasComputableℝSeq (x * q) where
--   lb := lb_mul_q x q
--   ub := ub_mul_q x q
--   hlb n := by
--     simp_rw [lb_mul_q, min_def]
--     by_cases hq : (q:ℝ) > 0
--     <;> split_ifs with h
--     <;> rify at *
--     <;> nlinarith (config := {splitNe := true}) [hx.hlb n, hx.hub n]
--   hub n := by
--     simp_rw [ub_mul_q, max_def]
--     by_cases hq : (q:ℝ) > 0
--     <;> split_ifs with h
--     <;> rify at *
--     <;> nlinarith (config := {splitNe := true}) [hx.hlb n, hx.hub n]
--   heq := by
--     have : (ub_mul_q x q - lb_mul_q x q)
--       = fun n => (abs (ub x n - lb x n)) * (abs q) := by
--       funext n
--       dsimp
--       simp_rw [ub_mul_q, lb_mul_q]
--       simp_rw [min_def, max_def, abs_ite_le]
--       split_ifs <;> nlinarith
--     rw [this]
--     apply IsCauSeq.mul
--     · intro ε hε
--       obtain ⟨i, hi⟩ := hx.hgap ε hε
--       use i
--       intro j hj
--       replace hi := hi j hj
--       simp_rw [abs_ite_le] at hi ⊢
--       split_ifs at hi ⊢
--       <;> dsimp at * <;> linarith
--     · exact IsCauSeq.const _

-- instance instComputableQMul [HasComputableℝSeq x] : HasComputableℝSeq (q * x) :=
--   mul_comm x q ▸ instComputableMulQ x q

/- `lb_mul` and `ub_mul` are the simple definitions, that take all four possible multiplications
    and try them all to get lower and upper bounds. `lb_ub_mul` is a more performant implementation,
    that only calls each element once. -/
def lb_mul (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) : CauSeq ℚ qabs :=
  ((hx.lb * hy.lb) ⊓ (hx.ub * hy.lb)) ⊓ ((hx.lb * hy.ub) ⊓ (hx.ub * hy.ub))

def ub_mul (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) : CauSeq ℚ qabs :=
  ((hx.lb * hy.lb) ⊔ (hx.ub * hy.lb)) ⊔ ((hx.lb * hy.ub) ⊔ (hx.ub * hy.ub))

theorem lb_ub_mul_equiv (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) :
    lb_mul hx hy ≈ ub_mul hx hy := by
  have : lb x ≈ lb x := by rfl
  have : ub x ≈ ub x := by rfl
  have : lb y ≈ lb y := by rfl
  have : ub y ≈ ub y := by rfl
  have := hx.heq
  have := Setoid.symm hx.heq
  have := hy.heq
  have := Setoid.symm hy.heq
  dsimp [lb_mul, ub_mul]
  apply CauSeq.inf_equiv_of_equivs
  <;> apply CauSeq.inf_equiv_of_equivs
  <;> apply CauSeq.equiv_sup_of_equivs
  <;> apply CauSeq.equiv_sup_of_equivs
  <;> exact CauSeq.mul_equiv_mul ‹_› ‹_›

set_option maxHeartbeats 400000
theorem lb_mul_is_lb (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) (n : ℕ) :
    (lb_mul hx hy) n ≤ x * y := by
  dsimp [lb_mul, Inf.inf]
  push_cast
  have hl₁ := hx.hlb n
  have hl₂ := hx.hub n
  have hl₃ := hy.hlb n
  have hl₄ := hy.hub n
  rcases le_or_lt x 0 with hxn|hxp
  all_goals rcases le_or_lt (hy.lb n:ℝ) 0 with hyln|hylp
  all_goals rcases le_or_lt (hy.ub n:ℝ) 0 with hyun|hyup
  all_goals try nlinarith
  all_goals repeat rw [min_def]
  all_goals split_ifs with h₁ h₂ h₃ h₃ h₂ h₃ h₃
  all_goals try nlinarith

theorem ub_mul_is_ub (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) (n : ℕ) :
    (ub_mul hx hy) n ≥ x * y := by
  dsimp [ub_mul, Sup.sup]
  push_cast
  have hl₁ := hx.hlb n
  have hl₂ := hx.hub n
  have hl₃ := hy.hlb n
  have hl₄ := hy.hub n
  rcases le_or_lt x 0 with hxn|hxp
  all_goals rcases le_or_lt (hy.lb n:ℝ) 0 with hyln|hylp
  all_goals rcases le_or_lt (hy.ub n:ℝ) 0 with hyun|hyup
  all_goals try nlinarith
  all_goals repeat rw [max_def]
  all_goals split_ifs with h₁ h₂ h₃ h₃ h₂ h₃ h₃
  all_goals try nlinarith
set_option maxHeartbeats 200000 --back to normal

-- def lb_ub_mul (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) : ℕ × /

def computableMul (hx : HasComputableℝSeq x) (hy : HasComputableℝSeq y) : HasComputableℝSeq (x * y) where
  lb := lb_mul hx hy
  ub := ub_mul hx hy
  hlb n := lb_mul_is_lb hx hy n
  hub n := ub_mul_is_ub hx hy n
  heq := lb_ub_mul_equiv hx hy

instance instComputableMul [hx : HasComputableℝSeq x] [hy : HasComputableℝSeq y] : HasComputableℝSeq (x * y) :=
  computableMul hx hy

variable {x : ℝ}

private noncomputable instance is_pos'_aux_sound :
    Inhabited { b : Bool // if b then 0 < x else x ≤ 0 } :=
  ⟨⟨0 < x, by
    by_cases h : 0 < x
    simp [h]
    simp [h, le_of_not_gt h]⟩⟩

/- Given a proof that a real number x isn't *exactly* zero, it's possible to decide if
0 ≤ x or not. Without that proof, we get a partial function. Since partial functions are
opaque, and we would like to prove this function correct, we actually return a Subtype
that says what the return Bool means. Then we need to show that this type is inhabited for
it to compile, which is the instance that is_pos'_aux_sound (noncomputably) provides. -/
partial def is_pos' (hx : HasComputableℝSeq x) : Bool :=
  aux 0 where
  aux (n : ℕ) : { b : Bool // if b then 0 < x else x ≤ 0 } :=
    if h : hx.ub n < 0 then
      ⟨false, by simp only [reduceIte]; rify at h; linarith [hx.hub n] ⟩
    else if h₂ : hx.lb n > 0 then
      ⟨true, by simp only [reduceIte]; rify at h₂; linarith [hx.hlb n] ⟩
    else
      aux (n+1)

/- `is_pos'` is a correct (partial) judge of nonnegativity. -/
theorem is_pos'_iff {x : ℝ} (hx : HasComputableℝSeq x) : is_pos' hx ↔ 0 < x := by
  constructor
  · intro h
    rw [is_pos'] at h
    set b' := is_pos'.aux hx 0
    obtain ⟨b, hb⟩ := b'
    dsimp at h
    simp only [h, reduceIte] at hb
    exact hb
  · intro h
    rw [is_pos']
    set b' := is_pos'.aux hx 0
    obtain ⟨b, hb⟩ := b'
    dsimp
    split_ifs at hb
    · assumption
    · linarith

/- If x is nonzero, there is eventually a point in the Cauchy sequences where either the lower
or upper bound prove this. This theorem states that this point exists. -/
theorem sign_witness_term [hx : HasComputableℝSeq x] (hnz : x ≠ 0) :
    { xq : ℕ × ℚ // (0:ℝ) < xq.2 ∧ xq.2 < abs x ∧ ∀ j ≥ xq.1, |(lb x - ub x) j| < xq.2} := by
    have hsx : abs x > 0 := by positivity
    have hq' : ∃(q:ℚ), (0:ℝ) < q ∧ q < abs x := exists_rat_btwn hsx
    obtain ⟨q, hq⟩ := Classical.indefiniteDescription _ hq'
    obtain ⟨hq₁, hq₂⟩ := hq
    obtain ⟨i, hi⟩ := Classical.indefiniteDescription _ (hx.heq q (Rat.cast_pos.mp hq₁))
    use (i, q)

theorem sign_witness_term_prop [hx : HasComputableℝSeq x] (n : ℕ) (hnz : x ≠ 0)
    (hub : ¬(ub x).val n < 0) (hlb: ¬(lb x).val n > 0) :
    n + Nat.succ 0 ≤ (sign_witness_term hnz).val.1 := by
  push_neg at hub hlb
  obtain ⟨h₁, h₂, h₃⟩ := (sign_witness_term hnz).property
  set k := (sign_witness_term hnz).val.1
  set q := (sign_witness_term hnz).val.2
  by_contra hn
  replace h₃ := h₃ n (by linarith)
  simp_rw [CauSeq.sub_apply] at h₃
  rw [abs_ite_le] at h₂ h₃
  have := hx.hlb n
  have := hx.hub n
  split_ifs at h₂ h₃ with h₄ h₅
  all_goals
    rify at *; linarith (config := {splitNe := true})

/-- With the proof that x≠0, we can also eventually get a sign witness: a number n such that
    either 0 < x and 0 < lb n; or that x < 0 and ub n < 0. Marking it as irreducible because
    in theory all of the info needed is in the return Subtype. -/
irreducible_def sign_witness (hx : HasComputableℝSeq x) (hnz : x ≠ 0) :
    { n // (0 < x ∧ 0 < hx.lb n) ∨ (x < 0 ∧ hx.ub n < 0)} :=
  sign_witness_aux 0 hnz where
  sign_witness_aux (k : ℕ) (hnz : x ≠ 0) : { n // (0 < x ∧ 0 < hx.lb n) ∨ (x < 0 ∧ hx.ub n < 0)}:=
    if hub : hx.ub k < 0 then
      ⟨k, Or.inr ⟨by rify at hub; linarith [hx.hub k], hub⟩⟩
    else if hlb : hx.lb k > 0 then
      ⟨k, Or.inl ⟨by rify at hlb; linarith [hx.hlb k], hlb⟩⟩
    else
      sign_witness_aux (k+1) hnz
    termination_by
      (sign_witness_term hnz).val.fst - k
    decreasing_by
    · decreasing_with
      apply Nat.sub_add_lt_sub _ Nat.le.refl
      exact sign_witness_term_prop k hnz hub hlb

/-- With the proof that x≠0, we get a total comparison function. -/
def is_pos (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : Bool :=
  0 < hx.lb (sign_witness hx hnz)

#eval is_pos (x := ((1:ℝ) + 1 ) * (-1 - (5:ℕ))) (inferInstance) (by norm_num)
#eval is_pos (x := ((1:ℝ) + 1 ) * (-1 + (5:ℕ))) (inferInstance) (by norm_num)

theorem is_pos_iff {x : ℝ} (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : is_pos hx hnz ↔ 0 < x := by
  have hsw := (sign_witness hx hnz).property
  have hls := hx.hlb (sign_witness hx hnz)
  have hus := hx.hub (sign_witness hx hnz)
  constructor
  · intro h
    rw [is_pos, decide_eq_true_eq] at h
    cases hsw
    · tauto
    · rify at *
      linarith [hx]
  · intro h
    have := not_lt.mpr (le_of_lt h)
    rw [is_pos, decide_eq_true_eq]
    tauto

/- Given computable sequences for a nonzero x, drop the leading terms of both sequences
(lb and ub) until both are nonzero. This gives a new sequence that we can "safely" invert.
-/
def dropTilSigned (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : HasComputableℝSeq x :=
  let start := sign_witness hx hnz
  { lb := hx.lb.drop start,
    ub := hx.ub.drop start,
    hlb := fun n ↦ hx.hlb (start+n),
    hub := fun n ↦ hx.hub (start+n),
    heq := Setoid.trans (
      Setoid.trans (hx.lb.drop_equiv_self start) hx.heq)
      (Setoid.symm (hx.ub.drop_equiv_self start))
  }

theorem sign_dropTilSigned (hx : HasComputableℝSeq x) (hnz : x ≠ 0) :
    (0 < x ∧ 0 < (hx.dropTilSigned hnz).lb 0) ∨ (x < 0 ∧ (hx.dropTilSigned hnz).ub 0 < 0) := by
  have := (sign_witness hx hnz).prop
  have := lt_trichotomy x 0
  tauto

/-- The sequence of lower bounds of 1/x. Only functions "correctly" to give lower bounds if we
   assume that hx is already `hx.dropTilSigned` (as proven in `lb_inv_correct`) -- but those
   assumptions aren't need for proving that it's Cauchy. -/
def lb_inv (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : CauSeq ℚ qabs :=
  if hx.is_pos hnz then
    ⟨fun n ↦ (hx.ub n)⁻¹, --x is positive so 1/(upper bound) is always a good lower bound.
      sorry⟩
  else
    --x is negative, so positive values for ub don't give us any info.
    let ub0 := hx.ub 0 --save this first value, it acts as fallback if we get a bad ub
    ⟨fun n ↦
      let ub := hx.ub n
      if ub > 0 then
        ub0⁻¹ --sign is indeterminate, fall back to the starting values
      else
        ub⁻¹,
      sorry⟩

/-- Analgoous to `lb_inv` for provides upper bounds on 1/x. -/
def ub_inv (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : CauSeq ℚ qabs :=
  if hx.is_pos hnz then
    let lb0 := hx.lb 0 --save this first value, it acts as fallback if we get a bad lb
    ⟨fun n ↦
      let lb := hx.lb n
      if lb > 0 then
        lb0⁻¹ --sign is indeterminate, fall back to the starting values
      else
        lb⁻¹,
      sorry⟩
  else
    ⟨fun n ↦ (hx.lb n)⁻¹,
      sorry⟩

/-- ub_inv applied to the negative of x is the negative of lb_inv. -/
theorem ub_inv_neg (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : hx.ub_inv hnz = -(
    (hx.instHasComputableNeg).lb_inv (neg_ne_zero.mpr hnz)) :=
  sorry

/- When applied to a `dropTilSigned`, `lb_inv` is a correct lower bound on x⁻¹. -/
theorem lb_inv_correct (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : ∀n,
    (hx.dropTilSigned hnz).lb_inv hnz n ≤ x⁻¹ :=
  let k := Acc; sorry
  -- sorry

def foob (n : ℕ) : Bool := by
  induction n using Nat.strongRecOn
  exact true

/- When applied to a `dropTilSigned`, `ub_inv` is a correct upper bound on x⁻¹. -/
theorem lb_inv_correct (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : ∀n,
    (hx.dropTilSigned hnz).ub_inv hnz n ≥ x⁻¹ :=
  sorry

/- An inverse is defined only on reals that we can prove are nonzero. If we can prove they are
 nonzero, then we can prove that at some point we learn the sign, and so can start giving actual
 upper and lower bounds. -/
def computableInv (hx : HasComputableℝSeq x) (hnz : x ≠ 0) : HasComputableℝSeq (x⁻¹) :=
  let signed := hx.dropTilSigned hnz
  { lb := signed.lb_inv hnz,
    ub := signed.ub_inv hnz,
    hlb := lb_inv_correct hx hnz,
    hub := fun n ↦ sorry,
    heq := sorry }

end HasComputableℝSeq

/- Computableℝ carries around a real value constructed somehow, val:ℝ, and a
  computable sequence seq. seq is (essentially) a HasComputableℝSeq val. But we
  would like Computableℝ's x and y to be equal iff x.val and y.val are, so we
  use Trunc: all seq's of the right type are equal (and so the corresponding
  structures are). -/
structure Computableℝ where
  val : ℝ
  seq : Trunc (HasComputableℝSeq val)

namespace Computableℝ

variable (r : ℝ) (x y : Computableℝ)

theorem eq_iff_Computableℝ : x = y ↔ x.val = y.val :=
  ⟨congrArg val, fun h ↦ by
  cases x; cases y; cases h
  simp only [mk.injEq, heq_eq_eq, true_and]
  exact Trunc.eq _ _⟩

def mk' [HasComputableℝSeq r] : Computableℝ :=
  { val := r, seq := Trunc.mk inferInstance }

@[simp]
theorem mk'_val [HasComputableℝSeq r] : (mk' r).val = r :=
  rfl

def lift (f : ℝ → ℝ) (seqf : ∀{x}, HasComputableℝSeq x → HasComputableℝSeq (f x)) :
    Computableℝ → Computableℝ :=
  fun x ↦ { val := f x.val, seq := Trunc.map seqf x.seq }

def lift₂ (f : ℝ → ℝ → ℝ) (seqf : ∀ {x y}, HasComputableℝSeq x → HasComputableℝSeq y
    → HasComputableℝSeq (f x y)) : Computableℝ → Computableℝ → Computableℝ :=
  fun x y ↦ { val := f x.val y.val, seq := Trunc.map₂ seqf x.seq y.seq }

@[simp]
theorem lift_val_eq : (lift f s a).val = f a.val :=
  rfl

@[simp]
theorem lift₂_val_eq : (lift₂ f s a b).val = f a.val b.val :=
  rfl

theorem lift₂_eq_iff : (lift₂ f s a b).val = (lift₂ f s x y).val ↔
    f a.val b.val = f x.val y.val := by
  constructor
  all_goals (intro h; simp at h ⊢; exact h)

instance instComputableAdd : Add Computableℝ :=
  ⟨lift₂ (· + ·) HasComputableℝSeq.computableAdd⟩

instance instComputableMul : Mul Computableℝ :=
  ⟨lift₂ (· * ·) HasComputableℝSeq.computableMul⟩

instance instComputableNeg : Neg Computableℝ :=
  ⟨lift (- ·) HasComputableℝSeq.computableNeg⟩

instance instComputableSub : Sub Computableℝ :=
  ⟨lift₂ (· - ·) HasComputableℝSeq.computableSub⟩

instance instComputableZero : Zero Computableℝ :=
  ⟨mk' (0 : ℕ)⟩

instance instComputableOne : One Computableℝ :=
  ⟨mk' (1 : ℕ)⟩

@[simp]
theorem add_val : (x + y).val = x.val + y.val := by
  rfl

@[simp]
theorem mul_val : (x * y).val = x.val * y.val := by
  rfl

@[simp]
theorem neg_val : (-x).val = -(x.val) := by
  rfl

@[simp]
theorem sub_val : (x - y).val = x.val - y.val := by
  rfl

@[simp]
theorem zero_val : (0 : Computableℝ).val = 0 := by
  rw [Zero.toOfNat0, instComputableZero]
  simp only [mk'_val, CharP.cast_eq_zero]

 @[simp]
theorem one_val : (1 : Computableℝ).val = 1 := by
  rw [One.toOfNat1, instComputableOne]
  simp only [mk'_val, Nat.cast_one]

instance instComputableRing : CommRing Computableℝ := by
  refine' { natCast := fun n => mk' n
            intCast := fun z => mk' z
            zero := 0
            one := 1
            mul := (· * ·)
            add := (· + ·)
            neg := (- ·)
            sub := (· - ·)
            npow := @npowRec _ ⟨mk' (1:ℕ)⟩ ⟨(· * ·)⟩
            nsmul := @nsmulRec _ ⟨mk' (0:ℕ)⟩ ⟨(· + ·)⟩
            zsmul := @zsmulRec _ ⟨mk' (0:ℕ)⟩ ⟨(· + ·)⟩ ⟨@Neg.neg _ _⟩,
            .. }
  all_goals
    intros
    first
    | rfl
    | rw [eq_iff_Computableℝ]
      simp
      first
      | dsimp [Nat.cast]
        simp only [Nat.cast_add, Nat.cast_one, neg_add_rev]
      | try ring_nf!

theorem isField : IsField Computableℝ where
  exists_pair_ne := ⟨0, 1, by
    rw [ne_eq, eq_iff_Computableℝ, zero_val, one_val]
    exact zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := sorry

end Computableℝ
