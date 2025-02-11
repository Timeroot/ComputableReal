import ComputableReal.IsComputable
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Peel

theorem cauchy_real_mk (x : CauSeq ℚ abs) : ∀ ε > 0, ∃ i, ∀ j ≥ i, |x j - Real.mk x| < ε := by
  intro ε hε
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hε
  obtain ⟨i, hi⟩ := x.2.cauchy₂ (by simpa using hq)
  simp_rw [abs_sub_comm]
  refine ⟨i, fun j hj ↦ lt_of_le_of_lt (Real.mk_near_of_forall_near ⟨i, fun k hk ↦ ?_⟩) hq'⟩
  exact_mod_cast (hi k hk j hj).le

/-- This is very similar to the statement
`TendstoLocallyUniformly (fun n x ↦ (F n x : ℝ)) (fun (q : ℚ) ↦ f q) .atTop`
but that only uses neighborhoods within the rationals, which is a strictly
weaker condition. This uses neighborhoods in the ambient space, the reals.
-/
def TendstoLocallyUniformlyWithout (F : ℕ → ℚ → ℚ) (f : ℝ → ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ (x : ℝ), ∃ t ∈ nhds x, ∃ a, ∀ (b : ℕ), a ≤ b → ∀ (y : ℚ), ↑y ∈ t →
    |f y - ↑(F b y)| < ε

theorem Real_mk_of_TendstoLocallyUniformly' (fImpl : ℕ → ℚ → ℚ) (f : ℝ → ℝ)
    (hfImpl : TendstoLocallyUniformlyWithout (fImpl) (f))
    (hf : Continuous f)
    (x : CauSeq ℚ abs)
    : ∃ (h : IsCauSeq abs (fun n ↦ fImpl n (x n))), Real.mk ⟨_, h⟩ = f (.mk x) := by

  apply Real.of_near

  simp only [Metric.continuous_iff, gt_iff_lt, Real.dist_eq] at hf

  rcases x with ⟨x, hx⟩
  intro ε hε

  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hf (.mk ⟨x, hx⟩) _ (half_pos hε)
  obtain ⟨i₁, hi₁⟩ := cauchy_real_mk ⟨x, hx⟩ δ₁ hδ₁pos

  obtain ⟨i₂_nhd, hi₂_nhds, i₃, hi₃⟩ := hfImpl _ (half_pos hε) (.mk ⟨x, hx⟩)
  obtain ⟨nl, nu, ⟨hnl, hnu⟩, hnd_sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hi₂_nhds
  replace hnd_sub : ∀ (r : ℚ), nl < r ∧ r < nu → ↑r ∈ i₂_nhd := fun r a => hnd_sub a
  replace hi₃ : ∀ (b : ℕ), i₃ ≤ b → ∀ (y : ℚ), nl < y ∧ y < nu → |f ↑y - ↑(fImpl b y)| < (ε / 2) := by
    peel hi₃
    exact fun h ↦ this (hnd_sub _ h)

  set ε_nhd := min (nu - (.mk ⟨x,hx⟩)) ((.mk ⟨x,hx⟩) - nl) with hε_nhd
  obtain ⟨i₄, hi₄⟩ := cauchy_real_mk ⟨x,hx⟩ (ε_nhd / 2) (by
    rw [hε_nhd, gt_iff_lt, ← min_div_div_right (zero_le_two), lt_inf_iff]
    constructor <;> linarith)

  have hεn₁ : ε_nhd ≤ _ := inf_le_left
  have hεn₂ : ε_nhd ≤ _ := inf_le_right

  set i := max i₁ (max i₃ i₄) with hi
  use i
  intro j hj
  simp only [hi, ge_iff_le, sup_le_iff] at hj

  specialize hδ₁ _ (hi₁ j (by linarith))
  specialize hi₄ j (by linarith)
  specialize hi₃ j (by linarith) (x j) (by
    constructor
    · linarith [sub_le_of_abs_sub_le_left hi₄.le]
    · linarith [sub_le_of_abs_sub_le_right hi₄.le]
  )

  calc |↑(fImpl j (x j)) - f (Real.mk ⟨x, hx⟩)| =
    |(↑(fImpl j (x j)) - f ↑(x j)) + (f ↑(x j) - f (Real.mk ⟨x, hx⟩))| := by congr; ring_nf
    _ ≤ |(↑(fImpl j (x j)) - f ↑(x j))| + |(f ↑(x j) - f (Real.mk ⟨x, hx⟩))| := abs_add _ _
    _ < ε := by rw [abs_sub_comm]; linarith

open scoped QInterval

namespace Rat

def toDecimal (q : ℚ) (prec : ℕ := 20):=
  (q.floor.repr).append <| ".".append <| (10^prec * (q - q.floor)).floor.repr.leftpad prec '0'

end Rat

namespace ComputableℝSeq

def of_TendstoLocallyUniformly_Continuous
    {f : ℝ → ℝ} (hf : Continuous f)
    (fImpl : ℕ → ℚInterval → ℚInterval)
    (fImpl_l : ℕ → ℚ → ℚ)
    (fImpl_u : ℕ → ℚ → ℚ)
    (hlb : ∀ (n : ℕ) (q : ℚInterval) (x : ℝ), x ∈ q → fImpl_l n q.fst ≤ f x)
    (hub : ∀ (n : ℕ) (q : ℚInterval) (x : ℝ), x ∈ q → f x ≤ fImpl_u n q.snd)
    (hImplDef : ∀ n q, fImpl n q = ⟨⟨fImpl_l n q.fst, fImpl_u n q.snd⟩,
      Rat.cast_le.mp ((hlb n q q.fst ⟨le_refl _, Rat.cast_le.mpr q.2⟩).trans
      (hub n q q.fst ⟨le_refl _, Rat.cast_le.mpr q.2⟩))⟩)
    (hTLU_l : TendstoLocallyUniformlyWithout fImpl_l f)
    (hTLU_u : TendstoLocallyUniformlyWithout fImpl_u f)
    (x : ComputableℝSeq) : ComputableℝSeq :=
  mk
  (x := f x.val)
  (lub := fun n ↦ fImpl n (x.lub n))
  (hcl := by
    obtain ⟨w, _⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_l f hTLU_l hf x.lb
    simp_rw [hImplDef]
    exact w
  )
  (hcu := by
    obtain ⟨w, _⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_u f hTLU_u hf x.ub
    simp_rw [hImplDef]
    exact w
  )
  (hlb := fun n ↦ by simp_rw [hImplDef]; exact hlb n (x.lub n) x.val ⟨x.hlb n, x.hub n⟩)
  (hub := fun n ↦ by simp_rw [hImplDef]; exact hub n (x.lub n) x.val ⟨x.hlb n, x.hub n⟩)
  (heq := by
    obtain ⟨_, h₁⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_l f hTLU_l hf x.lb
    obtain ⟨_, h₂⟩ := Real_mk_of_TendstoLocallyUniformly' fImpl_u f hTLU_u hf x.ub
    simp only [hImplDef, ← Real.mk_eq]
    rw [lb_eq_ub] at h₁
    exact h₁.trans h₂.symm
  )

namespace Sqrt

theorem boundedSqrt_le_rsqrt (y : ℚ) (n : ℕ) (b : ℕ) (hb : 0 < b):
    mkRat (Int.sqrt (y.num * b^n)) ((y.den * b^n).sqrt + 1) ≤ Real.sqrt y := by
  simp only [Rat.mkRat_eq_div, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one]
  rify
  by_cases hy : y ≤ 0
  · have h₁ : √↑y = 0 := by
      rw [Real.sqrt_eq_zero']
      exact Rat.cast_nonpos.mpr hy
    have h₂ : Int.sqrt (y.num * b ^ n) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr hy) (by positivity)
    simp [h₁, h₂]
  push_neg at hy
  rw [Rat.cast_def, Real.sqrt_div' _ (Nat.cast_nonneg' y.den)]
  conv_rhs =>
    equals √(↑(y.num * b^n)) / √(↑(y.den * b^n)) =>
      field_simp
      ring_nf
  apply div_le_div₀
  · exact Real.sqrt_nonneg _
  · convert Real.nat_sqrt_le_real_sqrt
    have h₄ : 0 < y.num * b ^ n := by positivity
    have := Int.toNat_of_nonneg h₄.le
    rify at this
    rw [this]
    norm_cast
  · simp [← Nat.ne_zero_iff_zero_lt, Nat.sqrt_eq_zero]
    positivity
  · exact Real.real_sqrt_le_nat_sqrt_succ

theorem rsqrt_le_boundedSqrt (y : ℚ) (n : ℕ) (b : ℕ) (hb : 0 < b):
    Real.sqrt y ≤ mkRat (Int.sqrt (y.num * b^n) + 1) (y.den * b^n).sqrt := by
  simp only [Rat.mkRat_eq_div, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one]
  rify
  by_cases hy : y ≤ 0
  · have h₁ : √↑y = 0 := by
      rw [Real.sqrt_eq_zero']
      exact Rat.cast_nonpos.mpr hy
    have h₂ : Int.sqrt (y.num * b ^ n) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr hy) (by positivity)
    simp [h₁, h₂]
  push_neg at hy
  rw [Rat.cast_def, Real.sqrt_div' _ (Nat.cast_nonneg' y.den)]
  conv_lhs =>
    equals √(↑(y.num * b^n)) / √(↑(y.den * b^n)) =>
      field_simp
      ring_nf
  apply div_le_div₀
  · have h₁ : 0 < (y.num * b ^ n).sqrt := by
      suffices 0 < Nat.sqrt (Int.toNat (y.num) * b ^ n) by
        rw [Int.sqrt.eq_1]
        norm_cast
        convert this
        conv_rhs => apply (Int.toNat_ofNat _).symm
        push_cast
        congr
        exact (Int.toNat_of_nonneg ((Rat.num_pos.mpr hy).le)).symm
      by_contra h₁
      simp [← Nat.ne_zero_iff_zero_lt, Nat.sqrt_eq_zero, hy, hb.ne'] at h₁
    positivity
  · convert Real.real_sqrt_le_nat_sqrt_succ
    have h₄ : 0 < y.num * b ^ n := by positivity
    have := Int.toNat_of_nonneg h₄.le
    rify at this
    rw [this]
    norm_cast
  · simp [← Nat.ne_zero_iff_zero_lt, Nat.sqrt_eq_zero, hb.ne']
  · exact Real.nat_sqrt_le_real_sqrt

/-- A version of square roots for rational intervals, that give an interval containing the actual
 square root, that are at most b^-n wider than the true interval. -/
def boundedSqrt (x : ℚInterval) (n : ℕ) (b : ℕ) (hb : 0 < b) : ℚInterval :=
  ⟨⟨
    let q := x.fst;
    mkRat (Int.sqrt (q.num * b^n)) ((q.den * b^n).sqrt + 1),
    let q := x.snd;
    mkRat (Int.sqrt (q.num * b^n) + 1) (q.den * b^n).sqrt⟩,
  by
    dsimp
    rify
    trans Real.sqrt (x.snd)
    · trans Real.sqrt (x.fst)
      · apply boundedSqrt_le_rsqrt _ _ _ hb
      · apply Real.sqrt_le_sqrt
        exact_mod_cast x.2
    · apply rsqrt_le_boundedSqrt _ _ _ hb
    ⟩

def sqrtq (x : ℚInterval) (n : ℕ) : ℚInterval :=
  --shortcut with an if to slightly speed things up
  if x.snd ≤ 0 then 0 else boundedSqrt x n 10 (by norm_num)

theorem lb_le_sqrt_lb (q : ℚInterval) (n : ℕ) : (sqrtq q n).fst ≤ Real.sqrt q.fst := by
  rw [sqrtq]
  split_ifs with h
  · simp
  · apply boundedSqrt_le_rsqrt q.toProd.1
    norm_num

theorem lb_le_sqrt (x : ComputableℝSeq) (n : ℕ) : (sqrtq (x.lub n) n).fst ≤ x.val.sqrt := by
  trans Real.sqrt (x.lub n).fst
  · apply lb_le_sqrt_lb
  · exact Real.sqrt_le_sqrt (x.hlb n)

theorem sqrt_ub_le_ub (q : ℚInterval) (n : ℕ) : Real.sqrt q.snd ≤ (sqrtq q n).snd := by
  rw [sqrtq]
  split_ifs with h
  · have := Real.sqrt_eq_zero'.mpr (Rat.cast_nonpos.mpr h)
    simp [this]
  · apply rsqrt_le_boundedSqrt q.toProd.2
    norm_num

theorem sqrt_le_ub (x : ComputableℝSeq) (n : ℕ) : x.val.sqrt ≤ (sqrtq (x.lub n) n).snd  := by
  trans Real.sqrt (x.lub n).toProd.2
  · apply Real.sqrt_le_sqrt
    exact x.hub n
  · apply sqrt_ub_le_ub

/-- This isn't actually true as written, oops. The error term depends on q -/
theorem sqrt_lb_le_lb_add (x : ComputableℝSeq) (n : ℕ) :
    Real.sqrt (x.lub n).fst ≤ (sqrtq (x.lub n) n).fst + (1/2^n) := by
  sorry

theorem ub_sub_le_sqrt (x : ComputableℝSeq) (n : ℕ) : (sqrtq (x.lub n) n).snd - (1/2^n) ≤ x.val.sqrt := by
  sorry

theorem lb_val_eq_sqrt_some (y : ℚInterval) : ∃ (h : IsCauSeq abs (fun n ↦ (sqrtq y n).fst)),
    Real.mk ⟨_, h⟩ = Real.sqrt y.fst := by
  apply Real.of_near
  /-
  have hc : ∀ (y : ℚInterval), IsCauSeq abs (fun n ↦ (Sqrt.lub y n).fst) := by
    --todo: pull out into own lemma
    intro y ε hε
    use (Int.clog 2 (1 / ε)).toNat
    intro j hj
    have hclog := Int.self_le_zpow_clog (Nat.one_lt_two) (1 / ε)
    sorry
  -/
  sorry

theorem lb_val_eq_sqrt (x : ComputableℝSeq) : ∃ (h : IsCauSeq abs (fun n ↦ (sqrtq (x.lub n) n).fst)),
    Real.mk ⟨_, h⟩ = x.val.sqrt := by
  /-
  fun n ↦ (x.lub n).fst   approaches x.val
  fun n ↦ Real.sqrt (x.lub n).fst    approaches Real.sqrt (x.val)

  ∀ y, (sqrtq y).fst   approaches Real.sqrt (y.fst) with error as 1/2^n
  -/

  apply Real.of_near
  intro ε hε

  obtain ⟨ε', hε', hε₂⟩ := exists_rat_btwn hε
  rw [Rat.cast_pos] at hε'
  suffices ∃ i, ∀ j ≥ i, |↑(sqrtq (x.lub j) j).toProd.1 - √x.val| < ε' by
    peel this
    exact gt_trans hε₂ this
  clear ε hε hε₂

  have heq₁ : Real.mk ⟨_, x.hcl⟩ = x.val := x.val_eq_mk_lb.symm
  have heq₂ : ∀ (i : ℕ), Real.mk ⟨fun n => (sqrtq (x.lub i) n).toProd.1,
      (lb_val_eq_sqrt_some (x.lub i)).rec (fun w _ ↦ w)⟩ = Real.sqrt (.mk ⟨_, x.hcl⟩)  := by
    sorry
  rw [heq₁] at heq₂
  clear heq₁

  obtain ⟨i₁, hi₁⟩ := x.hcl (ε' / 2) (half_pos hε')

  obtain ⟨hc, hc₂⟩ := lb_val_eq_sqrt_some (x.lub i₁)
  have hc₃ := cauchy_real_mk ⟨_, hc⟩
  clear hc₂

  obtain ⟨i₂, hi₂⟩ := hc₃ (ε' / 2) (half_pos (Rat.cast_pos.mpr hε'))
  clear hc₃

  dsimp at hi₁ hi₂
  use max i₁ i₂
  intro j hj
  specialize hi₁ j (le_of_max_le_left hj)
  specialize hi₂ j (le_of_max_le_right hj)
  clear hj i₂

  rw [heq₂ i₁] at hi₂
  clear heq₂

  sorry

theorem wanted_1 :
    TendstoLocallyUniformlyWithout
    (fun n (x : ℚ) => ↑((fun n q =>
      mkRat (Int.sqrt (q.num * 10 ^ n)) ((q.den * 10 ^ n).sqrt + 1)) n x))
    (fun q => √↑q) := by
  sorry

theorem wanted_2 :
    TendstoLocallyUniformlyWithout
    (fun n (x : ℚ) => ↑((fun n q =>
      if q ≤ 0 then 0 else mkRat (Int.sqrt (q.num * 10 ^ n) + 1) (q.den * 10 ^ n).sqrt) n x))
    (fun q => √↑q) := by
  sorry

def sqrt : ComputableℝSeq → ComputableℝSeq :=
  of_TendstoLocallyUniformly_Continuous
  (f := Real.sqrt)
  (hf := Real.continuous_sqrt)
  (fImpl := fun n q ↦ sqrtq q n)
  (fImpl_l := fun n q ↦ mkRat (Int.sqrt (q.num * 10^n)) ((q.den * 10^n).sqrt + 1))
  (fImpl_u := fun n q ↦ if q ≤ 0 then 0 else mkRat (Int.sqrt (q.num * 10^n) + 1) (q.den * 10^n).sqrt)
  (hImplDef := by
    rintro n ⟨⟨q₁, q₂⟩, hq⟩
    dsimp [sqrtq]
    split_ifs
    · have h : Int.sqrt (q₁.num * 10 ^ n) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr (by linarith)) (by positivity)
      simp [h]; rfl
    · rfl
  )
  (hTLU_l := wanted_1)
  (hTLU_u := wanted_2)
  (hlb := by
    intro n ⟨⟨q₁, q₂⟩, hq⟩ x ⟨hx₁, hx₂⟩
    have := lb_le_sqrt_lb ⟨⟨q₁, q₂⟩, hq⟩ n
    rw [sqrtq, boundedSqrt] at this
    split_ifs at this with h
    · have h0 : Int.sqrt (q₁.num * 10 ^ n) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr (by linarith)) (by positivity)
      simp [h0]
    · exact le_trans this (Real.sqrt_le_sqrt hx₁)
    )
  (hub := by
    intro n ⟨⟨q₁, q₂⟩, hq⟩ x ⟨hx₁, hx₂⟩
    dsimp at *
    split_ifs with h
    · suffices √x = 0 by
        simp [h, this]
      rw [Real.sqrt_eq_zero']
      exact le_trans hx₂ (Rat.cast_nonpos.mpr h)
    · have := sqrt_ub_le_ub ⟨⟨q₁, q₂⟩, hq⟩ n
      rw [sqrtq, boundedSqrt, if_neg h] at this
      exact le_trans (Real.sqrt_le_sqrt hx₂) this
  )

instance instComputableSqrt (x : ℝ) [hx : IsComputable x] : IsComputable (x.sqrt) :=
  .lift (Real.sqrt) sqrt (fun v ↦ val_eq_mk_lb (sqrt _) ▸ (lb_val_eq_sqrt v).rec (fun _ h ↦ h)) hx

instance instComputableSqrtTwoAddSeries (x : ℝ) [hx : IsComputable x] (n : ℕ) :
    IsComputable (Real.sqrtTwoAddSeries x n) :=
  n.rec hx (fun _ _ ↦ instComputableSqrt _)

example : Real.sqrt (1 + 1/4) > 2 + Real.sqrt 3 - Real.sqrt 7 := by
  native_decide

end Sqrt

section Pi

/-- See theorem Real.pi_gt_sqrtTwoAddSeries in Mathlib -/
def pi_lb (n : ℕ) : ℚ :=
  let TwoSubSqrt2SeriesN := (inferInstance : IsComputable (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))).seq
  2 ^ (n + 1) * TwoSubSqrt2SeriesN.lb n

/-- See theorem Real.pi_gt_sqrtTwoAddSeries in Mathlib -/
def pi_ub (n : ℕ) : ℚ :=
  let TwoSubSqrt2SeriesN := (inferInstance : IsComputable (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))).seq
  2 ^ (n + 1) * TwoSubSqrt2SeriesN.ub n + 1 / 4 ^ n

--100ms for 10^-40 precision
-- #time #eval! Rat.toDecimal (prec := 40) (pi_ub 100 - 3.14159265358979323846264338327950288419716939937510)

end Pi

/-
The Taylor series error formula, where fN is the nth-order approximation:
f(x) - fN(x) = 1/(n+1)! * f^(n+1)(c) * x^(n+1) for some c in [0,x].

For exp:
exp(x) - expN(x) = 1/(n+1)! * exp(c) * x^(n+1)

|exp(x) - expN(x)| = |1/(n+1)! * exp(c) * x^(n+1)|
  <= |1/(n+1)! * exp(x) * x^(n+1)|

|expN(x) - exp(x)| <= 1/(n+1)! * exp(x) * x^(n+1)

expN(x) <= exp(x) + 1/(n+1)! * exp(x) * x^(n+1)

expN(x) <= exp(x) (1 + x^(n+1) / (n+1)!)

∴ exp(x) >= expN(x) / (1 + x^(n+1) / (n+1)!)

likewise,

exp(x) <= expN(x) / (1 - x^(n+1) / (n+1)!)
 if (1 - x^(n+1) / (n+1)!) >= 0, otherwise 0
-/

-- namespace Exp

-- --valid lower bound when 0 ≤ x. CauSeq that converges to Real.exp x from below.
-- def exp_lb' (x : ℚ) (n : ℕ) : ℚ :=
--   if 1 < x then
--     (exp_lb' (x/2) n)^2
--   else
--     -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
--     let series : ℚ := (List.range n).foldr (fun n v ↦ 1 + (x * v) / (n+1)) 1
--     series
--   termination_by (x.ceil).toNat
--   decreasing_by decreasing_with
--   constructor
--   · sorry
--   · sorry

-- --valid upper bound when 0 ≤ x. CauSeq that converges to Real.exp x from above.
-- def exp_ub' (x : ℚ) (n : ℕ) : ℚ :=
--   if 1/2 < x then
--     (exp_ub' (x/2) n)^2
--   else
--     -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
--     let series : ℚ := (List.range n).foldr (fun n v ↦ 1 + (x * v) / (n+1)) 1
--     let den_ub : ℚ := 1 - x^(n+1) / (n+1).factorial
--     series / den_ub
--   termination_by (x.ceil).toNat
--   decreasing_by decreasing_with
--   sorry

-- def exp_lb (x : ℚ) : CauSeq ℚ abs :=
--   if h : 0 ≤ x then
--     ⟨exp_lb' x, sorry⟩
--   else
--     ⟨1 / exp_ub' (-x), sorry⟩

-- def exp_ub (x : ℚ) : CauSeq ℚ abs :=
--   if h : 0 ≤ x then
--     ⟨exp_ub' x, sorry⟩
--   else
--     ⟨1 / exp_lb' (-x), sorry⟩

-- theorem exp_lb_is_lb (x : ℚ) : ∀ n, exp_lb x n ≤ Real.exp x :=
--   sorry

-- theorem exp_ub_is_ub (x : ℚ) : ∀ n, exp_ub x n ≥ Real.exp x :=
--   sorry

-- theorem exp_lb_val (x : ℚ) : Real.mk (exp_lb x) = Real.exp x :=
--   sorry

-- theorem exp_ub_val (x : ℚ) : Real.mk (exp_ub x) = Real.exp x :=
--   sorry

-- def exp_lub (x : ℚInterval) (n : ℕ) : ℚInterval :=
--   ⟨⟨exp_lb x.fst n, exp_ub x.snd n⟩,
--     Rat.cast_le.mp (by calc
--       _ ≤ Real.exp x.fst := exp_lb_is_lb _ n
--       _ ≤ Real.exp x.snd := Real.exp_monotone (Rat.cast_le.mpr x.2)
--       _ ≤ (exp_ub x.toProd.2) n := exp_ub_is_ub _ n
--     )⟩

-- -- theorem causeq_eq_self (s : CauSeq ℚ abs) {h : IsCauSeq abs s} : ⟨(s : ℕ → ℚ), h⟩ = s :=
--   -- rfl

-- end Exp

-- -- theorem exp_lb_correct

-- def exp (x : ComputableℝSeq) : ComputableℝSeq where
--   lub n := Exp.exp_lub (x.lub n) n
--   hcl := sorry
--   hcu := sorry
--   hlub n := sorry
--   heq' := sorry

-- theorem exp_eq_exp (x : ComputableℝSeq) : (exp x).val = Real.exp (x.val) := by
--   sorry

-- end ComputableℝSeq

-- namespace Computableℝ

-- def exp : Computableℝ → Computableℝ :=
--   mapℝ ComputableℝSeq.exp ComputableℝSeq.exp_eq_exp

-- #eval (exp (-1)).val

-- #eval (-exp (-1)).val

-- #eval -(-exp (exp (exp 0.1))).val

-- #eval ((List.range 11).map (exp (exp (exp 0.1))).unquot.lb).map Rat.toDecimal

-- #eval ((List.range 11).map (exp (exp (exp 0.1))).unquot.ub).map Rat.toDecimal

-- #eval ((List.range 20).map (fun n ↦ ComputableℝSeq.Exp.exp_lb (5) n)).map Rat.toDecimal

end ComputableℝSeq
