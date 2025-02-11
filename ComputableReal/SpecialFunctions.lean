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

@[simp]
theorem val_of_TendstoLocallyUniformly_Continuous (f) (hf : Continuous f) (fI fl fu h₁ h₂ h₃ h₄ h₅ a)
  : (of_TendstoLocallyUniformly_Continuous hf fI fl fu h₁ h₂ h₃ h₄ h₅ a).val =
    f a.val :=
  ComputableℝSeq.mk_val_eq_val

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
  if x.snd ≤ 0 then 0 else boundedSqrt x n 4 (by norm_num)

theorem lb_le_sqrt_lb (q : ℚInterval) (n : ℕ) : (sqrtq q n).fst ≤ Real.sqrt q.fst := by
  rw [sqrtq]
  split_ifs with h
  · simp
  · apply boundedSqrt_le_rsqrt q.toProd.1
    norm_num

-- theorem lb_le_sqrt (x : ComputableℝSeq) (n : ℕ) : (sqrtq (x.lub n) n).fst ≤ x.val.sqrt := by
--   trans Real.sqrt (x.lub n).fst
--   · apply lb_le_sqrt_lb
--   · exact Real.sqrt_le_sqrt (x.hlb n)

theorem sqrt_ub_le_ub (q : ℚInterval) (n : ℕ) : Real.sqrt q.snd ≤ (sqrtq q n).snd := by
  rw [sqrtq]
  split_ifs with h
  · have := Real.sqrt_eq_zero'.mpr (Rat.cast_nonpos.mpr h)
    simp [this]
  · apply rsqrt_le_boundedSqrt q.toProd.2
    norm_num

-- theorem sqrt_le_ub (x : ComputableℝSeq) (n : ℕ) : x.val.sqrt ≤ (sqrtq (x.lub n) n).snd  := by
--   trans Real.sqrt (x.lub n).toProd.2
--   · apply Real.sqrt_le_sqrt
--     exact x.hub n
--   · apply sqrt_ub_le_ub

/-- This equality is a generally true way to "split a denominator", but is particularly useful
as an approximation when ε is small compared to y, and we wish to approximate
`x / (y + ε)` with `x / y`. -/
lemma denom_err (x y ε : ℝ) (hy : y ≠ 0) (hyε : y + ε ≠ 0 ) :
    x / (y + ε) = x / y - (x / y) * ε / (y + ε) := by
  field_simp
  ring_nf

theorem sqrt_lb_le_lb_add (q : ℚ) (n : ℕ) :
    Real.sqrt q ≤ (sqrtq q n).fst + 2 * Real.sqrt q / 2^n := by
  rw [sqrtq, boundedSqrt]
  split_ifs with h
  · have h₁ : √↑q = 0 := Real.sqrt_eq_zero'.mpr (Rat.cast_nonpos.mpr h)
    simp [h₁]
  · dsimp
    clear h
    nth_rewrite 4 [← Rat.mkRat_self q]
    nth_rewrite 1 [← Rat.mkRat_self q]
    simp only [Rat.mkRat_eq_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Nat.cast_nonneg,
      Real.sqrt_div', Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one, one_div]
    simp [Rat.cast, QInterval.instRatCastQInterval, NonemptyInterval.toProd]
    have hd := Rat.den_pos q
    generalize q.num = x, q.den = y at *
    clear q
    rcases le_or_lt x 0 with h|h
    · have h₁ : √↑x = 0 := by
        rw [Real.sqrt_eq_zero']
        exact Int.cast_nonpos.mpr h
      have h₂ : Int.sqrt (x * 4 ^ n) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg h (by positivity)
      simp [h₁, h₂]
    · obtain ⟨z,hz⟩ := Int.eq_ofNat_of_zero_le h.le
      subst x
      conv_rhs =>
        enter [1,1,1,1]
        tactic => norm_cast
      rw [Int.sqrt_natCast]
      simp only [Int.cast_natCast]
      /-
      x/(y+ε) = (x/y) - (x/y - x/(y+ε)) = (x/y) - x*(1/y - 1/(y+ε)) = x/y - x*((y+ε) - y)/(y*(y+ε))
       = x/y - (x/y)*(ε/(y+ε)). The error is thus at most (x/y)*ε/(y+ε), which is upper bounded by
       ≤ (sqrt q) * 1 / 4^n.
      Similarly for the numerator.
      -/
      have h₁ := @Real.floor_real_sqrt_eq_nat_sqrt (z * 4^n)
      rify at h₁
      rw [← h₁, ← Int.self_sub_fract]
      clear h₁
      have h₂ := Int.fract_lt_one √(↑z * 4 ^ n)
      have h₃ := Int.fract_nonneg √(↑z * 4 ^ n)
      generalize Int.fract √(↑z * 4 ^ n) = ε₁ at *

      have h₁ := @Real.floor_real_sqrt_eq_nat_sqrt (y * 4^n)
      rify at h₁
      rw [← h₁, ← Int.self_sub_fract]
      clear h₁
      have h₄ := Int.fract_lt_one √(↑y * 4 ^ n)
      have h₅ := Int.fract_nonneg √(↑y * 4 ^ n)
      rw [sub_add_comm]
      rw [← sub_sub_cancel 1 (Int.fract _)] at h₄ h₅
      generalize 1 - Int.fract √(↑y * 4 ^ n) = ε₂ at *
      simp only [sub_lt_self_iff, sub_nonneg] at h₄ h₅

      rw [Real.sqrt_mul', Real.sqrt_mul',
        show (4 ^ n = ((2 ^ n) ^ 2 : ℝ)) by norm_cast; rw [Nat.pow_right_comm]]
      rotate_left; positivity; positivity
      simp only [Nat.ofNat_nonneg, pow_nonneg, Real.sqrt_sq]

      rw [_root_.add_comm ε₂, sub_div, denom_err]
      rotate_left; positivity; positivity

      rw [show √↑z * 2 ^ n / (√↑y * 2 ^ n) = √↑z / √↑y by field_simp; ring_nf]
      suffices (√↑z / √↑y * ε₂ / (√↑y * 2 ^ n + ε₂) ≤ √↑z / √↑y / 2 ^ n)
        ∧ (ε₁ / (√↑y * 2 ^ n + ε₂) ≤ √↑z / √↑y / 2 ^ n) by
        rcases this
        rw [← mul_div 2]
        linarith

      replace h : 1 ≤ √↑z := Real.one_le_sqrt.mpr (by norm_cast at h ⊢)
      replace hd : 1 ≤ √↑y := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hd)

      constructor
      · apply div_le_div₀
        · positivity
        · exact mul_le_of_le_one_right (by positivity) h₅
        · positivity
        · trans √↑y * 2 ^ n
          · exact le_mul_of_one_le_left (by positivity) hd
          · exact le_add_of_nonneg_right h₄.le
      · rw [div_div]
        apply div_le_div₀
        · positivity
        · exact h₂.le.trans h
        · positivity
        · exact le_add_of_nonneg_right h₄.le

theorem ub_sub_le_sqrt (x : ComputableℝSeq) (n : ℕ) :
    (sqrtq (x.lub n) n).snd - (1/2^n) ≤ x.val.sqrt := by
  sorry

theorem TLUW_lower : TendstoLocallyUniformlyWithout
    (fun n (x : ℚ) => ↑((fun n q =>
      mkRat (Int.sqrt (q.num * 4 ^ n)) ((q.den * 4 ^ n).sqrt + 1)) n x))
    (fun q => √↑q) := by
  rw [TendstoLocallyUniformlyWithout]
  intro ε hε x
  sorry

theorem TLUW_upper : TendstoLocallyUniformlyWithout
    (fun n (x : ℚ) => ↑((fun n q =>
      if q ≤ 0 then 0 else mkRat (Int.sqrt (q.num * 4 ^ n) + 1) (q.den * 4 ^ n).sqrt) n x))
    (fun q => √↑q) := by
  rw [TendstoLocallyUniformlyWithout]
  intro ε hε x
  sorry

def sqrt : ComputableℝSeq → ComputableℝSeq :=
  of_TendstoLocallyUniformly_Continuous
  (f := Real.sqrt)
  (hf := Real.continuous_sqrt)
  (fImpl := fun n q ↦ sqrtq q n)
  (fImpl_l := fun n q ↦ mkRat (Int.sqrt (q.num * 4^n)) ((q.den * 4^n).sqrt + 1))
  (fImpl_u := fun n q ↦ if q ≤ 0 then 0 else mkRat (Int.sqrt (q.num * 4^n) + 1) (q.den * 4^n).sqrt)
  (hImplDef := by
    rintro n ⟨⟨q₁, q₂⟩, hq⟩
    dsimp [sqrtq]
    split_ifs
    · have h : Int.sqrt (q₁.num * 4 ^ n) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr (by linarith)) (by positivity)
      simp [h]; rfl
    · rfl
  )
  (hTLU_l := TLUW_lower) (hTLU_u := TLUW_upper)
  (hlb := by
    intro n ⟨⟨q₁, q₂⟩, hq⟩ x ⟨hx₁, hx₂⟩
    have := lb_le_sqrt_lb ⟨⟨q₁, q₂⟩, hq⟩ n
    rw [sqrtq, boundedSqrt] at this
    split_ifs at this with h
    · have h0 : Int.sqrt (q₁.num * 4 ^ n) = 0 := by
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
  .lift (Real.sqrt) sqrt (by apply val_of_TendstoLocallyUniformly_Continuous) hx

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
