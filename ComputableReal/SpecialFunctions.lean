import ComputableReal.IsComputable
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped QInterval

namespace Rat

def toDecimal (q : ℚ) (prec : ℕ := 20):=
  (q.floor.repr).append <| ".".append <| (10^prec * (q - q.floor)).floor.repr.leftpad prec '0'

end Rat

namespace ComputableℝSeq

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
def boundedSqrt (x : ℚInterval) (n : ℕ) (b : ℕ) (hb : 0 < b): ℚInterval :=
  ⟨⟨
    let q := x.fst;
    mkRat (Int.sqrt (q.num * b^n)) ((q.den * b^n).sqrt + 1),
    let q := x.snd;
    mkRat (Int.sqrt (q.num * b^n) + 1) (q.den * b^n).sqrt⟩,
  by
    sorry
    -- dsimp
    -- rify
    -- trans Real.sqrt (x.snd)
    -- · trans Real.sqrt (x.fst)
    --   · apply boundedSqrt_le_rsqrt _ _ _ hb
    --   · apply Real.sqrt_le_sqrt
    --     exact_mod_cast x.2
    -- · apply rsqrt_le_boundedSqrt _ _ _ hb
    ⟩

def lub (x : ℚInterval) (n : ℕ) : ℚInterval :=
  if x.snd ≤ 0 then 0 else boundedSqrt x n 10 (by norm_num)

theorem lb_IsCauSeq (x : ComputableℝSeq) : IsCauSeq abs (fun n ↦ (Sqrt.lub (x.lub n) n).fst) := by
  sorry

theorem ub_IsCauSeq (x : ComputableℝSeq) : IsCauSeq abs (fun n ↦ (Sqrt.lub (x.lub n) n).snd) := by
  sorry

theorem lb_le_sqrt (x : ComputableℝSeq) (n : ℕ) : (Sqrt.lub (x.lub n) n).fst ≤ x.val.sqrt := by
  sorry

theorem sqrt_le_ub (x : ComputableℝSeq) (n : ℕ) : x.val.sqrt ≤ (Sqrt.lub (x.lub n) n).snd  := by
  sorry

theorem lb_val_eq_sqrt (x : ComputableℝSeq) : Real.mk ⟨_, lb_IsCauSeq x⟩ = x.val.sqrt := by
  sorry

theorem ub_val_eq_sqrt (x : ComputableℝSeq) : Real.mk ⟨_, ub_IsCauSeq x⟩ = x.val.sqrt := by
  sorry

def sqrt (x : ComputableℝSeq) : ComputableℝSeq where
  lub n := Sqrt.lub (x.lub n) n
  hcl := lb_IsCauSeq x
  hcu := ub_IsCauSeq x
  heq' := by
    rw [← Real.mk_eq]
    exact (lb_val_eq_sqrt x).trans (ub_val_eq_sqrt x).symm
  hlub n := ⟨lb_val_eq_sqrt x ▸ lb_le_sqrt x n, lb_val_eq_sqrt x ▸ sqrt_le_ub x n⟩

instance instComputableSqrt (x : ℝ) [hx : IsComputable x] : IsComputable (x.sqrt) :=
  .lift (Real.sqrt) sqrt (val_eq_mk_lb (sqrt _) ▸ lb_val_eq_sqrt ·) hx

/- Testing -/
@[simp]
noncomputable def sqrtSeries (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => √(sqrtSeries x n)

instance instComputableSqrtSeries (x : ℝ) [hx : IsComputable x] (n : ℕ) :
    IsComputable (sqrtSeries x n) :=
  n.rec hx (fun _ _ ↦ instComputableSqrt _)
/-   end testing -/

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

--this is fast, with instComputableSqrtTwoAddSeries it's slow, so the trouble is actually addition. Oops
#time #eval! ((List.range 10).map (inferInstance : IsComputable (Sqrt.sqrtSeries 0 13)).seq.lb).map Rat.toDecimal

-- #eval! ((List.range 12).map pi_lb).map (fun q ↦ Rat.toDecimal (3.14159265358979 - q))
-- #eval! ((List.range 12).map pi_ub).map (fun q ↦ Rat.toDecimal (q - 3.14159265358979))

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
