import ComputableReal.IsComputable
import ComputableReal.SpecialFunctions.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Log

namespace ComputableℝSeq

open scoped QInterval

namespace Cos

/-
We'll divide `x` by a suitably large power of 2, and then apply
`cos 2x = 2 * (cos x)^2 - 1` to double it back up. This is similar
to exponentiation by squaring, but `·^(2^n)` is easy to express directly,
but now we need `x ↦ 2x^2 - 1` iterated `n` times. We define this function
(on intervals) and prove its basic properties.

Then we use Taylor expansion on cosine to get a good approximation when
‖x‖ ≤ 1.
-/

/-- Square a ℚInterval. Different from `x^2 := x * x`, which can have negative lower bounds -
although it would be nice to upstream this in the future. -/
def sq (x : ℚInterval) : ℚInterval :=
  if h₁ : x.snd < 0 then
    ⟨⟨x.snd^2, x.fst^2⟩, by dsimp; nlinarith [x.fst_le_snd]⟩
  else if h₂ : 0 < x.fst then
    ⟨⟨x.fst^2, x.snd^2⟩, by dsimp; nlinarith [x.fst_le_snd]⟩
  else
    ⟨⟨0, x.fst^2 ⊔ x.snd^2⟩, by simp only [le_sup_iff]; apply Or.inl; positivity⟩

/-- The `sq` is a valid bound on (real) squares. -/
theorem mem_sq (x : ℚInterval) : ∀ (r : ℝ), r ∈ x → r^2 ∈ sq x := by
  rintro r ⟨hr₁, hr₂⟩
  apply And.intro
  all_goals (
    simp_rw [sq, apply_dite (α := ℚInterval)]
    split_ifs with h₁ h₂
    all_goals (
      rify at *
      try push_cast
      try nlinarith
    )
  )
  simp only [le_sup_iff]
  cases lt_or_ge r 0
  · left
    nlinarith
  · right
    nlinarith

theorem sq_interval_nonneg (x : ℚInterval) : 0 ≤ (sq x).fst ∧ 0 ≤ (sq x).snd := by
  suffices 0 ≤ (sq x).fst by
    use ‹_›
    linarith [(sq x).fst_le_snd]
  dsimp [sq]
  split_ifs with h₁ h₂
  · apply sq_nonneg _
  · apply sq_nonneg _
  · rfl

theorem sq_interval_max {a : ℚ} (x : ℚInterval) (hx : -a ≤ x.fst ∧ x.snd ≤ a) :
    (sq x).fst ≤ a^2 ∧ (sq x).snd ≤ a^2 := by
  suffices (sq x).snd ≤ a^2 by
    exact ⟨(sq x).fst_le_snd.trans this, this⟩
  dsimp [sq]
  have h : x.toProd.1 ^ 2 ≤ a ^ 2 ∧ x.toProd.2 ^ 2 ≤ a ^ 2 :=
    ⟨sq_le_sq' hx.1 (x.fst_le_snd.trans hx.2),
      sq_le_sq' (hx.1.trans x.fst_le_snd) hx.2⟩
  split_ifs with h₁ h₂
  · exact h.left
  · exact h.right
  · exact sup_le_iff.mpr h

/-- The map `x ↦ 2x^2 - 1`, on intervals. In particular, if `cos θ ∈ x`, then
`cos 2θ ∈ doubling_map x`. -/
def doubling_map (x : ℚInterval) : ℚInterval :=
  2 • sq x - 1

/-- The doubling map maps `cos θ` bounding intervals to `cos 2θ` intervals. -/
theorem doubling_map_cos (x : ℚInterval) (θ : ℝ) (h : Real.cos θ ∈ x) :
    Real.cos (2 * θ) ∈ doubling_map x := by
  rw [Real.cos_two_mul, doubling_map]
  replace h := mem_sq x _ h
  rw [QInterval.mem_qinterval_iff_and] at h ⊢
  simpa using h

theorem doubling_map_cos_pow (x : ℚInterval) (n : ℕ) (θ : ℝ) (h : Real.cos θ ∈ x) :
    Real.cos (2^n * θ) ∈ doubling_map^[n] x := by
  induction n
  · simpa using h
  · rename_i n ih
    simp only [n.add_comm 1, Function.iterate_add_apply doubling_map 1 n, Function.iterate_one]
    rw [pow_add, pow_one, mul_assoc]
    exact doubling_map_cos (doubling_map^[n] x) (2 ^ n * θ) ih

/-- Assuming the original interval is between [-1,1], all iterates of `doubling_map`
  are between [-1,1]. -/
theorem doubling_map_abs_le_1 (x : ℚInterval) (hx : -1 ≤ x.fst ∧ x.snd ≤ 1) :
    ∀ n, -1 ≤ (doubling_map^[n] x).fst ∧ (doubling_map^[n] x).snd ≤ 1 := by
  intro n
  induction n
  · exact hx
  · rename_i n ih
    simp only [n.add_comm 1, Function.iterate_add_apply doubling_map 1 n, Function.iterate_one]
    generalize doubling_map^[n] x = y at ih ⊢
    rw [doubling_map, sq]
    obtain ⟨⟨y₁, y₂⟩, hy : y₁ ≤ y₂⟩ := y
    change -1 ≤ y₁ ∧ y₂ ≤ 1 at ih
    simp only [apply_dite, NonemptyInterval.fst_sub, NonemptyInterval.toProd_nsmul, Prod.smul_mk,
      nsmul_eq_mul, Nat.cast_ofNat, smul_zero, NonemptyInterval.toProd_one, Prod.snd_one,
      neg_le_sub_iff_le_add, le_add_iff_nonneg_left, NonemptyInterval.snd_sub, Prod.fst_one,
      tsub_le_iff_right]
    split
    · constructor
      · positivity
      · nlinarith
    split
    · constructor
      · positivity
      · nlinarith
    · use le_rfl
      suffices (y₁ ^ 2 ⊔ y₂ ^ 2) ≤ 1 by linarith
      rw [sup_le_iff]
      constructor <;> nlinarith

/-- The `doubling_map` only increases the width by at most a factor of 4. -/
theorem doubling_map_width_le_four (x : ℚInterval) (hx : -1 ≤ x.fst ∧ x.snd ≤ 1) (ε : ℚ)
    (hε : x.snd ≤ x.fst + ε) : (doubling_map x).snd ≤ (doubling_map x).fst + 4 * ε := by
  rw [doubling_map, sq]
  obtain ⟨⟨y₁, y₂⟩, hy : y₁ ≤ y₂⟩ := x
  dsimp at hx hε ⊢
  rcases lt_trichotomy ε 0 with hε'|hε'|hε'
  · exfalso
    linarith
  · have hy' : y₂ = y₁ := by linarith
    subst y₂ ε
    simp only [max_self, apply_dite, dite_eq_ite, apply_ite Prod.snd, ite_self, nsmul_eq_mul,
      Nat.cast_ofNat, apply_ite Prod.fst, smul_ite, smul_zero, mul_zero, add_zero, ge_iff_le]
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · have : y₁ = 0 := by linarith
      subst y₁
      norm_num
  · simp only [apply_dite, nsmul_eq_mul, Nat.cast_ofNat, smul_zero]
    split_ifs
    · nlinarith
    · nlinarith
    · suffices _ ⊔ _ ≤ 2 * ε by linarith
      rw [sup_le_iff]
      constructor <;> nlinarith

/-- The nth iterate of `doubling_map` increases the width by a factor of at most `4^n`. -/
theorem doubling_map_iterate_width (x : ℚInterval) (hx : -1 ≤ x.fst ∧ x.snd ≤ 1) (ε : ℚ)
    (hε : x.snd ≤ x.fst + ε) :
    ∀ n, (doubling_map^[n] x).snd ≤ (doubling_map^[n] x).fst + 4^n * ε := by
  intro n
  induction n
  · rw [pow_zero, one_mul]
    exact hε
  · rename_i n ih
    rw [n.add_comm 1, Function.iterate_add_apply doubling_map 1 n, Function.iterate_one]
    rw [pow_add, pow_one, mul_assoc]
    exact doubling_map_width_le_four _ (doubling_map_abs_le_1 x hx n) _ ih

private theorem cos_unit_interval_ordered (x : ℚInterval) (hx : -1 ≤ x.toProd.1 ∧ x.toProd.2 ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), (-(sq x).toProd.2) ^ i / ↑(2 * i).factorial ≤
    ∑ i ∈ Finset.range (2 * n + 1), (-(sq x).toProd.1) ^ i / ↑(2 * i).factorial := by
  set x_sq := sq x
  trans ∑ i ∈ Finset.range (2 * n), (-x_sq.toProd.1) ^ i / ↑(2 * i).factorial
  · cases n
    · rfl
    rename_i n
    rw [(by rfl : 2 * (n + 1) = 2 * n + 1 + 1)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have h₁ : ∀ n, (-x_sq.snd) ^ (2 * n + 1) ≤ (-x_sq.fst) ^ (2 * n + 1) := by
      intro n
      simp only [pow_add, pow_mul, pow_one]
      apply mul_le_mul_of_nonneg_of_nonpos'
      · apply pow_le_pow_left₀ (sq_nonneg _)
        simp only [Even.neg_pow (even_two)]
        exact pow_le_pow_left₀ (sq_interval_nonneg x).left x_sq.fst_le_snd 2
      · exact neg_le_neg_iff.mpr x_sq.fst_le_snd
      · simp only [Even.neg_pow (even_two)]
        positivity
      · exact neg_le_neg_iff.mpr (sq_interval_nonneg x).left
    refine add_le_add (add_le_add ?_ (by rfl))
      ((div_le_div_iff_of_pos_right (by positivity)).mpr <| h₁ n)
    induction n
    · rfl
    rename_i n ih
    rw [mul_add, mul_one, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [add_assoc, add_assoc (Finset.sum _ _)]
    refine add_le_add ih ?_
    clear ih
    have hf : ((2 * (2 * n + 1 + 1)).factorial : ℚ)
        = (4 * n + 3) * (4 * n + 4) * ↑(2 * (2 * n + 1)).factorial := by
      rw [mul_add, mul_one, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring_nf
    rw [hf, ← div_div, ← div_div (c := (Nat.factorial _ : ℚ)), ← add_div, ← add_div]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    suffices -x_sq.snd ^ (2 * n + 1) * (1 + (-x_sq.snd) / ((4 * n + 3) * (4 * n + 4))) ≤
      -x_sq.fst ^ (2 * n + 1) * (1 + (-x_sq.fst) / ((4 * n + 3) * (4 * n + 4))) by
      rw [← Odd.neg_pow (odd_two_mul_add_one n), ← Odd.neg_pow (odd_two_mul_add_one n)] at this
      ring_nf at this ⊢
      exact this
    suffices AntitoneOn (fun (x : ℚ) ↦ -x ^ (2 * n + 1) * (1 + -x / ((4 * n + 3) * (4 * n + 4)))) (Set.Icc 0 1) from
      this ⟨(sq_interval_nonneg x).left, (sq_interval_max x hx).left⟩
        ⟨(sq_interval_nonneg x).right, (sq_interval_max x hx).right⟩
        x_sq.fst_le_snd
    suffices AntitoneOn (fun (x : ℝ) ↦ -x ^ (2 * n + 1) * (1 + -x / ((4 * n + 3) * (4 * n + 4)))) (Set.Icc 0 1) by
      intro x hx y hy hxy
      exact_mod_cast (show _ * _ ≤ _ * _ from
        @this x ⟨mod_cast hx.1, mod_cast hx.2⟩ y ⟨mod_cast hy.1, mod_cast hy.2⟩ (mod_cast hxy))
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · fun_prop
    · fun_prop
    · intro p hp
      rw [interior_Icc, Set.mem_Ioo] at hp
      rw [deriv_mul (by fun_prop) (by fun_prop)]
      simp_rw [deriv.neg', deriv_pow]
      rw [deriv_const_add, deriv_div_const, deriv_neg]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        _root_.neg_mul, zero_add, add_tsub_cancel_right, zero_add]
      suffices 0 ≤ ((2 * ↑n + 1) * p ^ (2 * n) * (1 + -p / ((4 * ↑n + 3) * (4 * ↑n + 4)))) +
        (p ^ (2 * n + 1) * (-1 / ((4 * ↑n + 3) * (4 * ↑n + 4)))) by
        linarith
      suffices 0 ≤ p ^ (2 * n) *
          (2 * ↑n + 1 + (2 * ↑n + 2) * (-p / ((4 * ↑n + 3) * (4 * ↑n + 4)))) by
        ring_nf at this ⊢
        exact this
      suffices 0 ≤ 2 * ↑n + 1 + (2 * ↑n + 2) * (-p / ((4 * ↑n + 3) * (4 * ↑n + 4))) by
        rw [pow_mul]
        positivity
      suffices 0 ≤ (2 * ↑n + 1) * ((4 * ↑n + 3) * (4 * ↑n + 4)) + (2 * ↑n + 2) * -p by
        have h₀ : 0 < ((4 * ↑n + 3) * (4 * ↑n + 4) : ℝ) := by positivity
        rw [← div_le_div_iff_of_pos_right h₀, add_div, zero_div] at this
        convert this using 1
        field_simp
      suffices (2 * n + 2) * p ≤ 12 + n * 52 + ↑n ^ 2 * 72 + ↑n ^ 3 * 32 by
        linarith
      trans 2 * n + 2
      · exact mul_le_of_le_one_right (by positivity) hp.2.le
      suffices (0 : ℝ) ≤ 10 + ↑n * 50 + ↑n ^ 2 * 72 + ↑n ^ 3 * 32 by linarith
      positivity
  · rw [Finset.sum_range_succ, le_add_iff_nonneg_right, Even.neg_pow (Even.mul_right even_two n)]
    have h_y_sq := (sq_interval_nonneg x).left
    positivity

/-- A bound on `cos x` that works when `x` is in the range `[-1,1]`. -/
private def cos_unit_interval (x : ℚInterval) (hx : -1 ≤ x.fst ∧ x.snd ≤ 1) (n : ℕ) : ℚInterval :=
  -- Compute `x^2`, which will be [0,...] if xl/xu have different signs
  let x_sq := sq x
  -- Now `cos x` is an Antitone power series in `sq x`, so `x.fst` gives an upper
  -- bound and `x.snd` gives a lower bound.
  --TODO: Convert this `Finset.sum` into a `(List.range n).foldr`
  let cos_x_l : ℚ := ∑ i ∈ Finset.range (2 * n), (
    (-x_sq.snd)^i / (Nat.factorial (2 * i))
  )
  let cos_x_u : ℚ := ∑ i ∈ Finset.range (2 * n + 1), (
    (-x_sq.fst)^i / (Nat.factorial (2 * i))
  )
  ⟨⟨cos_x_l, cos_x_u⟩, cos_unit_interval_ordered x hx n⟩


theorem cos_unit_interval_mem (x : ℚInterval) (hx : -1 ≤ x.fst ∧ x.snd ≤ 1) (n : ℕ) (r : ℝ) (hr : r ∈ x) :
    Real.cos r ∈ cos_unit_interval x hx n := by
  --Step 1: Write down Taylor series stuff for Complex.cos, using Complex.exp_bound
  --Then turn this into Real.cos
  --Then show that these two expressions and under/over-approximations.
  --Alternately can go straight via `taylor_mean_remainder_bound`.
  --This sort of subsumes the proof of cos_unit_interval_ordered, since we're showing
  -- that lb ≤ cos x and cos ≤ ub so of course lb ≤ ub ... so that proof might become
  -- unneeded.
  --EDIT: actually this is in Mathlib in the form `Real.hasSum_cos`.
  change And _ _
  dsimp [cos_unit_interval]
  replace hr := mem_sq x r hr
  replace hx : _ ≤ (1 : ℚ) ∧ _ ≤ (1 : ℚ) := sq_interval_max x hx
  generalize sq x = y at *; clear x
  sorry

lemma inv_2_pow_clog_max_abs_mul_le_1 (xl xu : ℚ) :
    let x_max := |xl| ⊔ |xu|;
    let dn := Nat.clog 2 ⌈x_max⌉₊;
    -1 ≤ (2 ^ dn)⁻¹ * xl ∧ (2 ^ dn)⁻¹ * xu ≤ 1 := by
  intro x_max dn
  have h := Nat.le_pow_clog one_lt_two ⌈x_max⌉₊
  qify at h
  constructor
  · suffices -xl ≤ 2 ^ dn by
      linarith [inv_mul_le_one_of_le₀ this (pow_nonneg rfl dn)]
    exact (neg_le_abs xl).trans <| (le_max_left |xl| |xu|).trans <| (Nat.le_ceil x_max).trans h
  · suffices xu ≤ 2 ^ dn from
      inv_mul_le_one_of_le₀ this (pow_nonneg rfl dn)
    exact (le_abs_self xu).trans <| (le_max_right |xl| |xu|).trans <| (Nat.le_ceil x_max).trans h

/-- A bound on `cos x` that shrinks with `n`. First divides by a large enough power of 2 so
that we have a number within the range [-1,1]. Then we use the first `2n` terms of the Taylor
series for a lower bound, and the first `2n+1` terms for an upper bound. -/
def cos_interval (x : ℚInterval) (n : ℕ) : ℚInterval :=
  let ⟨⟨xl,xu⟩, hx⟩ := x
  let x_max := max (abs xl) (abs xu)
  let dn := Nat.clog 2 ⌈x_max⌉₊
  -- y := x / 2^xmax, so it's in the range [-1, 1]
  let y : ℚInterval := ⟨(2^dn : ℚ)⁻¹ • (xl, xu),
      (mul_le_mul_iff_of_pos_left (by positivity)).mpr hx⟩
  doubling_map^[dn] (cos_unit_interval y (inv_2_pow_clog_max_abs_mul_le_1 xl xu) n)

/-- `cos_interval` contains the cosines of any real values inside. -/
theorem cos_interval_mem (x : ℚInterval) (n : ℕ) (r : ℝ) (hr : r ∈ x) :
    Real.cos r ∈ cos_interval x n := by
  rw [cos_interval]
  let x_max := max (abs x.1.1) (abs x.1.2)
  let dn := Nat.clog 2 ⌈x_max⌉₊
  have h₁ : (y : ℚInterval) → _ := fun y ↦ doubling_map_cos_pow y dn ((2^dn)⁻¹ * r)
  conv at h₁ =>
    enter [y, 2, 2, 1]
    equals r => simp
  apply h₁
  apply cos_unit_interval_mem _ (inv_2_pow_clog_max_abs_mul_le_1 x.1.1 x.1.2)
  simpa [QInterval.mem_qinterval_iff_and, dn, x_max] using hr

/-- The width of `cos_interval` is bounded in terms of the magnitude of `x` and the width
of the input interval. -/
theorem cos_interval_width (x : ℚInterval) (n : ℕ) :
    (cos_interval x n).snd ≤ (cos_interval x n).fst +
      4 * (max (abs x.fst) (abs x.snd))^2 / 2^n +
      4 * (max (abs x.fst) (abs x.snd)) * (x.snd - x.fst) := by
  sorry

def cos (x : ComputableℝSeq) : ComputableℝSeq :=
  mk
  (x := Real.cos x.val)
  (lub := fun n ↦ cos_interval (x.lub n) n)
  (hcl := by
    intro ε
    sorry
  )
  (hcu := by
    sorry
  )
  (hlb := fun n ↦ by sorry)
  (hub := fun n ↦ by sorry)
  (heq := by
    sorry
  )

#eval! ((cos (-17)).lb 1).toDecimal
#eval! ((cos 17).ub 2).toDecimal

end Cos

end ComputableℝSeq

namespace IsComputable

instance instComputableCos (x : ℝ) [hx : IsComputable x] : IsComputable (Real.cos x) :=
  lift Real.cos ComputableℝSeq.Cos.cos (fun _ ↦ ComputableℝSeq.mk_val_eq_val) hx

end IsComputable

--test
example : Real.cos 10 < -0.83 := by
  native_decide

example : -0.84 < Real.cos 10 := by
  native_decide
