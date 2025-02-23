import ComputableReal.IsComputable
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ComputableℝSeq
namespace Exp

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

private lemma ceil_termination {x : ℚ} (hx : 1 < x) : ⌈x / 2⌉.toNat < ⌈x⌉.toNat := by
  simp only [Int.lt_toNat, Int.ofNat_toNat, sup_lt_iff, Int.ceil_pos]
  constructor
  · qify
    refine lt_of_lt_of_le ?_ (Int.le_ceil x)
    convert Int.ceil_lt_two_mul (a := x / 2) (by linarith)
    linarith
  · exact gt_of_gt_of_ge hx rfl

/-- A valid lower bound when 0 ≤ x. CauSeq that converges to Real.exp x from below. -/
def exp_lb₀ (x : ℚ) (n : ℕ) : ℚ :=
  if h : 1 < x then
    (exp_lb₀ (x/2) n)^2
  else
    -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
    (List.range n).foldr (fun (n : ℕ) v ↦ 1 + (x * v) / (n+1)) 1
  termination_by ⌈x⌉.toNat
  decreasing_by exact (ceil_termination h)

/-- A valid upper bound when 0 ≤ x. CauSeq that converges to Real.exp x from above. -/
def exp_ub₀ (x : ℚ) (n : ℕ) : ℚ :=
  if 1/2 < x then
    (exp_ub₀ (x/2) n)^2
  else
    -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
    let series : ℚ := (List.range n).foldr (fun n v ↦ 1 + (x * v) / (n+1)) 1
    let den_ub : ℚ := 1 - x^(n+1) / (n+1).factorial
    series / den_ub
  termination_by ⌈2 * x⌉.toNat
  decreasing_by decreasing_with
  constructor
  · qify
    rw [mul_div]
    refine lt_of_lt_of_le ?_ (Int.le_ceil (2 * x))
    convert Int.ceil_lt_two_mul (a := 2 * x / 2) (by linarith)
    linarith
  · linarith

theorem List_foldr_eq_finset_sum (x : ℚ) (n : ℕ) :
    List.foldr (fun n v => 1 + x * v / (↑n + 1)) 1 (List.range n)
    = ∑ i ∈ Finset.range (n + 1), x^i / i.factorial := by
  suffices ∀ (v : ℚ), List.foldr (fun n v => 1 + x * v / (↑n + 1)) v (List.range n)
      = (∑ i ∈ Finset.range n, x^i / i.factorial) + v * (x ^ n) / n.factorial by
    convert this 1
    simp [Finset.range_add_one, _root_.add_comm]
  induction n
  · simp
  · intro v
    rename_i n ih
    simp [Finset.range_add_one, List.range_succ, Nat.factorial_succ, ih]
    rw [add_mul, one_mul, add_div, pow_succ]
    suffices x * v / (↑n + 1) * x ^ n / ↑n.factorial = v * (x ^ n * x) / ((↑n + 1) * ↑n.factorial) by
      rw [this]
      ring
    field_simp
    ring_nf

theorem exp_lb₀_nonneg (x : ℚ) (n : ℕ) (hx : 0 ≤ x) : 0 ≤ exp_lb₀ x n := by
  rw [exp_lb₀, List_foldr_eq_finset_sum]
  split <;> positivity

theorem exp_lb₀_le_exp (x : ℚ) (n : ℕ) (hx : 0 ≤ x) : exp_lb₀ x n ≤ Real.exp x := by
  wlog hx₁ : x ≤ 1
  · push_neg at hx₁
    set y₀ := ⌈x⌉.toNat with hy
    generalize y₀=y at *; clear y₀
    induction y using Nat.strong_induction_on generalizing x
    rename_i n' ih
    rw [exp_lb₀, dif_pos hx₁, ← Real.sq_sqrt (Real.exp_nonneg ↑x), ← Real.exp_half]
    push_cast
    rw [sq_le_sq₀ (Rat.cast_nonneg.mpr <| exp_lb₀_nonneg _ _ <| Rat.div_nonneg hx rfl) (by positivity)]
    norm_cast
    by_cases h₂ : (x / 2) ≤ 1
    · exact this (x / 2) n (by positivity) h₂
    · refine ih ⌈x / 2⌉.toNat ?_ _ (by positivity) (by linarith) rfl
      simpa only [hy] using ceil_termination hx₁
  · rw [exp_lb₀]
    have hx₁' : ¬1 < x := by linarith
    rw [dif_neg hx₁', List_foldr_eq_finset_sum]
    exact_mod_cast Real.sum_le_exp_of_nonneg (Rat.cast_nonneg.mpr hx) _

-- def exp_lb (x : ℚ) : CauSeq ℚ abs :=
--   if h : 0 ≤ x then
--     ⟨exp_lb₀ x, sorry⟩
--   else
--     ⟨1 / exp_ub₀ (-x), sorry⟩

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

-- theorem causeq_eq_self (s : CauSeq ℚ abs) {h : IsCauSeq abs s} : ⟨(s : ℕ → ℚ), h⟩ = s :=
  -- rfl


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

end Exp
end ComputableℝSeq
