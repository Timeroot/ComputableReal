import ComputableReal.ComputableReal

open scoped QInterval

namespace Rat

def toDecimal (q : ℚ) (prec : ℕ := 20):=
  (q.floor.repr).append <| ".".append <| (10^prec * (q - q.floor)).floor.repr

end Rat

namespace ComputableℝSeq
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

namespace Exp

--valid lower bound when 0 ≤ x. CauSeq that converges to Real.exp x from below.
def exp_lb' (x : ℚ) (n : ℕ) : ℚ :=
  if 1 < x then
    (exp_lb' (x/2) n)^2
  else
    -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
    let series : ℚ := (List.range n).foldr (fun n v ↦ 1 + (x * v) / (n+1)) 1
    series
  termination_by (x.ceil).toNat
  decreasing_by decreasing_with
  sorry

--valid upper bound when 0 ≤ x. CauSeq that converges to Real.exp x from above.
def exp_ub' (x : ℚ) (n : ℕ) : ℚ :=
  if 1/2 < x then
    (exp_ub' (x/2) n)^2
  else
    -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
    let series : ℚ := (List.range n).foldr (fun n v ↦ 1 + (x * v) / (n+1)) 1
    let den_ub : ℚ := 1 - x^(n+1) / (n+1).factorial
    series / den_ub
  termination_by (x.ceil).toNat
  decreasing_by decreasing_with
  sorry

def exp_lb (x : ℚ) : CauSeq ℚ abs :=
  if h : 0 ≤ x then
    ⟨exp_lb' x, sorry⟩
  else
    ⟨1 / exp_ub' (-x), sorry⟩

def exp_ub (x : ℚ) : CauSeq ℚ abs :=
  if h : 0 ≤ x then
    ⟨exp_ub' x, sorry⟩
  else
    ⟨1 / exp_lb' (-x), sorry⟩

theorem exp_lb_is_lb (x : ℚ) : ∀ n, exp_lb x n ≤ Real.exp x :=
  sorry

theorem exp_ub_is_ub (x : ℚ) : ∀ n, exp_ub x n ≥ Real.exp x :=
  sorry

theorem exp_lb_val (x : ℚ) : Real.mk (exp_lb x) = Real.exp x :=
  sorry

theorem exp_ub_val (x : ℚ) : Real.mk (exp_ub x) = Real.exp x :=
  sorry

def exp_lub (x : ℚInterval) (n : ℕ) : ℚInterval :=
  ⟨⟨exp_lb x.fst n, exp_ub x.snd n⟩,
    Rat.cast_le.mp (by calc
      _ ≤ Real.exp x.fst := exp_lb_is_lb _ n
      _ ≤ Real.exp x.snd := Real.exp_monotone (Rat.cast_le.mpr x.2)
      _ ≤ (exp_ub x.toProd.2) n := exp_ub_is_ub _ n
    )⟩

-- theorem causeq_eq_self (s : CauSeq ℚ abs) {h : IsCauSeq abs s} : ⟨(s : ℕ → ℚ), h⟩ = s :=
  -- rfl

end Exp

-- theorem exp_lb_correct

def exp (x : ComputableℝSeq) : ComputableℝSeq where
  lub n := Exp.exp_lub (x.lub n) n
  hcl := sorry
  hcu := sorry
  hlub n := sorry
  heq' := sorry

theorem exp_eq_exp (x : ComputableℝSeq) : (exp x).val = Real.exp (x.val) := by
  sorry

end ComputableℝSeq

namespace Computableℝ

def exp : Computableℝ → Computableℝ :=
  mapℝ ComputableℝSeq.exp ComputableℝSeq.exp_eq_exp

#eval (exp (-1)).val

#eval (-exp (-1)).val

#eval -(-exp (exp (exp 0.1))).val

#eval ((List.range 11).map (exp (exp (exp 0.1))).unquot.lb).map Rat.toDecimal

#eval ((List.range 11).map (exp (exp (exp 0.1))).unquot.ub).map Rat.toDecimal

#eval ((List.range 20).map (fun n ↦ ComputableℝSeq.Exp.exp_lb (5) n)).map Rat.toDecimal

end Computableℝ
