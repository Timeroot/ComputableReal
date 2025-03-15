import ComputableReal.IsComputable
import Mathlib.Data.Complex.Trigonometric

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
    ⟨⟨x.snd^2, x.fst^2⟩, by dsimp; nlinarith [x.2]⟩
  else if h₂ : 0 < x.fst then
    ⟨⟨x.fst^2, x.snd^2⟩, by dsimp; nlinarith [x.2]⟩
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

/-- The map `x ↦ 2x^2 - 1`, on intervals. In particular, if `cos θ ∈ x`, then
`cos 2θ ∈ doubling_map x`. -/
def doubling_map (x : ℚInterval) : ℚInterval :=
  2 • sq x - 1

/-- The doubling map maps `cos θ` bounding intervals to `⬝cos 2θ` intervals. -/
theorem doubling_map_cos (x : ℚInterval) (θ : ℝ) (h : Real.cos θ ∈ x) :
    Real.cos (2 * θ) ∈ doubling_map x := by
  rw [Real.cos_two_mul, doubling_map]
  replace h := mem_sq x _ h
  rw [QInterval.mem_qinterval_iff_and] at h ⊢
  simpa using h

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
