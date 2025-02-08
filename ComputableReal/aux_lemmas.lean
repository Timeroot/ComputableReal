import Mathlib.Data.Real.Archimedean

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

/-- A function `f : α → β → γ` defines a function `map₂ f : Trunc α → Trunc β → Trunc γ`. -/
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
  rw [max_def]
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
  rw [min_def]
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

-- def apply (a : CauSeq ℚ abs) (f : ℚ → ℚ) (hf : Continuous f) : CauSeq ℚ abs :=
--   ⟨f ∘ a.1, by
--     -- let x := Real.mk a
--     intro ε hε
--     rw [continuous_iff_continuousAt] at hf
--     dsimp [ContinuousAt] at hf
--     simp_rw [LinearOrderedAddCommGroup.tendsto_nhds] at hf
--     rify at hf
--     -- let ⟨i, hi⟩ := a.2 ε hε
--     -- use i
--     -- intro j hj
--     -- replace hi := hi j hj
--     -- replace hf := hf (f (a i)) ε hε
--     -- dsimp [Filter.Eventually] at hf
--     -- by_contra hg; revert hf
--     -- simp only [imp_false, not_forall]
--     -- simp only [ge_iff_le, Function.comp_apply, not_exists, not_forall, not_lt, exists_prop] at hg
--     -- -- have := nhds x
--     -- have := tendsto_zero_iff_abs_tendsto_zero
--     -- simp at hf
--     -- cases hf
--     -- δ
--     sorry
--   ⟩

-- theorem equiv_apply (a b : CauSeq ℚ abs) (f : ℚ → ℚ) (hf : Continuous f) (hab : a ≈ b) :
--     a.apply f hf ≈ b.apply f hf := by
--   intro ε hε
--   rw [apply, apply]
--   dsimp
--   sorry

end Rat

namespace Completion

--extracted from CauSeq.Completion.instInvCauchyToRing

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem equiv_inv {f g: CauSeq β abv} (fg: f ≈ g) (hf: ¬LimZero f) (hg: ¬LimZero g)
    : mk (inv f hf) = mk (inv g hg) := by
  have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
  have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
  have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
  rw [mk_eq.2 fg, ← Ig] at If
  rw [← mul_one (mk (inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]

end Completion

end CauSeq

namespace Real

/-- Every real number has some Caucy sequence converging to it. -/
theorem exists_CauSeq (x : ℝ) : ∃(s : CauSeq ℚ abs), Real.mk s = x :=
  let ⟨y,hy⟩ := Quot.exists_rep x.cauchy
  ⟨y, by
  rw [Real.mk, CauSeq.Completion.mk, Quotient.mk'', Real.ofCauchy.injEq]
  exact hy⟩

end Real

namespace Continuous

-- lemma continuous_embed (fq : ℚ → ℚ) (fr : ℝ → ℝ) (hfr : ∀q, fq q = fr q) (hf₂ : Continuous fr) :
--     Continuous fq :=
--   sorry

end Continuous

--end silly lemmas
--================
