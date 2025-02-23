This is a package for [Lean4](https://github.com/leanprover/lean4) to enable computations with real numbers. As a theorem prover, Lean happily will talk about _all_ real numbers, including ones that cannot be computed. But most real numbers of interest can be computed. This is a package to help automatically determine certain statements about those real numbers. As a concrete example, statements like
```lean
example : Real.sqrt (1 + (1/4 : ℚ)) > Real.sqrt (2 + Real.sqrt (3 : ℕ)) / (Real.sqrt 7 - 1/2) := by
  native_decide
```
can now be proved by `native_decide`.

## Background

Colloquially, a real number is often called "computable" if there is an algorithm that produces successive lower- and upper-bounds which converge to that number (although precise definitions by experts may vary), and a computable function is one that maps computable numbers to computable numbers. These sequences are all rational numbers, so that we can represent them exactly. This gives it the flavor of [Interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic), but with the additional guarantee that our intervals need to converge.

For example, real addition is computable, since we can simply add the respective lower and upper bound sequences for the two summands. But computing the sign of a real is, strictly speaking, not computable: the lower bounds `-1 / 2^n` and upper bounds `1 / 2^n` converge to zero, but at any finite iteration we can't rule out that they're converging to a positive or negative value. For this reason, our implementation is a _partial function_: when the sign is needed, it will continue evaluating all the sequence until it determines the sign; this may not terminate.

## Implementation details

A `ComputableℝSeq` carries the functions for lower and upper bounds, together with proofs of their validity: they are equivalent Cauchy sequences, and the lower bound (resp. upper) stays below (resp. above) the completiton of the Cauchy sequence. Addition, negation, multiplication, and continuous functions can be computed on these sequences without issue.

When the sign function is needed, `ComputableℝSeq.sign` gives a `partial def` for computing this. Evaluating `ComputableℝSeq.sign` on `4 * (1/4 : ℚ) - 1` will immediately give `0`, since the lower and upper bounds will both evaluate to zero; but `Real.sqrt 2 - Real.sqrt 2` will never terminate. Computing the inverse of a `ComputableℝSeq` then calls `sign` appropriately. This also lets us create a `Decidable (x ≤ y)` instance where `x` and `y` are `ComputableℝSeq`.

To make this painlessly usable with `native_decide`, a typeclass `IsComputable (x : ℝ)` is available. This looks at the expression and tries to _structurally_ synthesize a `ComputableℝSeq` equal to the expression. This means that `Real.sqrt (2 + Real.sqrt 3)` is synthesized from a series of `IsComputable` instances for addition and square roots; but a local assumption like `x = 3` cannot be used. Then, given a pair of `IsComputable` instances on `x : ℝ` and `y : ℝ`, we have `Decidable (x ≤ y)`.

The partial aspect means that, in general, native_decide will be able to prove any true _inequality_ or _nonequality_, but is only able to provide _equalities_ if they're structurally rational expressions.

```lean
example : Real.sqrt 2 > 4 / 3 := by --true inequality, good
  native_decide

example : Real.sqrt 2 ≤ 1 + Real.sqrt 5 := by --true inequality, good
  native_decide

example : Real.sqrt 2 ≠ 4 / 3 := by --true nonequality, good
  native_decide

example : Real.sqrt 2 > 1 + Real.sqrt 5 := by --false inequality, gives an error that it evaluates to false
  native_decide

example : 2 + 5 = 14 / 2 := by --true equality, works because only rational numbers are involved
  native_decide

example : Real.sqrt 2 = Real.sqrt 2 := by --hangs, never terminate
  native_decide

example : Real.sqrt 2 - Real.sqrt 2 = 0:= by --hangs
  native_decide
```

## What's supported
* Addition, negation, subtraction
* Multiplication, natural number powers
* Inverses, division, integer powers
* Casts from naturals, rationals, `ofNat` literals, and `OfScientific` literals (e.g `1.2`)
* Simple functions: `ite`, `dite`, `Real.sign`, `abs`, `max`, `min`, `Finset.sum`
* `Real.sqrt`
* `Real.pi`

## TODO List
Roughly in order:
 * Adding support for `Real.exp` using repeated halving
   * This immediately gives support for `Real.sinh`, `Real.cosh`, `Real.tanh` 
 * Adding support for `Real.log` - will require careful sign handling similarly to inverses, due to the discontinuity at zero.
   * This gets us `Real.arsinh` ... not that it's in particularly high demand.
   * Also `Real.logb`, `Real.negMulLog`, `Real.posLog`.
 * Adding support for `Real.cos`
   * This gets us `Real.sin`, `Real.tan`, and most importantly, real powers `_ ^ _`. These rely on cosine because of their behavior with negative powers.
 * Supporting complex numbers, as a pair of computable sequences for real and imaginary parts.
   * Then using `Real.exp` and `Real.sin`/`Real.cos`, we get `Complex.exp`; then we get trig functions on the complex numbers for free too.
   * Make sure to add computability instances for `Complex.re`, `Complex.im`, `Complex.ofReal`, `abs`, `Complex.mk`, `Complex.normSq`, `Complex.instNorm`, `Complex.inner`... probably more.
 * Adding `Real.arctan`, possibly via `Real.two_mul_arctan_add_pi`.
   * This gets us `Real.arcsin` and `Real.arccos`, but also importantly `Complex.arg` and `Complex.log`. Then from `Complex.log` we get all the trig functions' inverses on the complex numbers.
 * Other, low-priority functions that can be implemented:
   * `Real.Gamma`, with the theorem `Real.GammaSeq_tendsto_Gamma`. Actually, given an implementation of `Real.pi`, this would give an alternate implementation of `Real.sin` using `Real.Gamma_mul_Gamma_one_sub` ... but that's probably not very practical.
   * Integrals with certain properties (such as positivity / convexity)