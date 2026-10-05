import QuaternionicSymmetry.AhatCoefficientLimits
import QuaternionicSymmetry.WeightFiveAhat
import QuaternionicSymmetry.AlgebraPolynomialLimits

/-! The fifth coefficient of the limiting positive Gaussian product.  This is
still a polynomial identity: the identification with actual Gaussian moments
is proved separately. -/

namespace QuaternionicSymmetry.AhatFifthCoefficientLimits

open Filter Topology

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S]

local notation "s(" r ")" => algebraMap ℝ S r

/-- The degree-five exponential coefficient in the five logarithmic
parameters, with matrix power traces as its coefficients. -/
def e₅ (z₁ z₂ z₃ z₄ z₅ : S) : MvPolynomial (Fin 5) S :=
  MvPolynomial.C z₅ * MvPolynomial.X 4 +
    MvPolynomial.C (z₁ * z₄) * MvPolynomial.X 0 * MvPolynomial.X 3 +
    MvPolynomial.C (z₂ * z₃) * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.C (s(1 / 2) * z₁ ^ 2 * z₃) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 +
    MvPolynomial.C (s(1 / 2) * z₁ * z₂ ^ 2) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C (s(1 / 6) * z₁ ^ 3 * z₂) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 +
    MvPolynomial.C (s(1 / 120) * z₁ ^ 5) * MvPolynomial.X 0 ^ 5

def logParameters (N : ℕ) (i : Fin 5) : ℝ :=
  (∑ m ∈ Finset.range N, AhatGaussianWeights.weight m ^ (i.val + 1)) /
    ((i.val : ℝ) + 1)

def logLimit (i : Fin 5) : ℝ := AhatGaussianWeights.positiveLog (i.val + 1)

theorem logParameters_tendsto (i : Fin 5) :
    Tendsto (fun N => logParameters N i) atTop (𝓝 (logLimit i)) := by
  convert (AhatGaussianWeights.partial_log_tendsto (j := i.val + 1) (by omega)) using 1;
    norm_num [logParameters, logLimit]

@[simp] theorem logLimit_zero : logLimit 0 = 1 / 24 := by
  simp [logLimit]

@[simp] theorem logLimit_one : logLimit 1 = 1 / 2880 := by
  simp [logLimit]

@[simp] theorem logLimit_two : logLimit 2 = 1 / 181440 := by
  simp [logLimit]

@[simp] theorem logLimit_three : logLimit 3 = 1 / 9676800 := by
  simp [logLimit]

@[simp] theorem logLimit_four : logLimit 4 = 1 / 479001600 := by
  change (-1 : ℝ) ^ 5 * (LogAhat.ell 5 : ℝ) = 1 / 479001600
  norm_num [LogAhat.ell_five]

theorem eval_e₅ (z₁ z₂ z₃ z₄ z₅ : S) (a : Fin 5 → ℝ) :
    MvPolynomial.eval (fun i => algebraMap ℝ S (a i)) (e₅ z₁ z₂ z₃ z₄ z₅) =
      s(a 4) * z₅ + s(a 0) * s(a 3) * z₁ * z₄ +
      s(a 1) * s(a 2) * z₂ * z₃ +
      s(1 / 2) * s(a 0) ^ 2 * s(a 2) * z₁ ^ 2 * z₃ +
      s(1 / 2) * s(a 0) * s(a 1) ^ 2 * z₁ * z₂ ^ 2 +
      s(1 / 6) * s(a 0) ^ 3 * s(a 1) * z₁ ^ 3 * z₂ +
      s(1 / 120) * s(a 0) ^ 5 * z₁ ^ 5 := by
  simp only [e₅, map_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, map_pow]
  ring

/-- Exact limiting trace polynomial.  The seven coefficients are those of the
printed fifth Gaussian polynomial after `z_j = 2 p_j`. -/
theorem e₅_limit_eval (z₁ z₂ z₃ z₄ z₅ : S) :
    MvPolynomial.eval (fun i => s(logLimit i)) (e₅ z₁ z₂ z₃ z₄ z₅) =
      s(1 / 479001600) * z₅ + s(1 / 232243200) * z₁ * z₄ +
      s(1 / 522547200) * z₂ * z₃ +
      s(1 / 209018880) * z₁ ^ 2 * z₃ +
      s(1 / 398131200) * z₁ * z₂ ^ 2 +
      s(1 / 238878720) * z₁ ^ 3 * z₂ +
      s(1 / 955514880) * z₁ ^ 5 := by
  rw [eval_e₅]
  simp only [logLimit_zero, logLimit_one, logLimit_two, logLimit_three, logLimit_four]
  simp only [← map_pow, ← map_mul]
  norm_num

/-- The limiting fifth trace coefficient, retained as a named expression to
keep large exterior-algebra applications small during elaboration. -/
def coefficient (z₁ z₂ z₃ z₄ z₅ : S) : S :=
  MvPolynomial.eval (fun i => s(logLimit i)) (e₅ z₁ z₂ z₃ z₄ z₅)

theorem coefficient_eq_seven_terms (z₁ z₂ z₃ z₄ z₅ : S) :
    coefficient z₁ z₂ z₃ z₄ z₅ =
      s(1 / 479001600) * z₅ + s(1 / 232243200) * z₁ * z₄ +
      s(1 / 522547200) * z₂ * z₃ +
      s(1 / 209018880) * z₁ ^ 2 * z₃ +
      s(1 / 398131200) * z₁ * z₂ ^ 2 +
      s(1 / 238878720) * z₁ ^ 3 * z₂ +
      s(1 / 955514880) * z₁ ^ 5 := e₅_limit_eval z₁ z₂ z₃ z₄ z₅

private theorem mapped_rational_factor (a b : ℝ) (m n : ℕ)
    (h : a * m = b * n) : s(a) * (m : S) = s(b) * (n : S) := by
  have hh := congrArg (algebraMap ℝ S) h
  simpa only [map_mul, map_natCast] using hh

theorem coefficient_two_p_printed (p₁ p₂ p₃ p₄ p₅ : S) :
    coefficient (2 * p₁) (2 * p₂) (2 * p₃) (2 * p₄) (2 * p₅) =
      s(1 / 11496038400) *
        (385 * p₁ ^ 5 + 770 * p₁ ^ 3 * p₂ + 440 * p₁ ^ 2 * p₃ +
         231 * p₁ * p₂ ^ 2 + 198 * p₁ * p₄ + 88 * p₂ * p₃ + 48 * p₅) := by
  rw [coefficient_eq_seven_terms]
  norm_num
  have h5 : s(1 / 479001600) * 2 = s(1 / 11496038400) * 48 :=
    mapped_rational_factor _ _ 2 48 (by norm_num)
  have h14 : s(1 / 232243200) * 4 = s(1 / 11496038400) * 198 :=
    mapped_rational_factor _ _ 4 198 (by norm_num)
  have h23 : s(1 / 522547200) * 4 = s(1 / 11496038400) * 88 :=
    mapped_rational_factor _ _ 4 88 (by norm_num)
  have h113 : s(1 / 209018880) * 8 = s(1 / 11496038400) * 440 :=
    mapped_rational_factor _ _ 8 440 (by norm_num)
  have h122 : s(1 / 398131200) * 8 = s(1 / 11496038400) * 231 :=
    mapped_rational_factor _ _ 8 231 (by norm_num)
  have h1112 : s(1 / 238878720) * 16 = s(1 / 11496038400) * 770 :=
    mapped_rational_factor _ _ 16 770 (by norm_num)
  have h11111 : s(1 / 955514880) * 32 = s(1 / 11496038400) * 385 :=
    mapped_rational_factor _ _ 32 385 (by norm_num)
  linear_combination p₅ * h5 + p₁ * p₄ * h14 + p₂ * p₃ * h23 +
    p₁ ^ 2 * p₃ * h113 + p₁ * p₂ ^ 2 * h122 +
    p₁ ^ 3 * p₂ * h1112 + p₁ ^ 5 * h11111

theorem scalar_e₅_tendsto (z₁ z₂ z₃ z₄ z₅ : S) (L : S →ₗ[ℝ] ℝ) :
    Tendsto
      (fun N => L (MvPolynomial.eval (fun i => s(logParameters N i))
        (e₅ z₁ z₂ z₃ z₄ z₅))) atTop
      (𝓝 (L (s(1 / 479001600) * z₅ + s(1 / 232243200) * z₁ * z₄ +
        s(1 / 522547200) * z₂ * z₃ +
        s(1 / 209018880) * z₁ ^ 2 * z₃ +
        s(1 / 398131200) * z₁ * z₂ ^ 2 +
        s(1 / 238878720) * z₁ ^ 3 * z₂ +
        s(1 / 955514880) * z₁ ^ 5))) := by
  have h := AlgebraPolynomialLimits.scalar_eval_tendsto
    (e₅ z₁ z₂ z₃ z₄ z₅) L logParameters logLimit logParameters_tendsto
  rw [e₅_limit_eval] at h
  exact h

theorem contains_e₅_limit {v : S} (hv : v ≠ 0) (z₁ z₂ z₃ z₄ z₅ w : S)
    (hp : ∀ N, PositiveRay.Contains v
      (MvPolynomial.eval (fun i => s(logParameters N i))
        (e₅ z₁ z₂ z₃ z₄ z₅ * MvPolynomial.C w))) :
    PositiveRay.Contains v
      ((s(1 / 479001600) * z₅ + s(1 / 232243200) * z₁ * z₄ +
        s(1 / 522547200) * z₂ * z₃ +
        s(1 / 209018880) * z₁ ^ 2 * z₃ +
        s(1 / 398131200) * z₁ * z₂ ^ 2 +
        s(1 / 238878720) * z₁ ^ 3 * z₂ +
        s(1 / 955514880) * z₁ ^ 5) * w) := by
  have h := AlgebraPolynomialLimits.contains_of_tendsto hv
    (e₅ z₁ z₂ z₃ z₄ z₅ * MvPolynomial.C w)
    logParameters logLimit logParameters_tendsto hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C, e₅_limit_eval] using h

theorem contains_coefficient_limit {v : S} (hv : v ≠ 0) (z₁ z₂ z₃ z₄ z₅ w : S)
    (hp : ∀ N, PositiveRay.Contains v
      (MvPolynomial.eval (fun i => s(logParameters N i))
        (e₅ z₁ z₂ z₃ z₄ z₅ * MvPolynomial.C w))) :
    PositiveRay.Contains v (coefficient z₁ z₂ z₃ z₄ z₅ * w) := by
  have h := AlgebraPolynomialLimits.contains_of_tendsto hv
    (e₅ z₁ z₂ z₃ z₄ z₅ * MvPolynomial.C w)
    logParameters logLimit logParameters_tendsto hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C, coefficient] using h

end
end QuaternionicSymmetry.AhatFifthCoefficientLimits
