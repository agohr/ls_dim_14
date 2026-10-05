import QuaternionicSymmetry.CompactSymplecticHaar
import Mathlib.Probability.Moments.MGFAnalytic

/-!
Analytic coefficient extraction for actual compact symplectic orbital
integrals. Compactness supplies exponential integrability at every real
parameter; the moment-generating-function theorems then identify every
Taylor coefficient with its Haar moment divided by its factorial.
The spectral Harish--Chandra formula remains a separate input to instantiate.
-/

namespace QuaternionicSymmetry.CompactSymplecticHaar

open Matrix MeasureTheory ProbabilityTheory

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem integrableExpSet_halfTrace (J B X : Matrix κ κ ℂ) :
    integrableExpSet (halfTrace J B X) (probability J) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact integrable_exp_halfTrace J B X t

/-- The actual normalized exponential orbital integral. -/
def exponentialIntegral (J B X : Matrix κ κ ℂ) (t : ℝ) : ℝ :=
  ∫ g, Real.exp (t * halfTrace J B X g) ∂probability J

theorem exponentialIntegral_eq_mgf (J B X : Matrix κ κ ℂ) :
    exponentialIntegral J B X = mgf (halfTrace J B X) (probability J) := rfl

theorem analyticAt_exponentialIntegral (J B X : Matrix κ κ ℂ) (t : ℝ) :
    AnalyticAt ℝ (exponentialIntegral J B X) t := by
  apply analyticAt_mgf
  simp [integrableExpSet_halfTrace]

/-- Differentiating the Haar integral at zero gives the corresponding moment.
All differentiation-under-the-integral conditions follow from compactness. -/
theorem iteratedDeriv_exponentialIntegral_zero (J B X : Matrix κ κ ℂ) (k : ℕ) :
    iteratedDeriv k (exponentialIntegral J B X) 0 =
      ∫ g, halfTrace J B X g ^ k ∂probability J := by
  apply iteratedDeriv_mgf_zero
  simp [integrableExpSet_halfTrace]

theorem hasFPowerSeriesAt_exponentialIntegral (J B X : Matrix κ κ ℂ) :
    HasFPowerSeriesAt (exponentialIntegral J B X)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun k => (∫ g, halfTrace J B X g ^ k ∂probability J) /
          (Nat.factorial k : ℝ))) 0 := by
  have h := hasFPowerSeriesAt_mgf
    (X := halfTrace J B X) (μ := probability J) (v := 0)
    (by simp [integrableExpSet_halfTrace])
  simpa only [zero_mul, Real.exp_zero, mul_one] using h

/-- In even degree, the coefficient is exactly the actual even moment
divided by `(2k)!`. -/
theorem even_taylor_coefficient (J B X : Matrix κ κ ℂ) (k : ℕ) :
    iteratedDeriv (2 * k) (exponentialIntegral J B X) 0 /
        (Nat.factorial (2 * k) : ℝ) =
      evenMoment J B X k / (Nat.factorial (2 * k) : ℝ) := by
  rw [iteratedDeriv_exponentialIntegral_zero]
  rfl

/-- The full-complex-trace convention introduces the factor `4^k` at
even weight `k`, in addition to the Taylor factorial. -/
theorem fullTrace_even_integral (J B X : Matrix κ κ ℂ) (k : ℕ) :
    (∫ g : stabilizer J,
      (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
        (g.1 : Matrix κ κ ℂ)ᴴ)).re ^ (2 * k) ∂probability J) =
      4 ^ k * evenMoment J B X k := by
  rw [fullTrace_integral_pow, pow_mul]
  norm_num [evenMoment]

end
end QuaternionicSymmetry.CompactSymplecticHaar
