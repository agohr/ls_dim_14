import QuaternionicSymmetry.OrbitalAnalyticOddKernel
import QuaternionicSymmetry.CompactSymplecticMoments

/-!
Coefficient extraction from a cross-multiplied Harish--Chandra identity.
The identity with the actual Haar integral remains an explicit premise;
all differentiation, Taylor factorials, and coefficient shifts are proved.
This does not register a new literature axiom or assert the spectral identity.
-/

namespace QuaternionicSymmetry.OrbitalHaarCoefficientExtraction

open Matrix MeasureTheory SmoothTaylorSeries CompactSymplecticHaar
open OrbitalAnalyticOddKernel OrbitalOddFormalKernel OrbitalOddDeterminantBase

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def smoothExponentialIntegral (J B X : Matrix κ κ ℂ) : Smooth :=
  ⟨exponentialIntegral J B X, by
    change ContDiff ℝ ⊤ (exponentialIntegral J B X)
    exact (show AnalyticOnNhd ℝ (exponentialIntegral J B X) Set.univ from
      fun t _ => analyticAt_exponentialIntegral J B X t).contDiff⟩

theorem coeff_taylor_exponentialIntegral (J B X : Matrix κ κ ℂ) (m : ℕ) :
    PowerSeries.coeff m (taylorHom (smoothExponentialIntegral J B X)) =
      (∫ g, halfTrace J B X g ^ m ∂probability J) / (m.factorial : ℝ) := by
  change PowerSeries.coeff m (series (smoothExponentialIntegral J B X)) = _
  rw [coeff_series]
  change iteratedDeriv m (exponentialIntegral J B X) 0 / _ = _
  rw [iteratedDeriv_exponentialIntegral_zero]

/-- Exact analytic-to-formal coefficient extraction at every rank and weight.
The hypothesis states the actual cross-multiplied integral identity, with
the source constant and odd Vandermondes displayed rather than hidden. -/
theorem coefficient_of_cross_multiplied_identity {n : ℕ} (x y : Fin n → ℚ)
    (J B X : Matrix κ κ ℂ)
    (hidentity : ∀ t : ℝ,
      t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        exponentialIntegral J B X t =
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t)
    (k : ℕ) :
    ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        (evenMoment J B X k / ((2 * k).factorial : ℝ)) =
      (sourceConstant n : ℝ) *
        ((PowerSeries.coeff (n ^ 2 + 2 * k)
          (sourceFullFormalOddKernel x y).det : ℚ) : ℝ) := by
  have h : parameter ^ (n ^ 2) *
      constant ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        smoothExponentialIntegral J B X =
      constant (sourceConstant n : ℝ) * sourceDeterminant x y := by
    apply Subtype.ext
    funext t
    exact hidentity t
  have hs := congrArg taylorHom h
  simp only [map_mul, map_pow, taylor_parameter, taylor_constant,
    taylor_sourceDeterminant, mul_assoc] at hs
  have hc := congrArg (PowerSeries.coeff (2 * k + n ^ 2)) hs
  rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_C_mul,
    coeff_taylor_exponentialIntegral, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map] at hc
  simpa only [evenMoment, Nat.add_comm, Rat.coe_castHom] using hc

/-- The full trace convention supplies exactly `4^k` after analytic
coefficient extraction; the Taylor factorial remains `(2k)!`. -/
theorem fullTrace_coefficient_of_cross_multiplied_identity {n : ℕ} (x y : Fin n → ℚ)
    (J B X : Matrix κ κ ℂ)
    (hidentity : ∀ t : ℝ,
      t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        exponentialIntegral J B X t =
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t)
    (k : ℕ) :
    ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        ((∫ g : stabilizer J,
          (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
            (g.1 : Matrix κ κ ℂ)ᴴ)).re ^ (2 * k) ∂probability J) /
          ((2 * k).factorial : ℝ)) =
      4 ^ k * (sourceConstant n : ℝ) *
        ((PowerSeries.coeff (n ^ 2 + 2 * k)
          (sourceFullFormalOddKernel x y).det : ℚ) : ℝ) := by
  rw [fullTrace_even_integral]
  have h := coefficient_of_cross_multiplied_identity x y J B X hidentity k
  calc
    _ = 4 ^ k * (((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        (evenMoment J B X k / ((2 * k).factorial : ℝ))) := by ring
    _ = _ := by rw [h]; ring

end
end QuaternionicSymmetry.OrbitalHaarCoefficientExtraction
