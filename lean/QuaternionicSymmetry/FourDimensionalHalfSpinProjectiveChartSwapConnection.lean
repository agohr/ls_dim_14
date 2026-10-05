import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondChart
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusDerivative

/-! The local projective connection generator glues across the two
standard CP¹ affine charts by the exact inversion tangent derivative. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartSwapConnection

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveSecondChart

noncomputable section

theorem swap_chartDen (z : ℂ) : chartDen coordinateSwap z = z := by
  simp [chartDen, coordinateSwap]

theorem swap_mobius (z : ℂ) : mobius coordinateSwap z = z⁻¹ := by
  rw [mobius, swap_chartDen]
  simp [chartNum, coordinateSwap]

theorem secondChart_generator_inversion (A : Mat2) (z : ℂ) (hz : z ≠ 0) :
    deriv (mobius coordinateSwap) z * affineGenerator A z =
      secondChartGenerator A (mobius coordinateSwap z) := by
  have hG : coordinateSwap * A =
      (coordinateSwap * A * coordinateSwap) * coordinateSwap + 0 := by
    simp only [add_zero, Matrix.mul_assoc, coordinateSwap_sq, mul_one]
  have hden : chartDen coordinateSwap z ≠ 0 := by
    rwa [swap_chartDen]
  have h := affine_gauge_chain coordinateSwap
    (coordinateSwap * A * coordinateSwap) A 0 z hG hden
  have hvar : varyingMobius coordinateSwap 0 z =
      fun _ => mobius coordinateSwap z := by
    funext t
    simp [varyingMobius, mobius, chartNum, chartDen]
  rw [hvar, deriv_const, add_zero] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartSwapConnection
