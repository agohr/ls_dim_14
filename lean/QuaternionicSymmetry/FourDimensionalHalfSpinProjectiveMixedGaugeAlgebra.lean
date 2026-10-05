import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondDerivative

/-! Source `[1:z]` to target `[w:1]` uses a one-sided matrix swap.
The exact mixed affine fraction and connection gauge chain are valid even
when `z = 0` and `w = 0`, so chart overlap is not assumed. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveSecondChart

noncomputable section

def mixedDen (G : Mat2) (z : ℂ) : ℂ := chartNum G z
def mixedNum (G : Mat2) (z : ℂ) : ℂ := chartDen G z
def mixedMobius (G : Mat2) (z : ℂ) : ℂ := mixedNum G z / mixedDen G z

theorem mixedDen_swap (G : Mat2) (z : ℂ) :
    mixedDen G z = chartDen (coordinateSwap * G) z := by
  simp [mixedDen, chartDen, chartNum, coordinateSwap,
    Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixedNum_swap (G : Mat2) (z : ℂ) :
    mixedNum G z = chartNum (coordinateSwap * G) z := by
  simp [mixedNum, chartDen, chartNum, coordinateSwap,
    Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixedMobius_swap (G : Mat2) (z : ℂ) :
    mixedMobius G z = mobius (coordinateSwap * G) z := by
  simp [mixedMobius, mobius, ← mixedNum_swap, ← mixedDen_swap]

def mixedVaryingMobius (G C : Mat2) (z t : ℂ) : ℂ :=
  (mixedNum G z + t * mixedNum C z) /
    (mixedDen G z + t * mixedDen C z)

theorem mixedVaryingMobius_swap (G C : Mat2) (z t : ℂ) :
    mixedVaryingMobius G C z t =
      varyingMobius (coordinateSwap * G) (coordinateSwap * C) z t := by
  simp [mixedVaryingMobius, varyingMobius,
    ← mixedNum_swap, ← mixedDen_swap]

theorem mixed_gauge_chain (G A B C : Mat2) (z : ℂ)
    (hG : G * B = A * G + C) (hden : mixedDen G z ≠ 0) :
    deriv (mixedMobius G) z * affineGenerator B z =
      secondChartGenerator A (mixedMobius G z) +
        deriv (mixedVaryingMobius G C z) 0 := by
  let S : Mat2 := coordinateSwap
  have hS : S * S = 1 := coordinateSwap_sq
  have hG' : (S * G) * B = (S * A * S) * (S * G) + S * C := by
    calc
      (S * G) * B = S * (G * B) := by rw [Matrix.mul_assoc]
      _ = S * (A * G + C) := by rw [hG]
      _ = (S * A * S) * (S * G) + S * C := by
        simp only [Matrix.mul_add, Matrix.mul_assoc,
          ← Matrix.mul_assoc S S, hS, one_mul]
  have hden' : chartDen (S * G) z ≠ 0 := by
    rwa [← mixedDen_swap]
  have h := affine_gauge_chain (S * G) (S * A * S)
    B (S * C) z hG' hden'
  have hm : mixedMobius G = mobius (S * G) := by
    funext w
    exact mixedMobius_swap G w
  have hv : mixedVaryingMobius G C z =
      varyingMobius (S * G) (S * C) z := by
    funext t
    exact mixedVaryingMobius_swap G C z t
  simpa only [hm, hv, secondChartGenerator, S] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
