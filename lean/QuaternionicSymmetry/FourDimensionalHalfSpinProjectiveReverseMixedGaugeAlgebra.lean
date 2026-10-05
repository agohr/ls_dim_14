import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondDerivative

/-! Source `[w:1]` to target `[1:z]` uses a right-sided matrix swap.
The explicit reverse mixed fraction and connection gauge chain include
the source and target affine poles. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveSecondMobius

noncomputable section

def reverseDen (G : Mat2) (w : ℂ) : ℂ := secondNum G w
def reverseNum (G : Mat2) (w : ℂ) : ℂ := secondDen G w
def reverseMobius (G : Mat2) (w : ℂ) : ℂ := reverseNum G w / reverseDen G w

theorem reverseDen_swap (G : Mat2) (w : ℂ) :
    reverseDen G w = chartDen (G * coordinateSwap) w := by
  simp [reverseDen, secondNum, chartDen, coordinateSwap,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem reverseNum_swap (G : Mat2) (w : ℂ) :
    reverseNum G w = chartNum (G * coordinateSwap) w := by
  simp [reverseNum, secondDen, chartNum, coordinateSwap,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem reverseMobius_swap (G : Mat2) (w : ℂ) :
    reverseMobius G w = mobius (G * coordinateSwap) w := by
  simp [reverseMobius, mobius, ← reverseNum_swap, ← reverseDen_swap]

def reverseVaryingMobius (G C : Mat2) (w t : ℂ) : ℂ :=
  (reverseNum G w + t * reverseNum C w) /
    (reverseDen G w + t * reverseDen C w)

theorem reverseVaryingMobius_swap (G C : Mat2) (w t : ℂ) :
    reverseVaryingMobius G C w t =
      varyingMobius (G * coordinateSwap) (C * coordinateSwap) w t := by
  simp [reverseVaryingMobius, varyingMobius,
    ← reverseNum_swap, ← reverseDen_swap]

theorem reverse_gauge_chain (G A B C : Mat2) (w : ℂ)
    (hG : G * B = A * G + C) (hden : reverseDen G w ≠ 0) :
    deriv (reverseMobius G) w * secondChartGenerator B w =
      affineGenerator A (reverseMobius G w) +
        deriv (reverseVaryingMobius G C w) 0 := by
  let S : Mat2 := coordinateSwap
  have hS : S * S = 1 := coordinateSwap_sq
  have hG' : (G * S) * (S * B * S) = A * (G * S) + C * S := by
    calc
      (G * S) * (S * B * S) = (G * B) * S := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S S,
          hS, one_mul]
      _ = (A * G + C) * S := by rw [hG]
      _ = A * (G * S) + C * S := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
  have hden' : chartDen (G * S) w ≠ 0 := by
    rwa [← reverseDen_swap]
  have h := affine_gauge_chain (G * S) A
    (S * B * S) (C * S) w hG' hden'
  have hm : reverseMobius G = mobius (G * S) := by
    funext z
    exact reverseMobius_swap G z
  have hv : reverseVaryingMobius G C w =
      varyingMobius (G * S) (C * S) w := by
    funext t
    exact reverseVaryingMobius_swap G C w t
  simpa only [hm, hv, secondChartGenerator, S] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
