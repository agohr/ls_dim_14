import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredSecondPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondChart

/-! The genuine `[w:1]` projective coordinate uses the opposite matrix
fraction; it is the first-chart Möbius map for the explicitly conjugated
matrix, including the south pole `w=0`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondMobius

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveSecondChart

noncomputable section

def secondDen (G : Mat2) (w : ℂ) : ℂ := G 1 0 * w + G 1 1
def secondNum (G : Mat2) (w : ℂ) : ℂ := G 0 0 * w + G 0 1
def secondMobius (G : Mat2) (w : ℂ) : ℂ := secondNum G w / secondDen G w

theorem secondDen_swap (G : Mat2) (w : ℂ) :
    secondDen G w = chartDen (coordinateSwap * G * coordinateSwap) w := by
  simp [secondDen, chartDen, coordinateSwap, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem secondNum_swap (G : Mat2) (w : ℂ) :
    secondNum G w = chartNum (coordinateSwap * G * coordinateSwap) w := by
  simp [secondNum, chartNum, coordinateSwap, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem secondMobius_swap (G : Mat2) (w : ℂ) :
    secondMobius G w = mobius (coordinateSwap * G * coordinateSwap) w := by
  simp [secondMobius, mobius, ← secondNum_swap, ← secondDen_swap]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondMobius
