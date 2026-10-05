import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

/-! The second genuine CP¹ affine chart `[z:1]` obtains its connection
generator by the fixed coordinate swap, with the derivative checked from
the literal homogeneous-coordinate ratio. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondChart

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator

noncomputable section

def coordinateSwap : Mat2 := !![(0 : ℂ), 1; 1, 0]

theorem coordinateSwap_sq : coordinateSwap * coordinateSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateSwap, Matrix.mul_apply, Fin.sum_univ_succ]

theorem coordinateSwap_vec (z : ℂ) :
    coordinateSwap *ᵥ ![1,z] = ![z,1] := by
  ext i
  fin_cases i <;>
    simp [coordinateSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def secondChartGenerator (A : Mat2) (z : ℂ) : ℂ :=
  affineGenerator (coordinateSwap * A * coordinateSwap) z

def secondChartLinearFlow (A : Mat2) (z t : ℂ) : ℂ :=
  let v : Fin 2 → ℂ := ![z,1]
  (v 0 + t * (A *ᵥ v) 0) / (v 1 + t * (A *ᵥ v) 1)

theorem secondChartLinearFlow_eq_swapped (A : Mat2) (z t : ℂ) :
    secondChartLinearFlow A z t =
      affineLinearFlow (coordinateSwap * A * coordinateSwap) z t := by
  simp only [secondChartLinearFlow, affineLinearFlow]
  rw [← coordinateSwap_vec z]
  simp only [← Matrix.mulVec_mulVec]
  simp [coordinateSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem secondChartLinearFlow_hasDerivAt (A : Mat2) (z : ℂ) :
    HasDerivAt (secondChartLinearFlow A z)
      (secondChartGenerator A z) 0 := by
  have hfun : secondChartLinearFlow A z =
      affineLinearFlow (coordinateSwap * A * coordinateSwap) z := by
    funext t
    exact secondChartLinearFlow_eq_swapped A z t
  rw [hfun]
  exact affineLinearFlow_hasDerivAt _ z

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondChart
