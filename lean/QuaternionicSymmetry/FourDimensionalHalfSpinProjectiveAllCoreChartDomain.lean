import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap

/-! In all four actual affine source/target cases, the matrix denominator
is precisely the target homogeneous coordinate. Thus target affine-chart
membership, not an artificial extra nonvanishing premise, gives the
denominator required by the checked differential covariance theorem. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreChartDomain

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinMatrix
  ComplexProjectiveTopology

noncomputable section

def indexedSourceVector (i : Fin 2) (z : ℂ) : Fin 2 → ℂ :=
  if i = 0 then ![1,z] else ![z,1]

def indexedSourcePoint (i : Fin 2) (z : ℂ) : ProjectiveSpinor :=
  if i = 0 then affineSpinorPoint z else secondAffineSpinorPoint z

theorem indexedSourcePoint_mk (i : Fin 2) (z : ℂ) :
    indexedSourcePoint i z =
      Projectivization.mk ℂ (indexedSourceVector i z) (by
        fin_cases i <;> simp [indexedSourceVector]) := by
  fin_cases i
  · rfl
  · exact secondAffineSpinorPoint_mk z

theorem indexedDenominator_eq_coordinate (i j : Fin 2) (A : Mat2) (z : ℂ) :
    indexedDenominator i j A z = (A *ᵥ indexedSourceVector i z) j := by
  fin_cases i <;> fin_cases j <;>
    simp [indexedDenominator, indexedSourceVector,
      chartDen, chartNum, mixedDen, reverseDen, secondDen,
      secondNum, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem indexedDenominator_ne_zero_of_target_mem (i j : Fin 2)
    (q : unitary ℍ) (z : ℂ)
    (hmem : projectiveHalfSpin q (indexedSourcePoint i z) ∈
      affineDomain 1 j) :
    indexedDenominator i j (halfSpinMatrix (q : ℍ)) z ≠ 0 := by
  rw [indexedDenominator_eq_coordinate]
  rw [indexedSourcePoint_mk, projectiveHalfSpin_mk] at hmem
  have hcoord := (mem_affineDomain_mk 1 j _ _).1 hmem
  simpa only [halfSpinLinearEquiv_apply] using hcoord

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreChartDomain
