import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveReverseMixedPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors

/-! The actual refined adapted-frame transition maps a second-affine
source point `[w:1]` to the first-affine target `[1:z]` by the exact
reverse mixed fraction, including either affine pole. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReversePoint

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinSmoothLocalFactors
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveReverseMixedPoint
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actualTransition_reversePoint (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : reverseDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0) :
    spinorTransition Q (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
      (secondAffineSpinorPoint w) =
    affineSpinorPoint
      (reverseMobius (halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w) := by
  obtain ⟨a, b, ha, _, _, hproj, _⟩ :=
    local_factors_clifford Q (achart ℍ p) (achart ℍ q) lift
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx
  rw [hproj]
  have hmat : halfSpinMatrix (a : ℍ) =
      halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y) :=
    congrArg halfSpinMatrix ha
  have hden' : reverseDen (halfSpinMatrix (a : ℍ)) w ≠ 0 := by
    rwa [hmat]
  rw [projectiveHalfSpin_reversePoint a w hden', hmat]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReversePoint
