import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondAction
import QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors

/-! The genuine adapted-frame projective transition, on a refined local
spin lift, has the exact second-affine matrix fraction. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondPoint

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinSmoothLocalFactors
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveSecondAction
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actualTransition_secondPoint_ratio (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : secondDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0) :
    ((projectiveChart 1 1)
      (spinorTransition Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
        (secondAffineSpinorPoint w))) 0 =
      secondMobius (halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w := by
  obtain ⟨a, b, ha, _, _, hproj, _⟩ :=
    local_factors_clifford Q (achart ℍ p) (achart ℍ q) lift
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx
  rw [hproj]
  have hmat : halfSpinMatrix (a : ℍ) =
      halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y) :=
    congrArg halfSpinMatrix ha
  have hden' : secondDen (halfSpinMatrix (a : ℍ)) w ≠ 0 := by
    rwa [hmat]
  rw [secondAffineSpinorPoint_action_ratio a w hden', hmat]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondPoint
