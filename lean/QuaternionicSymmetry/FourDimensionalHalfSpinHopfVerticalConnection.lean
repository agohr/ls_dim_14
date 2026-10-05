import QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalLinear

/-! The checked corrected Hopf fiber differential, now as a literal
real-linear map into the coefficient tangent plane, sends the negative
projective connection generator to the negative rank-three connection. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalConnection

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfVerticalLinear
  FourDimensionalHalfSpinHopfHorizontalVertical
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorHorizontalConnection
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem correctedVerticalLinear_horizontal
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    correctedVerticalLinear z
      (-(projectiveConnectionGenerator Q D p y u z)) =
      -(connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u) := by
  rw [correctedVerticalLinear_apply]
  exact indexedCorrectedHopf_zero_horizontal_vertical Q D p y u hy z
    (indexedCorrectedHopf_zero_coefficient z)

theorem correctedVerticalLinear_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    correctedVerticalLinear z
      (projectiveConnectionGenerator Q D p y u z) =
      connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u := by
  have h := correctedVerticalLinear_horizontal Q D p y u hy z
  rw [map_neg] at h
  exact neg_injective h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalConnection
