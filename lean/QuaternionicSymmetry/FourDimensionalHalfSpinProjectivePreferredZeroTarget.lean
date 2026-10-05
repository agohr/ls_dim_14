import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredZeroOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualCoreAffine

/-! The arbitrary target adapted trivialization of a globally chosen
first-affine projective point has exactly the Möbius fiber coordinate in
the independently constructed bundle core. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredZeroTarget

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectivePreferredAffinePoint
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveActualCoreAffine
  FourDimensionalHalfSpinActualTransitionSmooth
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem preferred_zero_target_fiber (z : SpinorBundleTotal Q)
    (hzero : preferredProjectiveChartIndex z.2 = 0)
    (q : M) (lift : unitary ℍ)
    (hx : z.1 ∈ liftNeighborhood Q (achart ℍ z.1) (achart ℍ q) lift)
    (hden : chartDen
      (halfSpinMatrix
        (scalarChart Q z.1 (achart ℍ z.1) (achart ℍ q) lift
          (extChartAt 𝓘(ℝ, ℍ) z.1 z.1)))
      (preferredProjectiveScalar z.2) ≠ 0) :
    ((projectiveChart 1 0)
      (((projectiveSpinorCore Q).localTriv (achart ℍ q)) z).2) 0 =
      mobius (halfSpinMatrix
        (scalarChart Q z.1 (achart ℍ z.1) (achart ℍ q) lift
          (extChartAt 𝓘(ℝ, ℍ) z.1 z.1)))
        (preferredProjectiveScalar z.2) := by
  have hy : (extChartAt 𝓘(ℝ, ℍ) z.1).symm
      (extChartAt 𝓘(ℝ, ℍ) z.1 z.1) = z.1 :=
    (extChartAt 𝓘(ℝ, ℍ) z.1).left_inv (mem_extChartAt_source z.1)
  rw [(projectiveSpinorCore Q).localTriv_apply]
  change ((projectiveChart 1 0)
    (spinorCoordChange Q (achart ℍ z.1) (achart ℍ q)
      (z.1,z.2))) 0 = _
  conv_lhs => rw [preferred_zero_affinePoint z.2 hzero]
  have h := actual_core_affine_transition Q z.1 q lift
    (extChartAt 𝓘(ℝ, ℍ) z.1 z.1) (by rw [hy]; exact hx)
    (preferredProjectiveScalar z.2) hden
  simpa only [hy] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredZeroTarget
