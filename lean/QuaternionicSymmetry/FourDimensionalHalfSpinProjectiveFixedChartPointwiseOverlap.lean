import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTargetMembership

/-! The all-four affine tensor covariance is specialized to a literal point
of the independently charted projective-spinor bundle. No transformed-fiber
membership is supplied: it follows from actual target chart membership. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPointwiseOverlap

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartTensorDescent
  FourDimensionalHalfSpinProjectiveFixedChartTargetMembership
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  ManifoldQuaternionicConnection
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem fixed_chart_tensor_overlap_at_actual_point
    (p q : M) (i j : Fin 2) (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hq : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) q).source)
    (hi : ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈
      affineDomain 1 i)
    (hj : ((projectiveSpinorCore Q).localTriv (achart ℍ q) z).2 ∈
      affineDomain 1 j)
    (v : ℍ × ℂ) :
    let c := fixedProjectiveChart Q p i z
    let T := fun t : ℍ × ℂ => fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i t)
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T c
      (indexedLocalTensor Q D i p c.1 c.2 v) =
    indexedLocalTensor Q D j q (T c).1 (T c).2
      (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T c v) := by
  have hy : (fixedProjectiveChart Q p i z).1 ∈
      chartOverlap (I := 𝓘(ℝ, ℍ)) p q := by
    constructor
    · change (extChartAt 𝓘(ℝ, ℍ) p) z.1 ∈
        (extChartAt 𝓘(ℝ, ℍ) p).target
      exact (extChartAt 𝓘(ℝ, ℍ) p).map_source hp
    · change (extChartAt 𝓘(ℝ, ℍ) p).symm
        ((extChartAt 𝓘(ℝ, ℍ) p) z.1) ∈
        (extChartAt 𝓘(ℝ, ℍ) q).source
      rw [(extChartAt 𝓘(ℝ, ℍ) p).left_inv hp]
      exact hq
  have hmem := spinorCoordChange_target_mem Q p q i j z hp hq hi hj
  exact fixed_chart_tensor_overlap_mfderiv Q D i j p q
    (fixedProjectiveChart Q p i z).1 hy
    (fixedProjectiveChart Q p i z).2 hmem v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPointwiseOverlap
