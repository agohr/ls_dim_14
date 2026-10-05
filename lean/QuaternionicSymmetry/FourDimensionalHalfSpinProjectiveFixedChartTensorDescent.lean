import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartMFDeriv
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAtlasTensorDescent

/-! The independent local projective AHS tensors transform under the
actual derivative of the independently constructed total-space fixed
affine-chart composition. Only genuine base and target-fiber chart
membership is assumed. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTensorDescent

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartMFDeriv
  FourDimensionalHalfSpinProjectiveAtlasTensorDescent
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinActualTransitionSmooth
  ManifoldQuaternionicConnection
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem fixed_chart_tensor_overlap_mfderiv
    (i j : Fin 2) (p q : M)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (z : ℂ)
    (hmem : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y,
          indexedSourcePoint i z) ∈ affineDomain 1 j)
    (v : ℍ × ℂ) :
    let T := fun t : ℍ × ℂ => fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i t)
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (indexedLocalTensor Q D i p y z v) =
      indexedLocalTensor Q D j q (T (y,z)).1 (T (y,z)).2
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  dsimp
  rw [fixedProjectiveChart_transition_mfderiv Q p q i j y hy z]
  rw [fixedProjectiveChart_transition Q p q i j y hy z]
  exact indexed_core_tensor_overlap_on_chart_domain Q D i j p q y hy z hmem v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTensorDescent
