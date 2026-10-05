import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartTensorDescent

/-! The local-lift choice is eliminated from the all-four-chart tensor
descent: the existing normalizer-lift theorem supplies one near every
actual base-chart overlap point. The remaining premise is exactly
membership of the transformed fiber point in the target affine chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAtlasTensorDescent

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveChartTensorDescent
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinActualTransitionSmooth
  ComplexProjectiveTopology
  QuaternionicManifoldLocalScalarLifts
  ManifoldQuaternionicConnection
  QuaternionicProjectiveStandardHilbertStructure
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem indexed_core_tensor_overlap_on_chart_domain
    (i j : Fin 2) (p q : M)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (z : ℂ)
    (hmem : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y,
          indexedSourcePoint i z) ∈ affineDomain 1 j)
    (v : ℍ × ℂ) :
    let T := indexedCoreTransition Q i j p q
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (indexedLocalTensor Q D i p y z v) =
      indexedLocalTensor Q D j q (T (y,z)).1 (T (y,z)).2
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  let x := (extChartAt 𝓘(ℝ, ℍ) p).symm y
  have hp0 : x ∈ (extChartAt 𝓘(ℝ, ℍ) p).source :=
    (extChartAt 𝓘(ℝ, ℍ) p).map_target hy.1
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart ℍ p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, ℍ)] using hp0
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart ℍ q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, ℍ)] using hy.2
  obtain ⟨lift, hx, _, _, _⟩ :=
    exists_local_scalar_lift Q leftLineStructure
      (achart ℍ p) (achart ℍ q) x hp hq
  exact indexed_core_tensor_overlap_of_target_mem Q D i j p q lift y hy hx z hmem v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAtlasTensorDescent
