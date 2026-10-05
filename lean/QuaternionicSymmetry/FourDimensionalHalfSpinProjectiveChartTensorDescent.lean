import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualChartDomain

/-! Literal projective bundle-core tensor covariance on every refined
adapted overlap and every source/target CP¹ affine chart. The only fiber
hypothesis is actual target-chart membership, which is inherent in a
genuine chart overlap; matrix nonvanishing is derived internally. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartTensorDescent

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveActualChartDomain
  FourDimensionalHalfSpinActualTransitionSmooth
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem indexed_core_tensor_overlap_of_target_mem
    (i j : Fin 2) (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hmem : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y,
          FourDimensionalHalfSpinProjectiveAllCoreChartDomain.indexedSourcePoint i z) ∈
        affineDomain 1 j)
    (v : ℍ × ℂ) :
    let T := indexedCoreTransition Q i j p q
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (indexedLocalTensor Q D i p y z v) =
      indexedLocalTensor Q D j q (T (y,z)).1 (T (y,z)).2
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  exact indexed_core_tensor_overlap_mfderiv Q D i j p q lift y hy hx z
    (core_denominator_ne_zero_of_target_mem Q i j p q lift y hx z hmem) v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartTensorDescent
