import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTransitionMFDeriv
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullMFDeriv

/-! The independent CP¹ local AHS operators are covariant under the
true manifold derivative of the literal projective-core transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveCoreTransitionGerm
  FourDimensionalHalfSpinProjectiveCoreTransitionMFDeriv
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem core_tensor_overlap_mfderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    let T := coreAffineTransition Q p q
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (localActualProjectiveAHS Q D p y z v) =
      localActualProjectiveAHS Q D q (φ y) (mobius (G y) z)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  dsimp
  rw [core_transition_mfderiv Q p q lift y hy hx z hden
      (localActualProjectiveAHS Q D p y z v)]
  rw [core_transition_mfderiv Q p q lift y hy hx z hden v]
  exact actual_projective_tensor_overlap Q D p q lift y 0 hy hx z hden v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv
