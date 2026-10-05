import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedGerm
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedMFDeriv

/-! The independently constructed literal projective bundle-core
coordinate change from affine chart 0 to affine chart 1 intertwines the
independent local AHS operators under its actual manifold derivative.
This upgrades the refined-frame formula by the checked core germ. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedTensor

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveCoreMixedGerm
  FourDimensionalHalfSpinProjectiveActualMixedMFDeriv
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
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

theorem core_mixed_tensor_overlap_mfderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    let T := coreMixedTransition Q p q
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (localActualProjectiveAHS Q D p y z v) =
      secondLocalActualProjectiveAHS Q D q (φ y)
        (mixedMobius (G y) z)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  dsimp
  have heq := coreMixedTransition_eventuallyEq Q p q lift y hy hx z hden
  rw [heq.mfderiv_eq (I := 𝓘(ℝ, ℍ × ℂ))
    (I' := 𝓘(ℝ, ℍ × ℂ))]
  exact actual_mixed_tensor_overlap_mfderiv Q D p q lift
    y hy hx z hden v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreMixedTensor
