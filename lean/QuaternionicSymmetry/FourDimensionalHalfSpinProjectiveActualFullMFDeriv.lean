import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullTransition

/-! The local independent projective almost-complex tensors intertwine by
the true manifold derivative of the complete base-plus-fiber transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullMFDeriv

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveActualFullTransition
  FourDimensionalHalfSpinProjectiveFullTransitionDerivative
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveLocalAHS
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem actual_projective_tensor_overlap_mfderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (FourDimensionalHalfSpinMatrix.halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => FourDimensionalHalfSpinMatrix.halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    let T := jointProjectiveTransition φ G
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (localActualProjectiveAHS Q D p y z v) =
      localActualProjectiveAHS Q D q (φ y) (mobius (G y) z)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
  dsimp
  rw [mfderiv_eq_fderiv]
  have hleft := actual_full_transition_fderiv Q p q lift y hy hx z hden
    (localActualProjectiveAHS Q D p y z v)
  have hright := actual_full_transition_fderiv Q p q lift y hy hx z hden v
  have htransport := actual_projective_tensor_overlap Q D p q lift y 0 hy hx z hden v
  dsimp at hleft hright htransport
  exact hleft.trans (htransport.trans (congrArg _ hright.symm))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullMFDeriv
