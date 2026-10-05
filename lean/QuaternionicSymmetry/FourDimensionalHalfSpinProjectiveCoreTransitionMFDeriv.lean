import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTransitionGerm
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullMFDeriv

/-! The literal independently constructed projective-bundle core
transition has exactly the full block manifold derivative used in the
local projective almost-complex overlap. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTransitionMFDeriv

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveCoreTransitionGerm
  FourDimensionalHalfSpinProjectiveActualFullTransition
  FourDimensionalHalfSpinProjectiveFullTransitionDerivative
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem core_transition_mfderiv (p q : M) (lift : unitary ℍ)
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
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
        (coreAffineTransition Q p q) (y,z) v =
      tangentTransition (fderiv ℝ φ y).toLinearMap
        (fderiv ℝ (fun t => mobius (G t) z) y).toLinearMap
        (complexMulReal (deriv (mobius (G y)) z)) v := by
  dsimp
  rw [mfderiv_eq_fderiv]
  have heq := coreAffineTransition_eventuallyEq Q p q lift y hy hx z hden
  rw [heq.fderiv_eq]
  exact actual_full_transition_fderiv Q p q lift y hy hx z hden v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTransitionMFDeriv
