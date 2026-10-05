import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullMFDeriv
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartOverlap

/-! The second projective affine chart glues by the actual derivative of
the inversion coordinate transition, completing the two local derivative
overlap laws without transporting a complex structure from the sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartMFDeriv

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFullTransitionDerivative
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveFiberChartOverlap
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor

noncomputable section

def fiberSwap (t : ℍ × ℂ) : ℍ × ℂ :=
  jointProjectiveTransition id (fun _ => coordinateSwap) t

theorem fiberSwap_mfderiv (y : ℍ) (z : ℂ) (hz : z ≠ 0)
    (v : ℍ × ℂ) :
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) fiberSwap (y,z) v =
      tangentTransition (LinearMap.id : ℍ →ₗ[ℝ] ℍ)
        (0 : ℍ →ₗ[ℝ] ℂ)
        (complexMulReal (deriv (mobius coordinateSwap) z)) v := by
  have hden : chartDen coordinateSwap z ≠ 0 := by
    simpa [chartDen, coordinateSwap] using hz
  have h := full_transition_fderiv id (fun _ : ℍ => coordinateSwap)
    y z differentiableAt_id (differentiableAt_const coordinateSwap) hden v
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (jointProjectiveTransition id (fun _ => coordinateSwap)) (y,z) v = _
  simpa [fderiv_id, fderiv_const, tangentTransition] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem actual_fiber_chart_overlap_mfderiv (p : M) (y : ℍ)
    (z : ℂ) (hz : z ≠ 0) (v : ℍ × ℂ) :
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) fiberSwap (y,z)
      (localActualProjectiveAHS Q D p y z v) =
      secondLocalActualProjectiveAHS Q D p y (mobius coordinateSwap z)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) fiberSwap (y,z) v) := by
  rw [fiberSwap_mfderiv y z hz (localActualProjectiveAHS Q D p y z v)]
  rw [fiberSwap_mfderiv y z hz v]
  exact local_tensor_fiber_chart_overlap Q D p y z hz v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartMFDeriv
