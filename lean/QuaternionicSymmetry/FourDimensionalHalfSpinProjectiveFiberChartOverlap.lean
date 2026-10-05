import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondHopf
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

/-! The independently constructed projective tensor agrees on the
intersection of the two genuine CP¹ affine fiber charts, via inversion.
This supplies the fiber-atlas gluing complement to adapted-base overlaps. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinProjectiveChartSwapConnection
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveSecondHopf
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem local_tensor_fiber_chart_overlap (p : M) (y : ℍ)
    (z : ℂ) (hz : z ≠ 0) (v : ℍ × ℂ) :
    let H := complexMulReal (deriv (mobius coordinateSwap) z)
    tangentTransition (LinearMap.id : ℍ →ₗ[ℝ] ℍ)
      (0 : ℍ →ₗ[ℝ] ℂ) H
      (localActualProjectiveAHS Q D p y z v) =
    secondLocalActualProjectiveAHS Q D p y (mobius coordinateSwap z)
      (tangentTransition (LinearMap.id : ℍ →ₗ[ℝ] ℍ)
        (0 : ℍ →ₗ[ℝ] ℂ) H v) := by
  dsimp
  let w := mobius coordinateSwap z
  let H := complexMulReal (deriv (mobius coordinateSwap) z)
  let Jp := (chartBaseComplex Q p y
    (antipodalCoefficient (hopfSphere ![1,z] (by simp)))).toLinearMap
  let Jq := (chartBaseComplex Q p y
    (antipodalCoefficient (hopfSphere ![w,1] (by simp)))).toLinearMap
  let Kp := localConnectionGenerator Q D p y z
  let Kq := secondLocalConnectionGenerator Q D p y w
  have hhopf : hopfSphere ![w,1] (by simp) =
      hopfSphere ![1,z] (by simp) := by
    calc
      hopfSphere ![w,1] (by simp) =
          hopfSphere ![z⁻¹,1] (by simp) := by
            congr 1
            simp [w, swap_mobius]
      _ = hopfSphere ![1,z] (by simp) := hopfSphere_inversion z hz
  have hbase : ∀ u, (LinearMap.id : ℍ →ₗ[ℝ] ℍ) (Jp u) =
      Jq ((LinearMap.id : ℍ →ₗ[ℝ] ℍ) u) := by
    intro u
    simpa only [LinearMap.id_apply, Jp, Jq, hhopf]
  have hvert : ∀ b, H (Complex.I * b) = Complex.I * H b := by
    intro b
    simp [H, complexMulReal]
    ring
  have hhoriz : ∀ u, (0 : ℍ →ₗ[ℝ] ℂ) u + H (-(Kp u)) =
      -(Kq ((LinearMap.id : ℍ →ₗ[ℝ] ℍ) u)) := by
    intro u
    have h := secondChart_generator_inversion
      (spinorMatrixForm Q D p y u) z hz
    simpa [H, Kp, Kq, w, complexMulReal,
      localConnectionGenerator_apply,
      secondLocalConnectionGenerator_apply,
      projectiveConnectionGenerator, mul_neg] using congrArg Neg.neg h
  change tangentTransition (LinearMap.id : ℍ →ₗ[ℝ] ℍ)
      (0 : ℍ →ₗ[ℝ] ℂ) H (graphComplex Jp Kp v) =
    graphComplex Jq Kq
      (tangentTransition (LinearMap.id : ℍ →ₗ[ℝ] ℍ)
        (0 : ℍ →ₗ[ℝ] ℂ) H v)
  exact graphComplex_overlap Jp Jq _ Kp Kq _ H
    hbase hvert hhoriz v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartOverlap
