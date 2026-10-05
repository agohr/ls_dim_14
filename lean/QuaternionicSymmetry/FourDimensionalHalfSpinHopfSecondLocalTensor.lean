import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondVerticalDirect
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfGraphAlgebra
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalTensor

/-! The literal second affine corrected-Hopf differential intertwines
the independently defined second local projective tensor with the
genuine sphere connection tensor, including the second-chart pole. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondLocalTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinHopfSecondVerticalDirect
  FourDimensionalHalfSpinHopfGraphAlgebra
  ManifoldTwistorHorizontalConnection
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfSphere
  ManifoldQuaternionicMetric

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem correctedHopf_secondLocalTensor_intertwining (p : M) (y : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (z : ℂ) (uw : ℍ × ℂ) :
    (fun v : ℍ × ℂ => (v.1, secondProjectiveVerticalDerivative z v.2))
      (secondLocalActualProjectiveAHS Q D p y z uw) =
      localTwistorComplex Q D p y hy
        (antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z)))
        (uw.1, secondProjectiveVerticalDerivative z uw.2) := by
  let a := antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z))
  have ha : a = antipodalCoefficient (hopfSphere ![z,1] (by simp)) := by
    exact congrArg antipodalCoefficient (secondAffineSpinorPoint_hopf z)
  have hv (w : ℂ) :
      secondProjectiveVerticalDerivative z (Complex.I * w) =
      verticalComplex a (secondProjectiveVerticalDerivative z w) :=
    secondProjectiveVerticalDerivative_complex
      (Q.reduction.Q (achart ℍ p)) z w
  have hh (u : ℍ) :
      secondProjectiveVerticalDerivative z
        (secondLocalConnectionGenerator Q D p y z u) =
      connectionVertical Q D p y hy a u := by
    exact secondProjectiveVerticalDerivative_connection Q D p y u hy z
  rw [secondLocalActualProjectiveAHS, ← ha]
  rw [← FourDimensionalHalfSpinHopfLocalTensor.sphereGraphComplex_eq_local
    Q D p y hy a]
  exact graphComplex_intertwining
    (chartBaseComplex Q p y a).toLinearMap
    (secondLocalConnectionGenerator Q D p y z)
    (secondProjectiveVerticalDerivative z)
    (connectionVertical Q D p y hy a)
    (verticalComplex a) hv hh uw

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondLocalTensor
