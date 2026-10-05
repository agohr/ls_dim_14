import QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalDirectConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfGraphAlgebra

/-! The corrected Hopf fiber differential intertwines the independently
defined local projective and sphere connection-graph complex tensors. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinHopfVerticalDirect
  FourDimensionalHalfSpinHopfVerticalDirectConnection
  FourDimensionalHalfSpinHopfGraphAlgebra
  ManifoldTwistorHorizontalConnection
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  ManifoldQuaternionicMetric

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sphereGraphComplex_eq_local (p : M) (y : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (a : coefficientSphere) :
    sphereGraphComplex (chartBaseComplex Q p y a).toLinearMap
      (connectionVertical Q D p y hy a) (verticalComplex a) =
      localTwistorComplex Q D p y hy a := by
  apply LinearMap.ext
  intro uv
  apply Prod.ext
  · rfl
  · change verticalComplex a (uv.2 + connectionVertical Q D p y hy a uv.1) -
      connectionVertical Q D p y hy a (chartBaseComplex Q p y a uv.1) =
      verticalComplex a (uv.2 + connectionVertical Q D p y hy a uv.1) -
      connectionVertical Q D p y hy a (chartBaseComplex Q p y a uv.1)
    rfl

theorem correctedHopf_localTensor_intertwining (p : M) (y : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (z : ℂ) (uw : ℍ × ℂ) :
    (fun v : ℍ × ℂ => (v.1, projectiveVerticalDerivative z v.2))
      (localActualProjectiveAHS Q D p y z uw) =
      localTwistorComplex Q D p y hy
        (antipodalCoefficient (projectiveHopf (affineSpinorPoint z)))
        (uw.1, projectiveVerticalDerivative z uw.2) := by
  let a := antipodalCoefficient (projectiveHopf (affineSpinorPoint z))
  have ha : a = antipodalCoefficient (FourDimensionalHalfSpinHopfSphere.hopfSphere
      ![1,z] (by simp)) := by
    exact congrArg antipodalCoefficient (affineSpinorPoint_hopf z)
  have hv (w : ℂ) :
      projectiveVerticalDerivative z (Complex.I * w) =
      verticalComplex a (projectiveVerticalDerivative z w) :=
    projectiveVerticalDerivative_complex (Q.reduction.Q (achart ℍ p)) z w
  have hh (u : ℍ) :
      projectiveVerticalDerivative z (localConnectionGenerator Q D p y z u) =
      connectionVertical Q D p y hy a u := by
    exact projectiveVerticalDerivative_connection Q D p y u hy z
  rw [localActualProjectiveAHS, ← ha]
  rw [← sphereGraphComplex_eq_local Q D p y hy a]
  exact graphComplex_intertwining
    (chartBaseComplex Q p y a).toLinearMap
    (localConnectionGenerator Q D p y z)
    (projectiveVerticalDerivative z)
    (connectionVertical Q D p y hy a)
    (verticalComplex a) hv hh uw

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalTensor
