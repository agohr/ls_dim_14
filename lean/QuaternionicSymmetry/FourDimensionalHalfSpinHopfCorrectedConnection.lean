import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphereHorizontal
import QuaternionicSymmetry.ManifoldTwistorHorizontalConnection

/-! The corrected first affine Hopf differential sends the independent
projective horizontal generator to minus the genuine sphere connection
vertical term at the antipodal coefficient. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfCorrectedConnection

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfSphereHorizontal
  FourDimensionalHalfSpinHopfAffineSphereDerivative
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinHopfSphere
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorSphereBundle
  ManifoldTwistorHorizontalConnection
  ManifoldQuaternionicAdjointConnection
  FourDimensionalHalfSpinAntipodalVerticalSign

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem correctedFirstAffineSphere_horizontal_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (geometricAntipodal (firstAffineSphere z))
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
        (geometricAntipodal ∘ firstAffineSphere) z
        (-(projectiveConnectionGenerator Q D p y u z))) =
      -toEuclidean ((connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u).1) := by
  rw [correctedFirstAffineSphere_horizontal_mfderiv Q D p y u hy z]
  let a := hopfSphere ![1,z] (by simp)
  have hconnection : (connectionVertical Q D p y hy
      (antipodalCoefficient a) u).1 =
      -(inducedForm Q D p y u a.1) := by
    change inducedForm Q D p y u (-a.1) = _
    exact (inducedForm Q D p y u).map_neg a.1
  change toEuclidean (inducedForm Q D p y u a.1) =
    -toEuclidean ((connectionVertical Q D p y hy
      (antipodalCoefficient a) u).1)
  rw [hconnection]
  simp [toEuclidean]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfCorrectedConnection
