import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondSphereDerivative
import QuaternionicSymmetry.ManifoldTwistorSphereAntipodalDerivative
import QuaternionicSymmetry.ManifoldTwistorHorizontalConnection

/-! The corrected `[z:1]` Hopf derivative takes the second genuine
projective horizontal graph to the induced rank-three sphere graph. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondCorrectedConnection

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinHopfSecondSphereDerivative
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

theorem correctedSecondAffineSphere_horizontal_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (geometricAntipodal (secondAffineSphere z))
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
        (geometricAntipodal ∘ secondAffineSphere) z
        (-(secondLocalConnectionGenerator Q D p y z u))) =
      -toEuclidean ((connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![z,1] (by simp))) u).1) := by
  have hcomp := mfderiv_comp z
    (geometricAntipodal_smooth.mdifferentiableAt (by simp))
    (secondAffineSphere_mdifferentiableAt z)
  rw [hcomp]
  change sphereTangentMap (geometricAntipodal (secondAffineSphere z))
    ((mfderiv (𝓡 2) (𝓡 2) geometricAntipodal (secondAffineSphere z))
      ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) secondAffineSphere z)
        (-(secondLocalConnectionGenerator Q D p y z u)))) = _
  rw [sphereTangentMap_antipodal,
    secondAffineSphere_horizontal_mfderiv Q D p y u hy z]
  simp only [neg_neg]
  let a := hopfSphere ![z,1] (by simp)
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
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondCorrectedConnection
