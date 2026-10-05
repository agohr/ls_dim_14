import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphereDerivative
import QuaternionicSymmetry.ManifoldTwistorSphereAntipodalDerivative
import QuaternionicSymmetry.FourDimensionalTwistorAntipodalConnection

/-! The actual first affine-chart Hopf mfderiv takes the independent
projective horizontal connection graph to the induced rank-three sphere
connection graph.  The corrected map has the opposite fiber sign. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphereHorizontal

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfAffineDerivative
  FourDimensionalHalfSpinHopfAffineSphereDerivative
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinHopfSphere
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorSphereBundle
  QuaternionicUnitScalarIsometries
  ManifoldQuaternionicAdjointConnection

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem firstAffineSphere_horizontal_mfderiv
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (firstAffineSphere z)
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) firstAffineSphere z
        (-(projectiveConnectionGenerator Q D p y u z))) =
      -toEuclidean (inducedForm Q D p y u
        (hopfSphere ![1,z] (by simp)).1) := by
  rw [firstAffineSphere_tangent_fderiv,
    normalizedSpinorHopf_affine_fderiv Q D p y u hy z,
    map_neg, imaginaryEuclidean_pureScalar]

theorem correctedFirstAffineSphere_horizontal_mfderiv
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (geometricAntipodal (firstAffineSphere z))
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
        (geometricAntipodal ∘ firstAffineSphere) z
        (-(projectiveConnectionGenerator Q D p y u z))) =
      toEuclidean (inducedForm Q D p y u
        (hopfSphere ![1,z] (by simp)).1) := by
  have hcomp := mfderiv_comp z
    (geometricAntipodal_smooth.mdifferentiableAt (by simp))
    (firstAffineSphere_mdifferentiableAt z)
  rw [hcomp]
  change sphereTangentMap (geometricAntipodal (firstAffineSphere z))
    ((mfderiv (𝓡 2) (𝓡 2) geometricAntipodal (firstAffineSphere z))
      ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) firstAffineSphere z)
        (-(projectiveConnectionGenerator Q D p y u z)))) = _
  rw [sphereTangentMap_antipodal,
    firstAffineSphere_horizontal_mfderiv Q D p y u hy z]
  simp

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphereHorizontal
