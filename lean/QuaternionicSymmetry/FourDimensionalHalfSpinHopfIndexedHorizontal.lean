import QuaternionicSymmetry.FourDimensionalHalfSpinHopfCorrectedConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

/-! Identify the corrected affine Hopf calculation with the literal
projective-bundle chart map already used in the global block derivative. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedHorizontal

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfSphereHorizontal
  FourDimensionalHalfSpinHopfCorrectedConnection
  FourDimensionalHalfSpinHopfAffineSphereDerivative
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorHorizontalConnection
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem indexedCorrectedHopf_zero_eq (z : ℂ) :
    indexedCorrectedHopf 0 z =
      geometricAntipodal (firstAffineSphere z) := by
  change correctedHopf (affineSpinorPoint z) = _
  change geometricAntipodal (projectiveHopfGeometric (affineSpinorPoint z)) = _
  congr 1
  rw [affineSpinorPoint_eq_projectiveChart,
    projectiveHopfGeometric_chart]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem indexedCorrectedHopf_zero_horizontal_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (indexedCorrectedHopf 0 z)
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z
        (-(projectiveConnectionGenerator Q D p y u z))) =
      -toEuclidean ((connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u).1) := by
  have hfun : indexedCorrectedHopf 0 =
      geometricAntipodal ∘ firstAffineSphere := by
    funext t; exact indexedCorrectedHopf_zero_eq t
  rw [hfun]
  exact correctedFirstAffineSphere_horizontal_connection Q D p y u hy z

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedHorizontal
