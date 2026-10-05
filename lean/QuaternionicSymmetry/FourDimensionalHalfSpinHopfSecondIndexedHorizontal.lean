import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondCorrectedConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative

/-! Identify the second affine calculation with the literal indexed
corrected Hopf fiber map used by the independent bundle atlas. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondIndexedHorizontal

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfSecondCorrectedConnection
  FourDimensionalHalfSpinHopfSecondSphereDerivative
  FourDimensionalHalfSpinProjectiveSecondTensor
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorHorizontalConnection
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem indexedCorrectedHopf_one_eq (z : ℂ) :
    indexedCorrectedHopf 1 z =
      geometricAntipodal (secondAffineSphere z) := by
  change correctedHopf (secondAffineSpinorPoint z) = _
  change geometricAntipodal
    (projectiveHopfGeometric (secondAffineSpinorPoint z)) = _
  congr 1
  rw [secondAffineSpinorPoint, projectiveHopfGeometric_chart]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem indexedCorrectedHopf_one_horizontal_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (indexedCorrectedHopf 1 z)
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z
        (-(secondLocalConnectionGenerator Q D p y z u))) =
      -toEuclidean ((connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![z,1] (by simp))) u).1) := by
  have hfun : indexedCorrectedHopf 1 =
      geometricAntipodal ∘ secondAffineSphere := by
    funext t; exact indexedCorrectedHopf_one_eq t
  rw [hfun]
  exact correctedSecondAffineSphere_horizontal_connection Q D p y u hy z

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondIndexedHorizontal
