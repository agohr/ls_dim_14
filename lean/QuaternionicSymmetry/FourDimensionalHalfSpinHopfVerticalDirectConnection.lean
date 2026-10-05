import QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalDirect
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedHorizontal

/-! The direct corrected Hopf fiber differential preserves the literal
connection horizontal graph; no equality transport appears in this
projective-representative formulation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalDirectConnection

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfVerticalDirect
  FourDimensionalHalfSpinHopfIndexedHorizontal
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfSphere
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorVerticalComplex
  ManifoldTwistorHorizontalConnection

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem projectiveVerticalDerivative_horizontal
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    projectiveVerticalDerivative z
      (-(projectiveConnectionGenerator Q D p y u z)) =
      -(connectionVertical Q D p y hy
        (antipodalCoefficient (projectiveHopf (affineSpinorPoint z))) u) := by
  let a := antipodalCoefficient (projectiveHopf (affineSpinorPoint z))
  apply Subtype.ext
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (coefficientSphereHomeomorph a)
        (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z
          (-(projectiveConnectionGenerator Q D p y u z)))) = _
  have hpoint : indexedCorrectedHopf 0 z = coefficientSphereHomeomorph a := by
    change correctedHopf (affineSpinorPoint z) = _
    exact correctedHopf_coefficient _
  rw [← hpoint, indexedCorrectedHopf_zero_horizontal_connection Q D p y u hy z]
  rw [← affineSpinorPoint_hopf z]
  rw [map_neg]
  exact congrArg Neg.neg
    ((EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply
      ((connectionVertical Q D p y hy a u).1))

theorem projectiveVerticalDerivative_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    projectiveVerticalDerivative z
      (projectiveConnectionGenerator Q D p y u z) =
      connectionVertical Q D p y hy
        (antipodalCoefficient (projectiveHopf (affineSpinorPoint z))) u := by
  have h := projectiveVerticalDerivative_horizontal Q D p y u hy z
  rw [map_neg] at h
  exact neg_injective h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalDirectConnection
