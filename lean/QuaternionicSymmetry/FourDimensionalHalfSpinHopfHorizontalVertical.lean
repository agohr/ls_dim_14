import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedVerticalComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedHorizontal

/-! The genuine corrected Hopf fiber mfderiv carries the projective
horizontal graph to the sphere horizontal graph, expressed in the
verified tangent-to-coefficient equivalence. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfHorizontalVertical

open scoped Manifold ContDiff Quaternion Matrix Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinHopfIndexedHorizontal
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinProjectiveConnection
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  ManifoldTwistorHorizontalConnection

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem indexedCorrectedHopf_zero_coefficient (z : ℂ) :
    indexedCorrectedHopf 0 z = coefficientSphereHomeomorph
      (antipodalCoefficient (hopfSphere ![1,z] (by simp))) := by
  change correctedHopf (affineSpinorPoint z) = _
  rw [correctedHopf_coefficient, affineSpinorPoint_hopf]

private theorem tangentEquiv_cast (a : coefficientSphere)
    (b : geometricSphere) (h : b = coefficientSphereHomeomorph a)
    (v : TangentSpace (𝓡 2) b) :
    (sphereTangentVerticalEquiv a (h ▸ v)).1 =
      (EuclideanSpace.equiv (Fin 3) ℝ) (sphereTangentMap b v) := by
  cases h
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem indexedCorrectedHopf_zero_horizontal_vertical
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ)
    (hpoint : indexedCorrectedHopf 0 z = coefficientSphereHomeomorph
      (antipodalCoefficient (hopfSphere ![1,z] (by simp)))) :
    sphereTangentVerticalEquiv
      (antipodalCoefficient (hopfSphere ![1,z] (by simp)))
      (hpoint ▸ mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z
        (-(projectiveConnectionGenerator Q D p y u z))) =
      -(connectionVertical Q D p y hy
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u) := by
  let a := antipodalCoefficient (hopfSphere ![1,z] (by simp))
  apply Subtype.ext
  change (sphereTangentVerticalEquiv a
    (hpoint ▸ (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z)
      (-(projectiveConnectionGenerator Q D p y u z)))).1 =
    -(connectionVertical Q D p y hy a u).1
  rw [tangentEquiv_cast a _ hpoint]
  rw [indexedCorrectedHopf_zero_horizontal_connection Q D p y u hy z]
  rw [map_neg]
  exact congrArg Neg.neg
    ((EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply
      ((connectionVertical Q D p y hy a u).1))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfHorizontalVertical
