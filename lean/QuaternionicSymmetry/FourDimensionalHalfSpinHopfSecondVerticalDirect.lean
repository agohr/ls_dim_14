import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondVerticalComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondIndexedHorizontal

/-! Direct coefficient-plane form of the second corrected Hopf
fiber differential, with no transport across an artificial equality. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondVerticalDirect

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinHopfSecondVerticalComplex
  FourDimensionalHalfSpinHopfSecondIndexedHorizontal
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfSphere
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  ManifoldTwistorHorizontalConnection

noncomputable section

def secondProjectiveVerticalDerivative (z : ℂ) :
    ℂ →ₗ[ℝ] verticalSubmodule
      (antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z))) :=
  (sphereTangentVerticalEquiv
    (antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z)))).toLinearMap.comp
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z).toLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem secondProjectiveVerticalDerivative_complex
    (S : QuaternionicStructure E) (z w : ℂ) :
    secondProjectiveVerticalDerivative z (Complex.I * w) =
      verticalComplex
        (antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z)))
        (secondProjectiveVerticalDerivative z w) := by
  let a := antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z))
  change sphereTangentVerticalEquiv a
      ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z)
        (Complex.I * w)) =
    verticalComplex a
      (sphereTangentVerticalEquiv a
        ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z) w))
  have hcomplex := indexedCorrectedHopf_one_mfderiv_complex S z w
  simp only [smul_eq_mul] at hcomplex
  rw [hcomplex]
  change sphereTangentVerticalEquiv a
      ((sphereTangentVerticalEquiv a).symm
        (verticalComplex a
          (sphereTangentVerticalEquiv a
            ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
              (indexedCorrectedHopf 1) z) w)))) = _
  rw [LinearEquiv.apply_symm_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem secondProjectiveVerticalDerivative_horizontal
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    secondProjectiveVerticalDerivative z
      (-(secondLocalConnectionGenerator Q D p y z u)) =
      -(connectionVertical Q D p y hy
        (antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z))) u) := by
  let a := antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z))
  apply Subtype.ext
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (coefficientSphereHomeomorph a)
        (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) z
          (-(secondLocalConnectionGenerator Q D p y z u)))) = _
  have hpoint : indexedCorrectedHopf 1 z = coefficientSphereHomeomorph a := by
    change ManifoldTwistorCorrectedHopf.correctedHopf
      (secondAffineSpinorPoint z) = _
    exact ManifoldTwistorCorrectedHopf.correctedHopf_coefficient _
  rw [← hpoint, indexedCorrectedHopf_one_horizontal_connection Q D p y u hy z]
  rw [← FourDimensionalHalfSpinProjectiveActualSecondBaseComplex.secondAffineSpinorPoint_hopf z]
  rw [map_neg]
  exact congrArg Neg.neg
    ((EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply
      ((connectionVertical Q D p y hy a u).1))

theorem secondProjectiveVerticalDerivative_connection
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    secondProjectiveVerticalDerivative z
      (secondLocalConnectionGenerator Q D p y z u) =
      connectionVertical Q D p y hy
        (antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint z))) u := by
  have h := secondProjectiveVerticalDerivative_horizontal Q D p y u hy z
  rw [map_neg] at h
  exact neg_injective h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondVerticalDirect
