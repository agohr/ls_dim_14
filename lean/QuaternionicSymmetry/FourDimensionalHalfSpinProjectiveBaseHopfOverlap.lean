import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinActualTransition
import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplexOverlap

/-! The actual adapted-sphere coefficient transition sends the Hopf
coefficient of a projective spinor to that of its true spinor transition;
the equality also holds after antipodal reversal. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBaseHopfOverlap

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalTwistorNormalizerQuotient
  QuaternionicManifoldRotationCoordinates
  QuaternionicManifoldProductGaugeDifferential
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicNormalizerRotationAxes
  QuaternionicIsometryNormalizer
  QuaternionicManifoldFixedNormalizer
  QuaternionicManifoldPointwiseLifts
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorSphereBundle
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem rotatedCoefficient_projectiveHopf (p q : M) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hi : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      Q.frames.adaptedCore.baseSet (achart ℍ p))
    (hj : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      Q.frames.adaptedCore.baseSet (achart ℍ q))
    (v : ProjectiveSpinor) :
    rotatedCoefficient Q p q y hy (projectiveHopf v) =
      projectiveHopf (spinorTransition Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hi hj v) := by
  apply Subtype.ext
  rw [spinorTransition_hopf]
  change Q.reduction.rankThreeCoordChange (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) (projectiveHopf v).1 =
    rotationLinear leftLineStructure
      (fixedTransitionNormalizer leftLineStructure Q (achart ℍ p)
        (achart ℍ q) ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hi hj)
      (projectiveHopf v).1
  exact (rotationLinear_fixedTransition leftLineStructure Q
    (achart ℍ p) (achart ℍ q)
    ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hi hj _).symm

theorem rotatedCoefficient_antipodal (p q : M) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (a : coefficientSphere) :
    rotatedCoefficient Q p q y hy (antipodalCoefficient a) =
      antipodalCoefficient (rotatedCoefficient Q p q y hy a) := by
  apply Subtype.ext
  change Q.reduction.rankThreeCoordChange (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) (-a.1) =
    -(Q.reduction.rankThreeCoordChange (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) a.1)
  exact map_neg _ _

theorem rotatedCoefficient_antipodal_projectiveHopf (p q : M) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hi : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      Q.frames.adaptedCore.baseSet (achart ℍ p))
    (hj : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      Q.frames.adaptedCore.baseSet (achart ℍ q))
    (v : ProjectiveSpinor) :
    rotatedCoefficient Q p q y hy
      (antipodalCoefficient (projectiveHopf v)) =
      antipodalCoefficient
        (projectiveHopf (spinorTransition Q (achart ℍ p) (achart ℍ q)
          ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hi hj v)) := by
  rw [rotatedCoefficient_antipodal Q p q y hy,
    rotatedCoefficient_projectiveHopf Q p q y hy hi hj]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBaseHopfOverlap
