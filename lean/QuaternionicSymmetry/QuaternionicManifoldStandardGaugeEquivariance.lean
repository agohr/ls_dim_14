import QuaternionicSymmetry.QuaternionicManifoldProductRepresentationPointwise

/-! Pointwise equivariance of the standard Lie action for the actual
locally lifted manifold tangent transition. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardGaugeEquivariance

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldProductRepresentationPointwise
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicProjectiveProductEquivariance
open QuaternionicProjectiveStandardLie
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem standardLie_fixedGauge_conjugation (p q : M) (lift : unitary ℍ)
    (y : E) (hy : y ∈ ManifoldQuaternionicConnection.chartOverlap
      (I := 𝓘(ℝ, E)) p q)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift)
    (A : E →L[ℝ] E)
    (hA : ∀ a, QuaternionicLieAlgebraProjection.symplecticProjection S A * synth S a =
      synth S a * QuaternionicLieAlgebraProjection.symplecticProjection S A) :
    standardLie S (fixedGaugeInv S Q p q y * A * fixedGauge S Q p q y) =
      standardChartInverse S Q p (achart E p) (achart E q) lift y *
        standardLie S A *
          standardChart S Q p (achart E p) (achart E q) lift y := by
  let t := QuaternionicManifoldSignedLocalLifts.localProductLift S Q
    (achart E p) (achart E q) lift
      ((extChartAt 𝓘(ℝ, E) p).symm y) hx
  rw [fixedGauge_eq_localProductLift S Q p q lift y hx,
    fixedGaugeInv_eq_localProductLift S Q p q lift y hy hx,
    standardChart_eq_localProductLift S Q p q lift y hx,
    standardChartInverse_eq_localProductLift S Q p q lift y hx]
  change standardLie S
      (QuaternionicIsometryNormalizer.conjugation
        (QuaternionicUnitScalarIsometries.symplecticProductAction S t).1.symm A) =
      (QuaternionicProjectiveStandardL2.standardActionL2 S t).symm.toContinuousLinearMap *
        standardLie S A *
          (QuaternionicProjectiveStandardL2.standardActionL2 S t).toContinuousLinearMap
  exact standardLie_conjugation_product_inv S t A hA

end
end QuaternionicSymmetry.QuaternionicManifoldStandardGaugeEquivariance
