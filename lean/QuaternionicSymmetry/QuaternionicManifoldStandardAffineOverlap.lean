import QuaternionicSymmetry.QuaternionicManifoldStandardGaugeDerivative
import QuaternionicSymmetry.QuaternionicManifoldStandardLieComparison

/-! The actual local standard connection obeys the affine gauge law on
every refined overlap carrying the explicit smooth product lift. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardAffineOverlap

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicManifoldStandardGaugeEquivariance
open QuaternionicManifoldStandardGaugeDerivative
open QuaternionicManifoldStandardLieComparison
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicProjectiveStandardLie
open ManifoldQuaternionicConnection
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem standardConnection_affine_refined (p q : M) (lift : unitary ℍ)
    (y : E) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardConnection S Q D p y =
      LocalConnectionGauge.transform
        (LocalConnectionCoordinatePullback.pullback
          (standardConnection S Q D q)
          (chartTransition (I := 𝓘(ℝ, E)) p q))
        (standardChart S Q p (achart E p) (achart E q) lift)
        (fun z => standardChartInverse S Q p (achart E p) (achart E q) lift z) y := by
  apply ContinuousLinearMap.ext
  intro u
  let φ := chartTransition (I := 𝓘(ℝ, E)) p q
  let v := fderiv ℝ φ y u
  let A := fixedForm S Q D q (φ y) v
  let F := fixedGauge S Q p q
  let H := fixedGaugeInv S Q p q
  let G := standardChart S Q p (achart E p) (achart E q) lift
  let K := standardChartInverse S Q p (achart E p) (achart E q) lift
  have hqy : φ y ∈ (extChartAt 𝓘(ℝ, E) q).target :=
    (extChartAt 𝓘(ℝ, E) q).map_source hy.2
  have hP : standardConnection S Q D p y u =
      standardLie S (fixedForm S Q D p y u) := by
    rw [standardConnection_eq_standardLie S Q D p y u hy.1, fixedForm_apply]
  have hQ : standardConnection S Q D q (φ y) v = standardLie S A := by
    rw [standardConnection_eq_standardLie S Q D q (φ y) v hqy]
    exact congrArg (standardLie S) (fixedForm_apply S Q D q (φ y) v).symm
  have hD := congrArg (fun T : E →L[ℝ] (E →L[ℝ] E) => T u)
    (fixedForm_overlap_pullback S Q D p q y hy)
  have hDA : fixedForm S Q D p y u =
      H y * (A * F y + fderiv ℝ F y u) := by
    simpa only [LocalConnectionGauge.transform_apply,
      LocalConnectionCoordinatePullback.pullback, ContinuousLinearMap.comp_apply]
      using hD
  have hAcomm (a : Fin 3 → ℝ) :
      QuaternionicLieAlgebraProjection.symplecticProjection S A *
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S a =
      VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S a *
        QuaternionicLieAlgebraProjection.symplecticProjection S A :=
    fixedForm_symplectic_commutes S Q D q (φ y) v hqy a
  have hEquiv := standardLie_fixedGauge_conjugation S Q p q lift y hy hx A hAcomm
  have hDeriv := standardLie_fixedGauge_derivative S Q p q lift y u hy hx
  have hEquiv' : standardLie S (H y * (A * F y)) =
      K y * standardLie S A * G y := by
    rw [← mul_assoc]
    exact hEquiv
  have hDeriv' : standardLie S (H y * fderiv ℝ F y u) =
      K y * fderiv ℝ G y u := hDeriv
  rw [hP, hDA, mul_add, map_add, hEquiv', hDeriv']
  change K y * standardLie S A * G y + K y * fderiv ℝ G y u =
    K y * (standardConnection S Q D q (φ y) v * G y + fderiv ℝ G y u)
  rw [hQ]
  noncomm_ring

end
end QuaternionicSymmetry.QuaternionicManifoldStandardAffineOverlap
