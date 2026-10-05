import QuaternionicSymmetry.FourDimensionalHalfSpinConjugateStandardLine
import QuaternionicSymmetry.QuaternionicManifoldStandardGaugeDerivative

/-! Exact line-block extraction from the already checked actual standard
connection/gauge action. This prepares the left-half-spin affine overlap
law by the separately proved quaternion-conjugation equivalence. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinAffineBlock

open scoped Quaternion Manifold ContDiff
open QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardLie
  QuaternionicProjectiveLineMaurer
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldStandardMaurerIdentity
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicManifoldStandardGaugeDerivative
  QuaternionicManifoldStandardGaugeEquivariance
  QuaternionicManifoldFixedConnectionOverlap
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldProductGaugeDifferential
  OperatorBlockDerivative
  QuaternionicLieAlgebraProjection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicConnection
  QuaternionicProjectiveStandardHilbertStructure

noncomputable section

private def c : StandardSpace (E := ℍ) ≃L[ℝ] ℍ × ℍ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ

theorem standardLie_line_block (A : ℍ →L[ℝ] ℍ) (w : ℍ) :
    (c (standardLie leftLineStructure A (c.symm (0, w)))).2 =
      scalarLineLie leftLineStructure A w := by
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem standardChart_line_block (p : M) (i j : atlas ℍ M)
    (lift : unitary ℍ) (y : ℍ) (w : ℍ) :
    (c ((standardChart leftLineStructure Q p i j lift y)
      (c.symm (0, w)))).2 =
      rightStar (scalarChart Q p i j lift y) w := by
  rfl

theorem standardChartInverse_line_block (p : M) (i j : atlas ℍ M)
    (lift : unitary ℍ) (y : ℍ) (w : ℍ) :
    (c ((standardChartInverse leftLineStructure Q p i j lift y)
      (c.symm (0, w)))).2 =
      rightStar (star (scalarChart Q p i j lift y)) w := by
  rfl

/-- The homogeneous term of the actual adapted gauge transformation acts
on the half-spin line by the genuine locally lifted right-line operator.
Quaternion conjugation converts this to the left projective spinor action. -/
theorem scalarLineLie_fixedGauge_conjugation (p q : M)
    (lift : unitary ℍ) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (A : ℍ →L[ℝ] ℍ)
    (hA : ∀ a, symplecticProjection leftLineStructure A *
        synth leftLineStructure a =
      synth leftLineStructure a * symplecticProjection leftLineStructure A) :
    scalarLineLie leftLineStructure
      (fixedGaugeInv leftLineStructure Q p q y * A *
        fixedGauge leftLineStructure Q p q y) =
      rightStar (star (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) *
        scalarLineLie leftLineStructure A *
          rightStar (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y) := by
  apply ContinuousLinearMap.ext
  intro w
  have h := congrArg
    (fun T : StandardSpace (E := ℍ) →L[ℝ] StandardSpace (E := ℍ) =>
      (c (T (c.symm (0, w)))).2)
    (standardLie_fixedGauge_conjugation leftLineStructure Q p q lift y hy hx A hA)
  change scalarLineLie leftLineStructure
      (fixedGaugeInv leftLineStructure Q p q y * A *
        fixedGauge leftLineStructure Q p q y) w =
      rightStar (star (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y))
        (scalarLineLie leftLineStructure A
          (rightStar (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y) w)) at h
  exact h

/-- The inhomogeneous Maurer--Cartan term of the actual adapted tangent
gauge is precisely the derivative term of its local half-spin line action. -/
theorem scalarLineLie_fixedGauge_derivative (p q : M)
    (lift : unitary ℍ) (y u : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift) :
    scalarLineLie leftLineStructure
      (fixedGaugeInv leftLineStructure Q p q y *
        fderiv ℝ (fixedGauge leftLineStructure Q p q) y u) =
      rightStar (star (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) *
        fderiv ℝ (fun z =>
          rightStar (scalarChart Q p (achart ℍ p) (achart ℍ q) lift z)) y u := by
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let k := kernelChart leftLineStructure Q p (achart ℍ p) (achart ℍ q) lift
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  have hk : DifferentiableAt ℝ k y :=
    symplecticFactor_chart_differentiableAt leftLineStructure Q p
      (achart ℍ p) (achart ℍ q) lift y hy.1 hx
  have hR : DifferentiableAt ℝ (fun z => rightStar (r z)) y :=
    differentiableAt_rightStar r y hr
  have hderiv : fderiv ℝ
      (standardChart leftLineStructure Q p (achart ℍ p) (achart ℍ q) lift)
      y u = blockOperator c (fderiv ℝ k y u)
        (fderiv ℝ (fun z => rightStar (r z)) y u) := by
    change fderiv ℝ (fun z => blockOperator c (k z) (rightStar (r z))) y u = _
    exact fderiv_blockOperator c k (fun z => rightStar (r z)) y u hk hR
  apply ContinuousLinearMap.ext
  intro w
  have h := congrArg
    (fun T : StandardSpace (E := ℍ) →L[ℝ] StandardSpace (E := ℍ) =>
      (c (T (c.symm (0, w)))).2)
    (standardLie_fixedGauge_derivative leftLineStructure Q p q lift y u hy hx)
  rw [hderiv] at h
  change scalarLineLie leftLineStructure
      (fixedGaugeInv leftLineStructure Q p q y *
        fderiv ℝ (fixedGauge leftLineStructure Q p q) y u) w =
      rightStar (star (r y))
        ((fderiv ℝ (fun z => rightStar (r z)) y u) w) at h
  exact h

/-- The independently extracted line block of the actual connection obeys
the complete affine gauge law under the smooth local quaternionic lift. -/
theorem scalarLineForm_affine_refined
    (D : CompatibleTangentConnection Q) (p q : M) (lift : unitary ℍ)
    (y u : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    scalarLineLie leftLineStructure (fixedForm leftLineStructure Q D p y u) =
      rightStar (star (r y)) *
        (scalarLineLie leftLineStructure
            (fixedForm leftLineStructure Q D q
              (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
              (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u)) *
            rightStar (r y) +
          fderiv ℝ (fun z => rightStar (r z)) y u) := by
  dsimp
  let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
  let v := fderiv ℝ φ y u
  let A := fixedForm leftLineStructure Q D q (φ y) v
  let F := fixedGauge leftLineStructure Q p q
  let H := fixedGaugeInv leftLineStructure Q p q
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  have hqy : φ y ∈ (extChartAt 𝓘(ℝ, ℍ) q).target :=
    (extChartAt 𝓘(ℝ, ℍ) q).map_source hy.2
  have hD := congrArg (fun T : ℍ →L[ℝ] (ℍ →L[ℝ] ℍ) => T u)
    (fixedForm_overlap_pullback leftLineStructure Q D p q y hy)
  have hDA : fixedForm leftLineStructure Q D p y u =
      H y * (A * F y + fderiv ℝ F y u) := by
    simpa only [LocalConnectionGauge.transform_apply,
      LocalConnectionCoordinatePullback.pullback, ContinuousLinearMap.comp_apply]
      using hD
  have hAcomm (a : Fin 3 → ℝ) :
      symplecticProjection leftLineStructure A * synth leftLineStructure a =
        synth leftLineStructure a * symplecticProjection leftLineStructure A :=
    fixedForm_symplectic_commutes leftLineStructure Q D q (φ y) v hqy a
  have hEquiv := scalarLineLie_fixedGauge_conjugation Q p q lift y hy hx A hAcomm
  have hDeriv := scalarLineLie_fixedGauge_derivative Q p q lift y u hy hx
  rw [hDA, mul_add, map_add]
  rw [mul_assoc] at hEquiv
  rw [hEquiv, hDeriv]
  noncomm_ring

end
end QuaternionicSymmetry.FourDimensionalHalfSpinAffineBlock
