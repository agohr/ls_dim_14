import QuaternionicSymmetry.QuaternionicManifoldLocalStandardMaurer
import QuaternionicSymmetry.OperatorBlockDerivative

/-! The actual local standard operator carries the fixed-model tangent
Maurer--Cartan derivative to its own operator derivative. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardMaurerIdentity

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldProductGaugeDifferential
open QuaternionicManifoldLocalStandardMaurer
open QuaternionicProjectiveProductMaurer
open QuaternionicProjectiveLineMaurer
open QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardL2
open OperatorBlockDerivative
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

private def c : StandardSpace (E := E) ≃L[ℝ] E × ℍ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ

def standardChart (p : M) (i j : atlas E M) (q : unitary ℍ)
    (y : E) : StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) :=
  QuaternionicManifoldStandardLocalOperator.localStandardOperator S Q i j q
    ((extChartAt 𝓘(ℝ, E) p).symm y)

theorem standardChart_eq_block (p : M) (i j : atlas E M)
    (q : unitary ℍ) (y : E) :
    standardChart S Q p i j q y =
      blockOperator (c (E := E)) (kernelChart S Q p i j q y)
        (rightStar (scalarChart Q p i j q y)) := by
  rfl

def standardChartInverse (p : M) (i j : atlas E M) (q : unitary ℍ)
    (y : E) : StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) :=
  blockOperator (c (E := E))
    (kernelChart S Q p i j q y).adjoint
    (rightStar (star (scalarChart Q p i j q y)))

set_option maxHeartbeats 800000 in
theorem standard_maurer_identity (p : M) (i j : atlas E M)
    (q : unitary ℍ) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈ liftNeighborhood Q i j q) :
    let r := scalarChart Q p i j q
    let h := kernelChart S Q p i j q
    standardLie S
      (((h y).adjoint * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
        (star (r y))) * fderiv ℝ (productGauge S r h) y u) =
      standardChartInverse S Q p i j q y *
        fderiv ℝ (standardChart S Q p i j q) y u := by
  dsimp
  let r := scalarChart Q p i j q
  let h := kernelChart S Q p i j q
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p i j q y hy hx
  have hh : DifferentiableAt ℝ h y :=
    symplecticFactor_chart_differentiableAt S Q p i j q y hy hx
  have hR : DifferentiableAt ℝ (fun z => rightStar (r z)) y :=
    differentiableAt_rightStar r y hr
  have hD : fderiv ℝ (standardChart S Q p i j q) y u =
      blockOperator (c (E := E)) (fderiv ℝ h y u)
        (fderiv ℝ (fun z => rightStar (r z)) y u) := by
    change fderiv ℝ (fun z => blockOperator (c (E := E))
      (h z) (rightStar (r z))) y u = _
    exact fderiv_blockOperator (c (E := E)) h (fun z => rightStar (r z))
      y u hh hR
  rw [hD]
  apply ContinuousLinearMap.ext
  intro z
  apply (c (E := E)).injective
  have hb := local_standard_maurer_blocks S Q p i j q y u hy hx
  change
    (QuaternionicLieAlgebraProjection.symplecticProjection S
        (((h y).adjoint * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
          (star (r y))) * fderiv ℝ (productGauge S r h) y u) z.fst,
      scalarLineLie S
        (((h y).adjoint * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
          (star (r y))) * fderiv ℝ (productGauge S r h) y u) z.snd) =
    (((h y).adjoint * fderiv ℝ h y u) z.fst,
      (rightStar (star (r y)) *
        fderiv ℝ (fun z => rightStar (r z)) y u) z.snd)
  apply Prod.ext
  · change QuaternionicLieAlgebraProjection.symplecticProjection S
        (((h y).adjoint * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
          (star (r y))) * fderiv ℝ (productGauge S r h) y u) z.fst =
        ((h y).adjoint * fderiv ℝ h y u) z.fst
    exact congrArg (fun A : E →L[ℝ] E => A z.fst) hb.1
  · change scalarLineLie S
        (((h y).adjoint * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
          (star (r y))) * fderiv ℝ (productGauge S r h) y u) z.snd =
        (rightStar (star (r y)) *
          fderiv ℝ (fun z => rightStar (r z)) y u) z.snd
    exact congrArg (fun A : ℍ →L[ℝ] ℍ => A z.snd) hb.2

end
end QuaternionicSymmetry.QuaternionicManifoldStandardMaurerIdentity
