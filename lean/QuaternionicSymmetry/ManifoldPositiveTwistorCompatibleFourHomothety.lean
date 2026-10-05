import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGeometry
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety

/-! Constant positive homothety of the genuine four-dimensional Einstein
geometry with the Weyl-commutation condition compatible with the existing
twistor sphere. No n ≥ 2 scalar-constancy theorem is used here. -/

namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourHomothety

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyCurvature
open ManifoldQuaternionicHomothetyScalar
open ManifoldQuaternionicScalarCurvature
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The corrected Weyl endomorphism in adapted coordinates has weight
minus two under constant frame rescaling. -/
theorem correctedWeylVector_rescale
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (s : ℝ) (hs : 0 < s)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w : E) :
    correctedWeylVector (rescalePositive P s hs) p y hy u v w =
      s⁻¹ ^ 2 • correctedWeylVector P p y hy u v w := by
  simp only [correctedWeylVector, rescalePositive,
    adaptedCurvature_rescale, localScalarCurvature_rescale]
  simp [smul_sub, smul_smul, mul_div_assoc, mul_assoc]

/-- Positive metric homothety preserves the actual four-dimensional
Einstein equation and the Weyl-commutation condition on the Q half. -/
def rescaleFour
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (s : ℝ) (hs : 0 < s) :
    PositiveTwistorCompatibleFourGeometry (E := E) (M := M) where
  toPositiveQuaternionicKahlerGeometry :=
    rescalePositive P.toPositiveQuaternionicKahlerGeometry s hs
  realDimension := P.realDimension
  einstein := by
    intro p y hy v w
    change localRicci
      (rescaleMetric P.tangent s (ne_of_gt hs))
      (rescaleConnection P.tangent P.connection s (ne_of_gt hs))
      p y hy v w =
      (localScalarCurvature
        (rescaleMetric P.tangent s (ne_of_gt hs))
        (rescaleConnection P.tangent P.connection s (ne_of_gt hs))
        p y hy / 4) * inner ℝ v w
    rw [localRicci_rescale, localScalarCurvature_rescale, P.einstein p y hy v w]
    ring
  oppositeWeyl := by
    intro p y hy u v a w
    change correctedWeylVector
      (rescalePositive P.toPositiveQuaternionicKahlerGeometry s hs)
      p y hy u v
      (synth (P.tangent.reduction.Q (achart E p)) a w) =
      synth (P.tangent.reduction.Q (achart E p)) a
        (correctedWeylVector
          (rescalePositive P.toPositiveQuaternionicKahlerGeometry s hs)
          p y hy u v w)
    rw [correctedWeylVector_rescale,
      correctedWeylVector_rescale,
      P.oppositeWeyl p y hy u v a w]
    exact ((synth (P.tangent.reduction.Q (achart E p)) a).map_smul
      (s⁻¹ ^ 2) (correctedWeylVector P.toPositiveQuaternionicKahlerGeometry
        p y hy u v w)).symm

/-- Compactness and connectedness of the actual underlying manifold are
unchanged by constant metric homothety. -/
def rescaleCompactFour
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry
      (E := E) (M := M))
    (s : ℝ) (hs : 0 < s) :
    CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M) where
  toPositiveTwistorCompatibleFourGeometry :=
    rescaleFour P.toPositiveTwistorCompatibleFourGeometry s hs
  compact := P.compact
  connected := P.connected

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourHomothety
