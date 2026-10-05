import QuaternionicSymmetry.FourDimensionalExteriorCanonicalHodge
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicHalf
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge

/-! The actual Q-plane and corrected Weyl forms lie in opposite eigenspaces
of the now frame-independent pointwise exterior Hodge operator. Atlas-overlap
transport and comparison with the source's spinor orientation remain distinct. -/

namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourCanonicalHodge

open FourDimensionalExteriorHodge
open FourDimensionalExteriorCanonicalHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalQuaternionicHodgeFrame
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge
open scoped Manifold ContDiff
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem quaternionicForm_canonicalStar_positive
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (v : V) (hv : ‖v‖ = 1) (α : TwoForm V)
    (hα : α ∈ (quaternionicSpan Q).map
      (operatorForm (frameBasis Q hdim v hv).toBasis)) :
    canonicalStar Q hdim α = α := by
  rw [canonicalStar_eq_frameStar Q hdim v hv]
  apply (mem_positiveExteriorHalf (frameBasis Q hdim v hv) α).mp
  rw [positiveExteriorHalf_eq_quaternionicFormImage Q hdim v hv]
  exact hα

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem correctedWeyl_canonicalStar_negative
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v z : E) (hz : ‖z‖ = 1) :
    let Q := P.tangent.reduction.Q (achart E p)
    let A := (correctedWeylOperator P p y hy u v).toLinearMap
    let b := frameBasis Q P.realDimension z hz
    canonicalStar Q P.realDimension
      (HyperholomorphicExterior.form b.toBasis A) =
      -HyperholomorphicExterior.form b.toBasis A := by
  dsimp only
  rw [canonicalStar_eq_frameStar _ _ z hz]
  exact correctedWeyl_negative_exteriorHodge P p y hy u v z hz

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourCanonicalHodge
