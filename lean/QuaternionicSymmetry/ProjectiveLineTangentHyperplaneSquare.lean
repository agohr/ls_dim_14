import QuaternionicSymmetry.ProjectiveLineTangentTransitions
import QuaternionicSymmetry.HolomorphicLineConstantFrameChange
import QuaternionicSymmetry.HolomorphicLineGaugeRefinement

/-! The genuine CP¹ tangent determinant line is holomorphically isomorphic
to the square of the standard hyperplane line. The minus sign in the
derivative of the inverted affine coordinate is removed by an explicit
constant frame change, not dropped from the transition computation. -/

namespace QuaternionicSymmetry.ProjectiveLineTangentHyperplaneSquare

open scoped Manifold ContDiff
open ComplexProjectiveTopology FourDimensionalHalfSpinProjective
open ProjectiveLineTangentDeterminant ProjectiveLineHyperplaneCore
open ProjectiveLineTangentTransitions HolomorphicDeterminantLine
open HolomorphicLinePowers HolomorphicLineGauge HolomorphicLineConstantFrameChange
noncomputable section

def chartSign (i : Fin 2) : ℂˣ := (-1)^i.val

def signedSquareCore := changedCore (powerCore hyperplaneCore 2) chartSign

instance signedSquareCore_holomorphic : signedSquareCore.IsContMDiff 𝓘(ℂ,Model) ∞ :=
  inferInstanceAs ((changedCore (powerCore hyperplaneCore 2) chartSign).IsContMDiff 𝓘(ℂ,Model) ∞)

theorem tangentLine_transition_scalar (i j : Fin 2) (p : ProjectiveSpinor) :
    transitionScalar tangentLineCore.core (chartIndex i) (chartIndex j) p =
      transitionDet tangentCore (chartIndex i) (chartIndex j) p := by
  change transitionDet tangentCore (chartIndex i) (chartIndex j) p * 1 = _
  exact mul_one _

theorem square_transition_scalar (i j : Fin 2) (p : ProjectiveSpinor) :
    transitionScalar (powerCore hyperplaneCore 2) i j p =
      (hyperplaneTransition i j p)^2 := by
  change (hyperplaneTransition i j p * 1)^2 * 1 = _
  simp only [mul_one]

theorem signedSquare_transition_tangent (i j : Fin 2) (p : ProjectiveSpinor)
    (hp : p ∈ signedSquareCore.baseSet i ∩ signedSquareCore.baseSet j) :
    transitionScalar signedSquareCore i j p =
      transitionScalar tangentLineCore.core (chartIndex i) (chartIndex j) p := by
  have hi : p ∈ affineDomain 1 i := hp.1
  have hj : p ∈ affineDomain 1 j := hp.2
  by_cases hij : i = j
  · subst j
    have ht : p ∈ tangentLineCore.core.baseSet (chartIndex i) := by
      change p ∈ (projectiveChart 1 i).source
      simpa only [projectiveChart_source] using hi
    exact (signedSquareCore.coordChange_self i p hp.1 1).trans
      (tangentLineCore.core.coordChange_self (chartIndex i) p ht 1).symm
  · rw [tangentLine_transition_scalar,
      tangent_determinant_transition_distinct i j hij p hi hj]
    change transitionScalar (changedCore (powerCore hyperplaneCore 2) chartSign) i j p = _
    rw [transition_changedCore, square_transition_scalar]
    fin_cases i <;> fin_cases j <;> simp_all [chartSign]

def tangentToSignedSquareGauge :
    letI := tangentLineCore.holomorphic
    GaugeIso (IB := 𝓘(ℂ,Model)) tangentLineCore.core signedSquareCore := by
  letI := tangentLineCore.holomorphic
  exact HolomorphicLineGaugeRefinement.refinementGauge
    tangentLineCore.core signedSquareCore chartIndex
    (by
      intro i p hp
      change p ∈ (projectiveChart 1 i).source
      simpa only [projectiveChart_source] using hp)
    signedSquare_transition_tangent

/-- The actual holomorphic tangent/O(2) comparison on all intersections
of the tangent atlas and the standard two-chart projective cover. -/
def tangentHyperplaneSquareGauge :
    letI := tangentLineCore.holomorphic
    GaugeIso (IB := 𝓘(ℂ,Model)) tangentLineCore.core (powerCore hyperplaneCore 2) := by
  letI := tangentLineCore.holomorphic
  exact tangentToSignedSquareGauge.trans
    (frameChangeGauge (powerCore hyperplaneCore 2) chartSign).symm

end
end QuaternionicSymmetry.ProjectiveLineTangentHyperplaneSquare
