import QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeGluing
import QuaternionicSymmetry.ManifoldTwistorSphereBundle

/-! A canonical pointwise exterior two-form on the actual tangent fiber of
each point of the original quaternionic twistor sphere bundle. The preferred
chart merely implements the definition; the local formula below proves
independence from that choice. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeGlobalMap

open FourDimensionalExteriorHodge
open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourTwistorHodgeGluing
open ManifoldQuaternionicFourTwistorHodgeEigen
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

def twistorTangentTwoForm (z : TwistorSphere Q) :
    TwoForm (TangentSpace 𝓘(ℝ,E) (projection Q z)) := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  exact localTangentTwoForm Q hdim k x hk (localCoordinate Q k z hk).1

theorem twistorTangentTwoForm_local (z : TwistorSphere Q)
    (i : atlas E M)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    twistorTangentTwoForm Q hdim z =
      localTangentTwoForm Q hdim i (projection Q z) hi
        (localCoordinate Q i z hi).1 := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  have hc := congrArg Subtype.val
    (localTrivialization_transition Q i k z hi hk)
  change (localCoordinate Q k z hk).1 =
    Q.reduction.rankThreeCoordChange i k x (localCoordinate Q i z hi).1 at hc
  change localTangentTwoForm Q hdim k x hk (localCoordinate Q k z hk).1 = _
  rw [hc]
  exact localTangentTwoForm_overlap Q hdim i k x hi hk _

theorem twistorTangentTwoForm_reversedStar (z : TwistorSphere Q) :
    (-(ManifoldQuaternionicFourGlobalHodge.tangentHodgeStar Q hdim
      (projection Q z))) (twistorTangentTwoForm Q hdim z) =
    -twistorTangentTwoForm Q hdim z := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  change (-(ManifoldQuaternionicFourGlobalHodge.tangentHodgeStar Q hdim x))
    (localTangentTwoForm Q hdim k x hk (localCoordinate Q k z hk).1) = _
  exact localTangentTwoForm_reversedStar Q hdim k x hk _

end
end QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeGlobalMap
