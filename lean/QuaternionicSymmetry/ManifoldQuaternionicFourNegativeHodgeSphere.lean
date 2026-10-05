import QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeGlobalMap
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSurjective

/-! The actual pointwise negative-Hodge unit sphere in the tangent exterior
fiber, using the core-preferred orthonormal quaternionic frame to measure
the six-coordinate Euclidean norm. Its independence under overlaps is
certified by the gluing theorem for the quaternionic sphere image. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNegativeHodgeSphere

open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicUnitSphere
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourTwistorHodgeGlobalMap
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

def negativeTangentUnitHalf (x : M) :
    Set (TwoForm (TangentSpace 𝓘(ℝ,E) x)) :=
  let k := Q.frames.adaptedCore.indexAt x
  let hk := Q.frames.adaptedCore.mem_baseSet_at x
  {α | (-(tangentHodgeStar Q hdim x)) α = -α ∧
    coordinateSquare (coordinates (localBasis Q hdim k)
      (pullbackTwoForm (localBasis Q hdim k)
        (localToTangentEquiv Q k x hk).toLinearMap α)) = 1}

theorem twistorTangentTwoForm_mem_negativeTangentUnitHalf
    (z : TwistorSphere Q) :
    twistorTangentTwoForm Q hdim z ∈
      negativeTangentUnitHalf Q hdim (projection Q z) := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  refine ⟨twistorTangentTwoForm_reversedStar Q hdim z, ?_⟩
  change coordinateSquare (coordinates (localBasis Q hdim k)
      (pullbackTwoForm (localBasis Q hdim k)
        (localToTangentEquiv Q k x hk).toLinearMap
          (twistorTangentTwoForm Q hdim z))) = 1
  rw [twistorTangentTwoForm_local Q hdim z k hk,
    localTangentTwoForm_pullback]
  have ha : coefficientSquare (localCoordinate Q k z hk).1 = 1 :=
    (localCoordinate Q k z hk).2
  exact normalized_coordinateSquare_synth
    (Q.reduction.Q k) hdim (unit : E) unit_norm _ ha

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNegativeHodgeSphere
