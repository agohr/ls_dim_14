import QuaternionicSymmetry.FourDimensionalExteriorPullbackContinuous
import QuaternionicSymmetry.FourDimensionalExteriorUnitSphereHomeomorphism
import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberEquiv

/-! The actual tangent negative-Hodge sphere receives the subspace topology
from basis-independent exterior two-forms. Its local coefficient map is
continuous by the finite-dimensional operator-form and exterior-pullback
continuity theorems, not by declaration. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberTopology

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorTwoFormCanonicalTopology
open FourDimensionalExteriorPullbackContinuous
open FourDimensionalExteriorUnitMapContinuous
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourNegativeHodgeSphere
open ManifoldQuaternionicFourHodgeFiberEquiv
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

def negativeTangentUnitHalfTopology (x : M) :
    TopologicalSpace {α : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
      α ∈ negativeTangentUnitHalf Q hdim x} := by
  change TopologicalSpace {α : TwoForm E //
    α ∈ negativeTangentUnitHalf Q hdim x}
  exact TopologicalSpace.induced Subtype.val (canonicalTwoFormTopology hdim)

theorem localHodgeSphereMap_continuous
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    @Continuous coefficientSphere
      {α : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
        α ∈ negativeTangentUnitHalf Q hdim x}
      inferInstance (negativeTangentUnitHalfTopology Q hdim x)
      (localHodgeSphereMap Q hdim i x hi) := by
  letI : TopologicalSpace (TwoForm E) := canonicalTwoFormTopology hdim
  letI : TopologicalSpace
      {α : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
        α ∈ negativeTangentUnitHalf Q hdim x} :=
    negativeTangentUnitHalfTopology Q hdim x
  let b := localBasis Q hdim i
  let T : E →ₗ[ℝ] E :=
    (localToTangentEquiv Q i x hi).symm.toLinearMap
  apply continuous_induced_rng.mpr
  change @Continuous coefficientSphere (TwoForm E) inferInstance
    (canonicalTwoFormTopology hdim)
    (fun a => pullbackTwoFormLinear b T
      (normalizedSynthFormLinear (Q.reduction.Q i) b a.1))
  exact (pullbackTwoFormLinear_continuous hdim b T).comp
    ((normalizedSynthForm_continuous (Q.reduction.Q i) hdim b).comp
      continuous_subtype_val)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberTopology
