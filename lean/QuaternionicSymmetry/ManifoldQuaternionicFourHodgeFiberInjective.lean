import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberSurjective
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitInjective

/-! The normalized tangent two-form map is injective on each local
coefficient fiber, supplying local inverse uniqueness. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberInjective

open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicUnitInjective
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

theorem localTangentTwoForm_injective
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a c : Fin 3 → ℝ)
    (h : localTangentTwoForm Q hdim i x hi a =
      localTangentTwoForm Q hdim i x hi c) : a = c := by
  have hp := congrArg
    (pullbackTwoForm (localBasis Q hdim i)
      (ManifoldQuaternionicFourTangentOrientation.localToTangentEquiv
        Q i x hi).toLinearMap) h
  rw [localTangentTwoForm_pullback,
    localTangentTwoForm_pullback] at hp
  exact normalized_operatorForm_synth_injective
    (Q.reduction.Q i) hdim (unit : E) unit_norm a c hp

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberInjective
