import QuaternionicSymmetry.ManifoldQuaternionicIsometryLocalDerivative
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal

/-! The fixed adapted quaternionic operator and preferred tangent operator
describe the same genuine tangent endomorphism after tangent-chart transport. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalGaugeTransport

open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- A quaternionic endomorphism expressed in one fixed adapted frame. -/
def localTangentSynth (i : atlas E M) (x : M) (a : Fin 3 → ℝ) : E →L[ℝ] E :=
  (Q.frames.fromFrame i x).comp
    ((synth (Q.reduction.Q i) a).comp (Q.frames.toFrame i x))

/-- Its coefficient transition is compatible with the actual tangent
coordinate transition, not merely with an abstract SO(3) matrix. -/
theorem localTangentSynth_coordChange (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) (v : E) :
    localTangentSynth Q j x
      (Q.reduction.rankThreeCoordChange i j x a)
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x v) =
    (tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x
      (localTangentSynth Q i x a v) := by
  let C := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x
  let Ti := Q.frames.toFrame i x
  let Tj := Q.frames.toFrame j x
  let Fi := Q.frames.fromFrame i x
  let Fj := Q.frames.fromFrame j x
  have h₁ : Tj (C v) = Q.frames.coordChange i j x (Ti v) := by
    rw [Q.frames.coordChange_apply, Q.frames.from_to i x hi]
  have h₂ (w : E) : Fj (Q.frames.coordChange i j x w) = C (Fi w) := by
    rw [Q.frames.coordChange_apply, Q.frames.from_to j x hj]
  change Fj ((synth (Q.reduction.Q j)
      (Q.reduction.rankThreeCoordChange i j x a)) (Tj (C v))) =
    C (Fi ((synth (Q.reduction.Q i) a) (Ti v)))
  rw [h₁, synth_rankThreeCoordChange_eval Q i j x hi hj a]
  exact h₂ _

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalGaugeTransport
