import QuaternionicSymmetry.ManifoldQuaternionicFixedLocalRepresentations
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput

/-! Continuity of the actual rank-three coefficient at a common fixed point.
The result is extracted from the BG-R3 joint smooth isometry evaluation and
the local adapted-frame continuity already proved for fixed components. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedPointCoefficientContinuous
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFixedLocalRepresentations
open ManifoldQuaternionicFixedLocalCoefficientContinuous
open ManifoldQuaternionicFixedCoefficientRepresentation
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldRiemannianFixedComponentInput
open ManifoldRiemannianIsometryLieInput
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuous_coefficientAction_fixed
    (hR3 : IsometryLieSource.{0,0})
    (S : Subgroup (QuaternionicIsometries Q)) (x : M)
    (hx : x ∈ fixedPoints Q S) (a : Fin 3 → ℝ) :
    Continuous (fun f : S => coefficientAction Q f.1 x a) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let y : FixedComponent Q S x := ⟨x, mem_connectedComponentIn hx⟩
  let y₀ : fixedChartDomain Q S x x := ⟨y, mem_chart_source E x⟩
  have hpoint (f : S) :
      localCLMRepresentation Q S x x y₀ f a = coefficientAction Q f.1 x a := by
    rw [localCLMRepresentation_apply]
    change Q.reduction.rankThreeCoordChange (achart E x) (achart E x) x
      (coefficientAction Q f.1 x
        (Q.reduction.rankThreeCoordChange (achart E x) (achart E x) x a)) = _
    rw [Q.reduction.rankThreeCoordChange_self (achart E x) x
      (Q.frames.adaptedCore.mem_baseSet_at x)]
    rw [Q.reduction.rankThreeCoordChange_self (achart E x) x
      (Q.frames.adaptedCore.mem_baseSet_at x)]
  apply continuous_iff_continuousAt.mpr
  intro f₀
  have h := continuousAt_localCLMRepresentation Q hChart hManifold
    hAction S x x hx f₀ y₀
  have hcomp : ContinuousAt
      (fun f : S => localCLMRepresentation Q S x x y₀ f) f₀ := by
    exact h.comp₂ continuousAt_id continuousAt_const
  have hval : ContinuousAt
      (fun f : S => localCLMRepresentation Q S x x y₀ f a) f₀ :=
    ((ContinuousLinearMap.apply ℝ (Fin 3 → ℝ) a).continuous.continuousAt).comp
      hcomp
  simpa only [hpoint] using hval

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedPointCoefficientContinuous
