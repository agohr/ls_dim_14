import QuaternionicSymmetry.ManifoldQuaternionicJointSphereBundleBridge

/-! Joint continuity in the isometry, base point, and sphere coefficient of
the two-fixed-frame derivative rotation. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointMovingCoefficientContinuity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointMovingAdaptedDerivative
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldRiemannianIsometryLieInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuousAt_movingCoefficientRotation_joint
    (hR3 : IsometryLieSource.{0,0})
    (f₀ : QuaternionicIsometries Q) (x₀ : M) (a₀ : Fin 3 → ℝ) :
    ContinuousAt (fun p : (QuaternionicIsometries Q × M) × (Fin 3 → ℝ) =>
      movingCoefficientRotation Q f₀ x₀ p.2 p.1) ((f₀,x₀),a₀) := by
  have hforward : ContinuousAt
      (fun p : (QuaternionicIsometries Q × M) × (Fin 3 → ℝ) =>
        movingAdaptedDerivative Q f₀ x₀ p.1) ((f₀,x₀),a₀) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((f₀,x₀),a₀))
      (continuousAt_movingAdaptedDerivative Q hR3 f₀ x₀) continuousAt_fst
  have hbackward : ContinuousAt
      (fun p : (QuaternionicIsometries Q × M) × (Fin 3 → ℝ) =>
        movingAdaptedInverseDerivative Q f₀ x₀ p.1) ((f₀,x₀),a₀) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((f₀,x₀),a₀))
      (continuousAt_movingAdaptedInverseDerivative Q hR3 f₀ x₀) continuousAt_fst
  have hsynth : ContinuousAt
      (fun p : (QuaternionicIsometries Q × M) × (Fin 3 → ℝ) =>
        synth (Q.reduction.Q (achart E x₀)) p.2) ((f₀,x₀),a₀) :=
    (synth (Q.reduction.Q (achart E x₀))).continuous.continuousAt.comp
      continuousAt_snd
  have hconj : ContinuousAt
      (fun p : (QuaternionicIsometries Q × M) × (Fin 3 → ℝ) =>
        (movingAdaptedDerivative Q f₀ x₀ p.1).comp
          ((synth (Q.reduction.Q (achart E x₀)) p.2).comp
            (movingAdaptedInverseDerivative Q f₀ x₀ p.1)))
      ((f₀,x₀),a₀) := hforward.clm_comp (hsynth.clm_comp hbackward)
  exact (coeff (Q.reduction.Q (achart E (f₀ • x₀)))).continuous.continuousAt.comp
    (f := fun p : (QuaternionicIsometries Q × M) × (Fin 3 → ℝ) =>
      (movingAdaptedDerivative Q f₀ x₀ p.1).comp
        ((synth (Q.reduction.Q (achart E x₀)) p.2).comp
          (movingAdaptedInverseDerivative Q f₀ x₀ p.1)))
    (x := ((f₀,x₀),a₀)) hconj

end
end QuaternionicSymmetry.ManifoldQuaternionicJointMovingCoefficientContinuity
