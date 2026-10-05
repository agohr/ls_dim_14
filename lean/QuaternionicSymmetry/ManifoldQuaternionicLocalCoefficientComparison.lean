import QuaternionicSymmetry.ManifoldQuaternionicIsometryLocalDerivative
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients

/-! Comparison of the smooth fixed-chart coefficient formula with the
intrinsic derivative-conjugation action. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalCoefficientComparison

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryLocalDerivative
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- At the center of fixed adapted charts, the smooth matrix conjugation
really is the derivative-conjugation action on the quaternionic three-plane. -/
theorem localDerivative_conjugates_synth_center
    (f : QuaternionicIsometries Q) (p : M) (a : Fin 3 → ℝ) :
    (localAdaptedDerivative Q f p p).comp
      ((synth (Q.reduction.Q (achart E p)) a).comp
        (localAdaptedInverseDerivative Q f p p)) =
      synth (Q.reduction.Q (achart E (f • p)))
        (coefficientAction Q f p a) := by
  let i := achart E p
  let j := achart E (f • p)
  let F := Q.frames.fromFrame j (f • p)
  let T := Q.frames.toFrame j (f • p)
  let U := localAdaptedDerivative Q f p p
  let V := localAdaptedInverseDerivative Q f p p
  have hj := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • p)
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p
  ext w
  let v := tangentEquiv Q f⁻¹ (f • p) (F w)
  have hv : tangentEquiv Q f p v = F w :=
    tangentEquiv_inverse_after_forward Q f p (F w)
  have hV : V w = Q.frames.toFrame i p v :=
    localAdaptedInverseDerivative_center_apply Q f p w
  have hU (q : E) : U q = T (tangentEquiv Q f p
      (Q.frames.fromFrame i p q)) :=
    localAdaptedDerivative_center_apply Q f p q
  have htarget := congrArg (fun A : TangentSpace 𝓘(ℝ,E) (f • p) →L[ℝ]
      TangentSpace 𝓘(ℝ,E) (f • p) => T (A (F w)))
    (tangentSynth_coefficientAction Q f p a)
  change T (F ((synth (Q.reduction.Q j) (coefficientAction Q f p a))
      (T (F w)))) =
    T (tangentConjugation Q f p (tangentSynth Q p a) (F w)) at htarget
  rw [Q.frames.to_from j (f • p) hj] at htarget
  rw [Q.frames.to_from j (f • p) hj] at htarget
  rw [← hv, tangentConjugation_apply_tangentEquiv] at htarget
  change (synth (Q.reduction.Q j) (coefficientAction Q f p a)) w =
    T (tangentEquiv Q f p (tangentSynth Q p a v)) at htarget
  calc
    U ((synth (Q.reduction.Q i) a) (V w)) =
      T (tangentEquiv Q f p
        (Q.frames.fromFrame i p
          ((synth (Q.reduction.Q i) a)
            (Q.frames.toFrame i p v)))) := by rw [hV, hU]
    _ = T (tangentEquiv Q f p (tangentSynth Q p a v)) := by
      rfl
    _ = (synth (Q.reduction.Q j) (coefficientAction Q f p a)) w :=
      htarget.symm

/-- Thus coefficient extraction at the chart center agrees with the actual
derivative-induced three-dimensional rotation. -/
theorem localCoefficientRotation_center
    (f : QuaternionicIsometries Q) (p : M) (a : Fin 3 → ℝ) :
    localCoefficientRotation Q f p p a = coefficientAction Q f p a := by
  change coeff (Q.reduction.Q (achart E (f • p)))
    ((localAdaptedDerivative Q f p p).comp
      ((synth (Q.reduction.Q (achart E p)) a).comp
        (localAdaptedInverseDerivative Q f p p))) = _
  rw [localDerivative_conjugates_synth_center]
  exact coeff_synth _ _

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalCoefficientComparison
