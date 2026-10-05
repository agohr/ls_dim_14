import QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneDerivative

/-! The inverse genuine adapted tangent gauge transports the fixed
quaternionic span in one frame back to that of the other. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneBackward

open ManifoldQuaternionicConnection ManifoldQuaternionicAdjointOverlap
open VectorBundleFrameTransitions
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem inverseGauge_mem_quaternionicSpan
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (T : E →L[ℝ] E)
    (hT : T ∈ quaternionicSpan (Q.reduction.Q (achart E q))) :
    adaptedGaugeInv Q p q y * T * adaptedGauge Q p q y ∈
      quaternionicSpan (Q.reduction.Q (achart E p)) := by
  let b := coeff (Q.reduction.Q (achart E q)) T
  let a := rankThreeGaugeInv Q p q y b
  have hb : synth (Q.reduction.Q (achart E q)) b = T :=
    synth_coeff_of_mem _ _ hT
  have hRa : rankThreeGauge Q p q y a = b := by
    change (rankThreeGauge Q p q y * rankThreeGaugeInv Q p q y) b = b
    rw [(rankThreeGauge_inverse Q p q y hy).2]
    rfl
  have heq := synth_rankThreeGauge Q p q y hy a
  rw [hRa, hb] at heq
  have hhg := (adaptedGauge_inverse Q p q y hy).1
  have hgh := (adaptedGauge_inverse Q p q y hy).2
  have hback : adaptedGaugeInv Q p q y * T * adaptedGauge Q p q y =
      synth (Q.reduction.Q (achart E p)) a := by
    rw [heq]
    simp only [mul_assoc, ← mul_assoc (adaptedGaugeInv Q p q y)
      (adaptedGauge Q p q y), hhg, one_mul, hgh, mul_one]
  rw [hback]
  exact synth_mem _ _

end
end QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneBackward
