import QuaternionicSymmetry.ManifoldQuaternionicChartProjection

/-! The actual isometry derivative carries every chartwise Q-plane
endomorphism, not only the three displayed generators, into the target
chartwise Q-plane. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalSpanDerivative

open ManifoldQuaternionicReduction
open ManifoldQuaternionicLocalSynthSpan
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicChartProjection
open ManifoldQuaternionicSpanSymmetry
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem localRawDerivative_chartSpan_intertwines
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (T : E →L[ℝ] E)
    (hT : T ∈ Q.chartSpan (achart E p) x) :
    ∃ U : E →L[ℝ] E,
      U ∈ Q.chartSpan (achart E (f • p)) (f • x) ∧
        (localRawDerivative Q f p x).comp T =
          U.comp (localRawDerivative Q f p x) := by
  let i := achart E p
  let a := coeff (Q.reduction.Q i)
    (inverseChartConjugation Q i x T)
  let U := localTangentSynth Q (achart E (f • p)) (f • x)
    (localTrueCoefficientAction Q f p x a)
  have hbase : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i := hx
  have hTexpr : localTangentSynth Q i x a = T := by
    change chartProjection Q i x T = T
    exact chartProjection_fixed Q i x hbase T hT
  refine ⟨U, localTangentSynth_mem_chartSpan Q _ _ _, ?_⟩
  ext v
  change localRawDerivative Q f p x (T v) =
    U (localRawDerivative Q f p x v)
  rw [← hTexpr]
  exact localRawDerivative_intertwines Q f p x hx hy a v

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalSpanDerivative
