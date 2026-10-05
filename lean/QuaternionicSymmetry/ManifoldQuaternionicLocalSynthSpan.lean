import QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance

/-! Relate the coefficient-synthesized local endomorphisms to the genuine
chartwise quaternionic three-plane and its three displayed generators. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSpan

open ManifoldQuaternionicReduction
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicSpanSymmetry
open VectorBundleFrameTransitions
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] in
theorem localTangentSynth_mem_chartSpan (i : atlas E M) (x : M)
    (a : Fin 3 → ℝ) :
    localTangentSynth Q i x a ∈ Q.chartSpan i x := by
  rw [Q.chartSpan_eq_map]
  refine ⟨synth (Q.reduction.Q i) a, synth_mem _ _, ?_⟩
  ext v
  rfl

theorem localTangentSynth_generator (i : atlas E M) (x : M)
    (t : Fin 3) :
    localTangentSynth Q i x
        (coeff (Q.reduction.Q i)
          (quaternionicGenerator (Q.reduction.Q i) t)) =
      Q.chartGenerator i t x := by
  ext v
  change Q.frames.fromFrame i x
      ((synth (Q.reduction.Q i)
        (coeff (Q.reduction.Q i)
          (quaternionicGenerator (Q.reduction.Q i) t)))
        (Q.frames.toFrame i x v)) =
      Q.frames.fromFrame i x
        ((quaternionicGenerator (Q.reduction.Q i) t)
          (Q.frames.toFrame i x v))
  rw [synth_coeff_of_mem _ _ (generator_mem_span _ _)]

/-- In fixed charts, the genuine derivative sends a displayed quaternionic
generator to a coefficient-synthesized member of the target plane. -/
theorem localRawDerivative_chartGenerator_intertwines
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (t : Fin 3) :
    (localRawDerivative Q f p x).comp
        (Q.chartGenerator (achart E p) t x) =
      (localTangentSynth Q (achart E (f • p)) (f • x)
        (localTrueCoefficientAction Q f p x
          (coeff (Q.reduction.Q (achart E p))
            (quaternionicGenerator (Q.reduction.Q (achart E p)) t)))).comp
        (localRawDerivative Q f p x) := by
  let b := coeff (Q.reduction.Q (achart E p))
    (quaternionicGenerator (Q.reduction.Q (achart E p)) t)
  ext v
  change localRawDerivative Q f p x
      (Q.chartGenerator (achart E p) t x v) =
    localTangentSynth Q (achart E (f • p)) (f • x)
      (localTrueCoefficientAction Q f p x b)
      (localRawDerivative Q f p x v)
  rw [← localTangentSynth_generator Q (achart E p) x t]
  exact localRawDerivative_intertwines Q f p x hx hy b v

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSpan
