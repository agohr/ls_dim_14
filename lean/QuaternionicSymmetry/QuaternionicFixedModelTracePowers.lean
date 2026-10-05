import QuaternionicSymmetry.QuaternionicRankThreeTracePowers
import QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace

/-! All positive even power traces respect the fixed quaternionic model
change used by the actual projective-standard connection. -/
namespace QuaternionicSymmetry.QuaternionicFixedModelTracePowers
open QuaternionicFixedModelAdjointTrace QuaternionicManifoldFixedNormalizer
  QuaternionicManifoldModelProjection
  QuaternionicIsometryNormalizer QuaternionicLieAlgebraProjection
  ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  QuaternionicRankThreeTracePowers LocalEndomorphismTrace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S T : QuaternionicStructure E)

omit [Nontrivial E] in
private theorem fixedConjugation_pow (A : E →L[ℝ] E) (j : ℕ) :
    (conjugation (modelGauge S T).symm A) ^ j =
      conjugation (modelGauge S T).symm (A ^ j) := by
  induction j with
  | zero =>
      apply ContinuousLinearMap.ext
      intro v
      simp [conjugation]
  | succ j ih =>
      rw [pow_succ, ih, pow_succ, conjugation_product]

omit [Nontrivial E] in
theorem fixedConjugation_trace_pow (A : E →L[ℝ] E) (j : ℕ) :
    traceCLM ((conjugation (modelGauge S T).symm A) ^ j) =
      traceCLM (A ^ j) := by
  rw [fixedConjugation_pow, traceCLM_fixedConjugation]

theorem standardLie_fixed_even_trace (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection T A * synth T a =
      synth T a * symplecticProjection T A)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j *
      traceCLM ((QuaternionicProjectiveStandardLie.standardLie S
        (conjugation (modelGauge S T).symm A)) ^ (2 * j)) =
      (4 : ℝ) ^ j * traceCLM ((symplecticProjection T A) ^ (2 * j)) +
      2 * traceCLM ((adjointRepresentation T A) ^ (2 * j)) := by
  rw [standard_even_trace_rankThree S _ j hj]
  rw [symplecticProjection_modelGauge S T A hA,
    fixedConjugation_trace_pow S T,
    adjointRepresentation_scalarProjection_fixed S T A hA]

end
end QuaternionicSymmetry.QuaternionicFixedModelTracePowers
