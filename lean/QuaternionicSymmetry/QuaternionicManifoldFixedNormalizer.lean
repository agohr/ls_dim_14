import QuaternionicSymmetry.QuaternionicStructureIsometryTransport
import QuaternionicSymmetry.ManifoldQuaternionicUnitaryNormalizer

/-! Conjugate actual adapted tangent transitions into the normalizer of one
fixed quaternionic model. -/

namespace QuaternionicSymmetry.QuaternionicManifoldFixedNormalizer

open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal ManifoldQuaternionicUnitaryNormalizer
  QuaternionicIsometryNormalizer QuaternionicStructureIsometryTransport
open scoped ContDiff Manifold

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)

/-- A constant isometric quaternionic identification between a chosen model
and another chart's quaternionic structure. -/
def modelGauge (T : QuaternionicStructure E) : E ≃ₗᵢ[ℝ] E :=
  Classical.choose (exists_intertwiningIsometry S T)

omit [Nontrivial E] in
theorem modelGauge_I (T : QuaternionicStructure E) (v : E) :
    modelGauge S T (S.I v) = T.I (modelGauge S T v) :=
  (Classical.choose_spec (exists_intertwiningIsometry S T)).1 v

omit [Nontrivial E] in
theorem modelGauge_J (T : QuaternionicStructure E) (v : E) :
    modelGauge S T (S.J v) = T.J (modelGauge S T v) :=
  (Classical.choose_spec (exists_intertwiningIsometry S T)).2 v

omit [Nontrivial E] in
theorem modelGauge_K (T : QuaternionicStructure E) (v : E) :
    modelGauge S T (S.K v) = T.K (modelGauge S T v) := by
  change modelGauge S T (S.I (S.J v)) = T.I (T.J (modelGauge S T v))
  rw [modelGauge_I, modelGauge_J]

theorem modelGauge_conjugation_synth (T : QuaternionicStructure E)
    (a : Fin 3 → ℝ) :
    conjugation (modelGauge S T) (synth S a) = synth T a := by
  rw [synth_apply, synth_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul]
  congr 1
  ext v
  let w := (modelGauge S T).symm v
  have hw : modelGauge S T w = v :=
    (modelGauge S T).apply_symm_apply v
  change modelGauge S T (quaternionicGenerator S t w) =
    quaternionicGenerator T t v
  fin_cases t
  · change modelGauge S T (S.I w) = T.I v
    rw [modelGauge_I, hw]
  · change modelGauge S T (S.J w) = T.J v
    rw [modelGauge_J, hw]
  · change modelGauge S T (S.K w) = T.K v
    rw [modelGauge_K, hw]

theorem modelGauge_maps_span (T : QuaternionicStructure E)
    (A : E →L[ℝ] E) (hA : A ∈ quaternionicSpan S) :
    conjugation (modelGauge S T) A ∈ quaternionicSpan T := by
  rw [← synth_coeff_of_mem S A hA, modelGauge_conjugation_synth]
  exact synth_mem T _

theorem modelGauge_symm_maps_span (T : QuaternionicStructure E)
    (A : E →L[ℝ] E) (hA : A ∈ quaternionicSpan T) :
    conjugation (modelGauge S T).symm A ∈ quaternionicSpan S := by
  rw [← synth_coeff_of_mem T A hA]
  have heq (a : Fin 3 → ℝ) :
      conjugation (modelGauge S T).symm (synth T a) = synth S a := by
    apply (conjugation (modelGauge S T)).injective
    rw [← conjugation_mul]
    have hmul : modelGauge S T * (modelGauge S T).symm = 1 := by
      change modelGauge S T * (modelGauge S T)⁻¹ = 1
      group
    rw [hmul, conjugation_one]
    exact (modelGauge_conjugation_synth S T a).symm
  rw [heq]
  exact synth_mem S _

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem frameConjugation_eq_adjoint (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (A : E →L[ℝ] E) :
    conjugation (frameTransitionIsometry Q i j x hi hj) A =
      (transitionAtlas Q.frames.adaptedCore).adjointCoordChange i j x A := by
  ext v
  rw [conjugation_apply, adjointCoordChange_apply]
  change Q.frames.coordChange i j x
      (A (Q.frames.coordChange j i x v)) =
    Q.frames.coordChange i j x (A (Q.frames.coordChange j i x v))
  rfl

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem frameConjugation_maps_span (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (A : E →L[ℝ] E) (hA : A ∈ quaternionicSpan (Q.reduction.Q i)) :
    conjugation (frameTransitionIsometry Q i j x hi hj) A ∈
      quaternionicSpan (Q.reduction.Q j) := by
  rw [frameConjugation_eq_adjoint Q i j x hi hj]
  apply Q.reduction.map_span_le i j x hi hj
  exact ⟨A, hA, rfl⟩

/-- An actual transition of adapted tangent frames, expressed relative to
one fixed quaternionic model. -/
def fixedTransition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    E ≃ₗᵢ[ℝ] E :=
  (modelGauge S (Q.reduction.Q j)).symm *
    frameTransitionIsometry Q i j x hi hj *
      modelGauge S (Q.reduction.Q i)

theorem fixedTransition_mem_normalizer (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    fixedTransition S Q i j x hi hj ∈ normalizer S := by
  intro A
  constructor
  · intro hA
    change conjugation
      ((modelGauge S (Q.reduction.Q j)).symm *
        frameTransitionIsometry Q i j x hi hj *
          modelGauge S (Q.reduction.Q i)) A ∈ quaternionicSpan S
    rw [conjugation_mul, conjugation_mul]
    apply modelGauge_symm_maps_span
    apply frameConjugation_maps_span Q i j x hi hj
    exact modelGauge_maps_span S (Q.reduction.Q i) A hA
  · intro hA
    have hback : conjugation
        (fixedTransition S Q i j x hi hj).symm
        (conjugation (fixedTransition S Q i j x hi hj) A) ∈
          quaternionicSpan S := by
      change conjugation
        ((modelGauge S (Q.reduction.Q i)).symm *
          frameTransitionIsometry Q j i x hj hi *
            modelGauge S (Q.reduction.Q j))
          (conjugation (fixedTransition S Q i j x hi hj) A) ∈ quaternionicSpan S
      rw [conjugation_mul, conjugation_mul]
      apply modelGauge_symm_maps_span
      apply frameConjugation_maps_span Q j i x hj hi
      exact modelGauge_maps_span S (Q.reduction.Q j) _ hA
    rw [← conjugation_mul] at hback
    have hinv : (fixedTransition S Q i j x hi hj).symm *
        fixedTransition S Q i j x hi hj = 1 := by
      change (fixedTransition S Q i j x hi hj)⁻¹ *
        fixedTransition S Q i j x hi hj = 1
      group
    simpa only [hinv, conjugation_one] using hback

end
end QuaternionicSymmetry.QuaternionicManifoldFixedNormalizer
