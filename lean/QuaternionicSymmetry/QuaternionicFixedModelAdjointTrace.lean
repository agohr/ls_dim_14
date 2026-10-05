import QuaternionicSymmetry.QuaternionicStandardTraceProduct
import QuaternionicSymmetry.QuaternionicManifoldModelProjection
import QuaternionicSymmetry.ManifoldQuaternionicCurvaturePreservesSpan

/-! Fixed quaternionic model gauge preserves the actual rank-three adjoint
operator, because it carries the three named generators without rotating
their coefficient coordinates. -/
namespace QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace

open QuaternionicManifoldFixedNormalizer QuaternionicManifoldModelProjection
  QuaternionicIsometryNormalizer
  LocalEndomorphismTrace
  QuaternionicLieAlgebraProjection ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicCurvaturePreservesSpan
  ManifoldQuaternionicRankThreeOrientation
  ManifoldQuaternionicConnection
open scoped ContDiff Manifold
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S T : QuaternionicStructure E)

theorem adjointRepresentation_fixedConjugation (A : E →L[ℝ] E)
    (hA : PreservesSpan T A) :
    adjointRepresentation S (conjugation (modelGauge S T).symm A) =
      adjointRepresentation T A := by
  let C := conjugation (modelGauge S T).symm
  apply ContinuousLinearMap.ext
  intro a
  have hinj : Function.Injective (synth S) := by
    intro b c h
    calc
      b = coeff S (synth S b) := (coeff_synth S b).symm
      _ = coeff S (synth S c) := by rw [h]
      _ = c := coeff_synth S c
  apply hinj
  let B := A * synth T a - synth T a * A
  have hB : B ∈ quaternionicSpan T := hA _ (synth_mem T a)
  have hCB : C B ∈ quaternionicSpan S :=
    modelGauge_symm_maps_span S T B hB
  have hc : C B = C A * synth S a - synth S a * C A := by
    dsimp [B]
    rw [map_sub, conjugation_product, conjugation_product,
      modelGauge_symm_conjugation_synth S T a]
  calc
    synth S (adjointRepresentation S (C A) a) = C B := by
      rw [adjointRepresentation_apply]
      change synth S (coeff S (C A * synth S a - synth S a * C A)) = C B
      rw [← hc]
      exact synth_coeff_of_mem S _ hCB
    _ = C (synth T (adjointRepresentation T A a)) := by
      rw [adjointRepresentation_apply]
      exact congrArg C (synth_coeff_of_mem T B hB).symm
    _ = synth S (adjointRepresentation T A a) :=
      modelGauge_symm_conjugation_synth S T _

theorem scalarProjection_fixedConjugation (A : E →L[ℝ] E)
    (hsp : ∀ a, symplecticProjection T A * synth T a =
      synth T a * symplecticProjection T A) :
    scalarProjection S (conjugation (modelGauge S T).symm A) =
      conjugation (modelGauge S T).symm (scalarProjection T A) := by
  let C := conjugation (modelGauge S T).symm
  have hp := symplecticProjection_modelGauge S T A hsp
  have hS := projection_sum S (C A)
  have hT := congrArg C (projection_sum T A)
  rw [map_add, ← hp] at hT
  exact add_left_cancel (hS.trans hT.symm)

theorem adjointRepresentation_scalarProjection_fixed (A : E →L[ℝ] E)
    (hsp : ∀ a, symplecticProjection T A * synth T a =
      synth T a * symplecticProjection T A) :
    adjointRepresentation S
      (scalarProjection S (conjugation (modelGauge S T).symm A)) =
        adjointRepresentation T A := by
  rw [scalarProjection_fixedConjugation S T A hsp]
  have hscalar : PreservesSpan T (scalarProjection T A) := by
    intro U hU
    rw [← synth_coeff_of_mem T U hU]
    change (scalarProjection T A * synth T (coeff T U) -
      synth T (coeff T U) * scalarProjection T A) ∈ quaternionicSpan T
    rw [show scalarProjection T A = synth T _ from rfl,
      synth_commutator_cross]
    exact (quaternionicSpan T).smul_mem _ (synth_mem T _)
  rw [adjointRepresentation_fixedConjugation S T _ hscalar]
  have hz : adjointRepresentation T (symplecticProjection T A) = 0 :=
    adjointRepresentation_eq_zero_of_commutes T _ hsp
  have hs := congrArg (adjointRepresentation T) (projection_sum T A)
  rw [map_add, hz, zero_add] at hs
  exact hs

omit [Nontrivial E] in
theorem traceCLM_fixedConjugation (A : E →L[ℝ] E) :
    traceCLM (conjugation (modelGauge S T).symm A) = traceCLM A := by
  rw [traceCLM_apply, traceCLM_apply]
  have h := LinearMap.trace_conj' A.toLinearMap
    (modelGauge S T).symm.toLinearEquiv
  exact h

omit [Nontrivial E] in
theorem traceCLM_fixedConjugation_product (A B : E →L[ℝ] E) :
    traceCLM (conjugation (modelGauge S T).symm A *
      conjugation (modelGauge S T).symm B) = traceCLM (A * B) := by
  rw [← conjugation_product, traceCLM_fixedConjugation]

/-- The fixed-model standard block trace expressed in the original adapted
chart's symplectic and rank-three components. -/
theorem standardLie_fixed_product_trace (A B : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection T A * synth T a =
      synth T a * symplecticProjection T A)
    (hB : ∀ a, symplecticProjection T B * synth T a =
      synth T a * symplecticProjection T B) :
    traceCLM
      (QuaternionicProjectiveStandardLie.standardLie S
          (conjugation (modelGauge S T).symm A) *
        QuaternionicProjectiveStandardLie.standardLie S
          (conjugation (modelGauge S T).symm B)) =
      traceCLM (symplecticProjection T A * symplecticProjection T B) +
        (1 / 2 : ℝ) *
          traceCLM (adjointRepresentation T A * adjointRepresentation T B) := by
  rw [QuaternionicStandardTraceProduct.standardLie_product_trace]
  rw [symplecticProjection_modelGauge S T A hA,
    symplecticProjection_modelGauge S T B hB,
    traceCLM_fixedConjugation_product]
  rw [adjointRepresentation_scalarProjection_fixed S T A hA,
    adjointRepresentation_scalarProjection_fixed S T B hB]

end
end QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace
