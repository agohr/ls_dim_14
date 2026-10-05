import QuaternionicSymmetry.QuaternionicTraceOrthogonality

/-! Exact real trace normalization of scalar quaternionic endomorphisms. -/
namespace QuaternionicSymmetry.QuaternionicScalarTrace

open LocalEndomorphismTrace VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E]

theorem synth_anticommutator (S : QuaternionicStructure E) (a b : Fin 3 → ℝ) :
    synth S a * synth S b + synth S b * synth S a =
      (-(2 * ∑ i : Fin 3, a i * b i)) • (1 : E →L[ℝ] E) := by
  ext v
  simp [synth_apply, Fin.sum_univ_three, quaternionicGenerator,
    S.J_I_anti, S.I_sq, S.J_sq]
  module

variable [FiniteDimensional ℝ E]

theorem trace_synth_product (S : QuaternionicStructure E) (a b : Fin 3 → ℝ) :
    traceCLM (synth S a * synth S b) =
      -(Module.finrank ℝ E : ℝ) * ∑ i : Fin 3, a i * b i := by
  have h := congrArg (traceCLM (V := E)) (synth_anticommutator S a b)
  have hdim : traceCLM (1 : E →L[ℝ] E) = (Module.finrank ℝ E : ℝ) :=
    LinearMap.trace_id ℝ E
  rw [map_add, map_smul, hdim, traceCLM_cyclic (synth S b) (synth S a)] at h
  simp only [smul_eq_mul] at h
  linarith

theorem trace_adjoint_synth_product (S : QuaternionicStructure E) (a b : Fin 3 → ℝ) :
    traceCLM (ManifoldQuaternionicAdjointConnection.adjointRepresentation S (synth S a) *
      ManifoldQuaternionicAdjointConnection.adjointRepresentation S (synth S b)) =
        -8 * ∑ i : Fin 3, a i * b i := by
  rw [traceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 3))]
  simp [Matrix.trace,
    QuaternionicLieAlgebraProjection.adjointRepresentation_synth,
    crossProduct, Fin.sum_univ_three]
  ring

theorem trace_synth_product_eq_adjoint (S : QuaternionicStructure E) (a b : Fin 3 → ℝ) :
    traceCLM (synth S a * synth S b) =
      ((Module.finrank ℝ E : ℝ) / 8) *
        traceCLM (ManifoldQuaternionicAdjointConnection.adjointRepresentation S (synth S a) *
          ManifoldQuaternionicAdjointConnection.adjointRepresentation S (synth S b)) := by
  rw [trace_synth_product, trace_adjoint_synth_product]
  ring

end
end QuaternionicSymmetry.QuaternionicScalarTrace
