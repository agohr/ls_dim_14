import QuaternionicSymmetry.ManifoldQuaternionicKSWScalarInput
import QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace
import QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus
import QuaternionicSymmetry.ManifoldQuaternionicScalarTraceComparison
import QuaternionicSymmetry.ContinuousWedgeInstances

/-! The precise rank-three curvature normalization of the quaternionic
four-form, derived from the registered KSW Lemma 3.10 formula. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWFourForm
open ManifoldQuaternionicKSWScalarInput QuaternionicManifoldFixedSolder
open QuaternionicManifoldFixedNormalizer QuaternionicFixedModelAdjointTrace
open QuaternionicManifoldProjectiveStandardConnection
open ManifoldQuaternionicFourForm ManifoldQuaternionicFourFormLocalCalculus
open ManifoldQuaternionicConnection ManifoldQuaternionicAdjointConnection
open ManifoldQuaternionicAdjointCurvature ManifoldQuaternionicCurvatureProjection
open ManifoldQuaternionicSymplecticCurvature QuaternionicLieAlgebraProjection
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open LocalEndomorphismTrace QuaternionicScalarTrace
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [Nontrivial E] in
theorem kahlerCoefficients_eq_chart (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (i : Fin 3) :
    kahlerCoefficients S Q p y u v i =
      chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) i ![u,v] := by
  rw [chartKahler_solder Q p y hy]
  let T := Q.reduction.Q (achart E p)
  let U := modelGauge S T
  have hgen (w : E) : U (quaternionicGenerator S i w) =
      quaternionicGenerator T i (U w) := by
    fin_cases i
    · exact modelGauge_I S T w
    · exact modelGauge_J S T w
    · exact modelGauge_K S T w
  change inner ℝ (quaternionicGenerator S i (U.symm (solder Q p y u)))
    (U.symm (solder Q p y v)) =
    inner ℝ (quaternionicGenerator T i (solder Q p y u)) (solder Q p y v)
  rw [← U.inner_map_map, hgen, U.apply_symm_apply, U.apply_symm_apply]

theorem inducedCurvature_eq_source
    (hsp : KSWSp1CurvatureFormula S Q D) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    inducedCurvature Q D p y u v =
      (-(2 * scalarRatio S Q D p y hy)) •
        adjointRepresentation S (synth S (kahlerCoefficients S Q p y u v)) := by
  have hcomm (a : Fin 3 → ℝ) :
      symplecticProjection (Q.reduction.Q (achart E p)) (D.curvature Q p y u v) *
        synth (Q.reduction.Q (achart E p)) a =
      synth (Q.reduction.Q (achart E p)) a *
        symplecticProjection (Q.reduction.Q (achart E p)) (D.curvature Q p y u v) := by
    rw [← symplecticCurvature_eq_projection Q D p y u v hy]
    exact symplecticCurvature_commutes Q D p y u v hy a
  rw [inducedCurvature_eq_adjoint Q D p y u v hy,
    ← adjointRepresentation_scalarProjection_fixed S (Q.reduction.Q (achart E p))
      (D.curvature Q p y u v) hcomm]
  change adjointRepresentation S
    (scalarProjection S (fixedTangentConjugation S Q p (D.curvature Q p y u v))) = _
  rw [hsp p y u v hy, map_smul]

theorem inducedCurvature_product_trace
    (hsp : KSWSp1CurvatureFormula S Q D) (p : M) (y u v a b : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    traceCLM (inducedCurvature Q D p y u v * inducedCurvature Q D p y a b) =
      (-32 * scalarRatio S Q D p y hy ^ 2) *
        ∑ i : Fin 3, kahlerCoefficients S Q p y u v i *
          kahlerCoefficients S Q p y a b i := by
  rw [inducedCurvature_eq_source S Q D hsp p y u v hy,
    inducedCurvature_eq_source S Q D hsp p y a b hy,
    smul_mul_smul_comm, map_smul, trace_adjoint_synth_product]
  simp only [smul_eq_mul]
  ring


omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem wedge_square_apply (α : E [⋀^Fin 2]→L[ℝ] ℝ) (a b c d : E) :
    ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) α α ![a,b,c,d] =
      2 * (α ![a,b] * α ![c,d] - α ![a,c] * α ![b,d] + α ![a,d] * α ![b,c]) := by
  change LocalChernWeilQuadratic.wedge22
    (LocalChernWeilQuadratic.traceProduct (ContinuousLinearMap.id ℝ ℝ)) α α _ = _
  rw [LocalChernWeilQuadraticTransgression.wedge22_trace_apply _
    (fun p q => mul_comm p q)]
  simp only [ContinuousLinearMap.id_apply]
  ring

theorem induced_traceSquareForm_eq_chartFour
    (hsp : KSWSp1CurvatureFormula S Q D) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    LocalChernWeilQuadratic.traceSquareForm traceCLM (inducedForm Q D p) y =
      (-32 * scalarRatio S Q D p y hy ^ 2) •
        chartFour Q (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0,w 1,w 2,w 3] := by ext i; fin_cases i <;> rfl
  rw [hw]
  simp only [LocalChernWeilQuadratic.traceSquareForm_apply traceCLM traceCLM_cyclic,
    LocalTraceSquareAlgebra.traceSquare4, map_add, map_sub,
    ContinuousAlternatingMap.smul_apply]
  change (2 : ℝ) • (traceCLM (inducedCurvature Q D p y (w 0) (w 1) *
      inducedCurvature Q D p y (w 2) (w 3)) -
    traceCLM (inducedCurvature Q D p y (w 0) (w 2) *
      inducedCurvature Q D p y (w 1) (w 3)) +
    traceCLM (inducedCurvature Q D p y (w 0) (w 3) *
      inducedCurvature Q D p y (w 1) (w 2))) = _
  rw [inducedCurvature_product_trace S Q D hsp p y _ _ _ _ hy,
    inducedCurvature_product_trace S Q D hsp p y _ _ _ _ hy,
    inducedCurvature_product_trace S Q D hsp p y _ _ _ _ hy]
  simp only [chartFour, Fin.sum_univ_three, ContinuousAlternatingMap.add_apply,
    wedge_square_apply, kahlerCoefficients_eq_chart S Q p y _ _ hy, smul_eq_mul]
  ring

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWFourForm
