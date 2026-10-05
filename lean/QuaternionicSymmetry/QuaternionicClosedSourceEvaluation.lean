import QuaternionicSymmetry.QuaternionicClosedSourceGenerators
import QuaternionicSymmetry.ManifoldClosedPolynomialComparison
import QuaternionicSymmetry.QuaternionicManifoldWeylRankTraceForms
import QuaternionicSymmetry.ManifoldQuaternionicFixedFundamental

/-! The genuine closed characteristic generators evaluate to the exact Weyl
trace variables and normalized fundamental form used in the pointwise certificates. -/
namespace QuaternionicSymmetry.QuaternionicClosedSourceEvaluation
open Module QuaternionicClosedSourceGenerators ManifoldEvenClosedEvaluation
open ManifoldFormExteriorEvaluation ExteriorContinuousPairing
open QuaternionicCorrectedSourceTraceForms QuaternionicWeylMatrixCoefficients
open QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureOrbitalSign
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicManifoldWeylRankTraceForms ManifoldQuaternionicFixedFundamental
open ManifoldQuaternionicAdjointChernWeil ManifoldDeRhamAllDegrees
open QuaternionicContinuousFundamental MatrixTracePolynomial
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourceGrade_value
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W), ∀ k : ℕ,
      gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap (k+1)
        (sourceGrade S Q D t k) =
      signedTracePower (complexifiedMatrix
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) (k+1) := by
  obtain ⟨W, hW, htrace⟩ := closedSourceTrace_eq_rank_weyl S Q D hsp hdecomp b t p y hy ht
  refine ⟨W, hW, ?_⟩
  intro k
  have hp : representative p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
      _ (closedSourceEvenTrace S Q D t (k+1)).val.val =
      tangentTraceRepresentative S W (HyperWeylFiber.mem_skewCentralizer S hW) b (k+1) := by
    apply toContinuous_injective
    rw [representative_pairing]
    ext v
    exact htrace (k+1) (Nat.succ_pos k) v
  apply Subtype.ext
  change value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap _
    (castClosedDegree (sourceDegree k) (closedSourceEvenTrace S Q D t (k+1))).val.val = _
  rw [castClosedDegree_form, value_cast]
  change (representative p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
    _ (closedSourceEvenTrace S Q D t (k+1)).val.val).val = _
  rw [hp, tangentTraceRepresentative_val S W _ b (k+1) (Nat.succ_pos k)]

set_option maxRecDepth 2000 in
theorem quarterGrade_value
    (hsp : KSWSp1CurvatureFormula S Q D) (r : ℝ)
    (hr : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = r)
    (b : Basis ι ℝ E) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 1
      (quarterPontryaginCandidateForm Q D) =
      (r / Real.pi) ^ 2 • QuaternionicFundamental.form S b := by
  have hp : representative p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
      4 (quarterPontryaginCandidateForm Q D).val.val =
      (r / Real.pi) ^ 2 • fundamentalPower S b := by
    apply toContinuous_injective
    rw [representative_pairing, toContinuous_smul]
    ext v
    exact quarterForm_fixed S Q D hsp r hr b p y hy v
  apply Subtype.ext
  change (representative p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
    4 (quarterPontryaginCandidateForm Q D).val.val).val = _
  rw [hp]
  rfl

end
end QuaternionicSymmetry.QuaternionicClosedSourceEvaluation
