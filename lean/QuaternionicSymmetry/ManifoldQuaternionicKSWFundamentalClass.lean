import QuaternionicSymmetry.ManifoldQuaternionicKSWFourForm
import QuaternionicSymmetry.ManifoldQuaternionicKSWConstantScalarInput
import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
import QuaternionicSymmetry.ManifoldQuaternionicFundamentalClass

/-! The analytic quarter-Pontryagin form equals a precisely normalized
positive multiple of the actual quaternionic fundamental form. The KSW
curvature and constant-scalar statements remain explicit source premises;
comparison with a topological Pontryagin class is a separate obligation. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWFundamentalClass
open ManifoldQuaternionicKSWFourForm ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWConstantScalarInput ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicAdjointChernWeil ManifoldQuaternionicFundamentalClass
open ManifoldQuaternionicFourFormGluing ManifoldDifferentialForms
open ManifoldDeRhamWedge ManifoldDeRhamRing LocalChernWeilTracePowers
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem traceSquare_eq_fundamental
    (hsp : KSWSp1CurvatureFormula S Q D) (r : ℝ)
    (hr : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = r) :
    closedTraceCurvatureSquare Q D = (-32 * r ^ 2) • closedFundamental Q D := by
  apply Subtype.ext
  apply Subtype.ext
  apply form_ext_center
  intro x
  change inChartModel x (traceCurvatureSquare Q D) (extChartAt 𝓘(ℝ,E) x x) =
    inChartModel x ((-32 * r ^ 2) • fundamentalFourForm Q) (extChartAt 𝓘(ℝ,E) x x)
  rw [inChartModel_smul, traceCurvatureSquare_chart Q D x (mem_extChartAt_target x)]
  rw [traceCurvaturePowerForm, tracePowerForm_one_eq_traceSquareForm]
  rw [induced_traceSquareForm_eq_chartFour S Q D hsp x _ (mem_extChartAt_target x),
    hr x _ (mem_extChartAt_target x)]
  have hf := (fourFormData Q).inChartModel_toForm x (mem_extChartAt_target x)
  exact congrArg (fun α => (-32 * r ^ 2) • α) hf.symm

theorem quarterForm_eq_fundamental
    (hsp : KSWSp1CurvatureFormula S Q D) (r : ℝ)
    (hr : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = r) :
    quarterPontryaginCandidateForm Q D =
      (r ^ 2 / Real.pi ^ 2) • closedFundamental Q D := by
  rw [quarterPontryaginCandidateForm, traceSquare_eq_fundamental S Q D hsp r hr,
    smul_smul]
  congr 1
  ring

theorem quarterClass_eq_fundamental
    (hsp : KSWSp1CurvatureFormula S Q D) (r : ℝ)
    (hr : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = r) :
    quarterPontryaginCandidateClass Q D =
      (r ^ 2 / Real.pi ^ 2) • fundamentalClass Q D := by
  change closedFormClass 3 (quarterPontryaginCandidateForm Q D) = _
  rw [quarterForm_eq_fundamental S Q D hsp r hr, closedFormClass_smul]
  rfl

/-- Exact scalar-curvature coefficient of the analytic quarter class. -/
theorem quarterForm_eq_scalar
    (G : PositiveScalarTangentGeometry Q)
    (hsp : KSWSp1CurvatureFormula S Q G.connection) (κ : ℝ)
    (hκ : ∀ x : M, preferredScalarCurvature Q G.connection x = κ) :
    quarterPontryaginCandidateForm Q G.connection =
      ((κ / (16 * (S.quaternionicDimension : ℝ) *
        ((S.quaternionicDimension : ℝ) + 2))) ^ 2 / Real.pi ^ 2) •
        closedFundamental Q G.connection :=
  quarterForm_eq_fundamental S Q G.connection hsp _
    (scalarRatio_eq_const S Q G κ hκ)


theorem exists_positive_fundamental_multiple
    (hconstant : KSWConstantScalarOnConnectedModel (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q) (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ t : ℝ, 0 < t ∧ 0 < t ^ 4 / Real.pi ^ 2 ∧
      quarterPontryaginCandidateForm Q G.connection =
        (t ^ 4 / Real.pi ^ 2) • closedFundamental Q G.connection := by
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter S Q hconstant G hn hconn
  refine ⟨t, htpos, div_pos (pow_pos htpos 4) (sq_pos_of_pos Real.pi_pos), ?_⟩
  have h := quarterForm_eq_fundamental S Q G.connection
    (formula_of_KSWLemma310OnModel S Q hsp G hn) (t ^ 2) (fun p y hy => (ht p y hy).symm)
  have ht4 : (t ^ 2) ^ 2 = t ^ 4 := by ring
  simpa only [ht4] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWFundamentalClass
