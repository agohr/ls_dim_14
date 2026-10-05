import QuaternionicSymmetry.ManifoldQuaternionicKSWFundamentalClass
import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
import QuaternionicSymmetry.QuaternionicContinuousFundamental
import QuaternionicSymmetry.ExteriorContinuousPowers

/-! The actual fundamental and normalized quaternionic four-forms, transported
by the inverse solder, equal the fixed exterior forms used by the certificates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedFundamental
open Module ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWFourForm ManifoldQuaternionicKSWFundamentalClass
open ManifoldQuaternionicFourForm ManifoldQuaternionicFourFormGluing
open ManifoldQuaternionicFourFormLocalCalculus QuaternionicContinuousFundamental
open ExteriorContinuousPairing ManifoldDifferentialForms
open ManifoldQuaternionicAdjointChernWeil ManifoldQuaternionicFundamentalClass
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [Nontrivial E] in
theorem chartKahler_comp_fixed (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (i : Fin 3) :
    (chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) i).compContinuousLinearMap
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap =
    kahler S i := by
  ext v
  have hv : v = ![v 0, v 1] := by ext j; fin_cases j <;> rfl
  rw [hv]
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hm : (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap ∘ ![v 0, v 1] =
      ![(fixedSolderEquiv S Q p y hy).symm (v 0),
        (fixedSolderEquiv S Q p y hy).symm (v 1)] := by
    ext j
    fin_cases j <;> rfl
  rw [hm]
  rw [← kahlerCoefficients_eq_chart S Q _ _ _ _ hy]
  simp only [kahlerCoefficients, ← fixedSolderEquiv_apply S Q p y hy,
    ContinuousLinearEquiv.apply_symm_apply]
  exact (frameKahler_apply S i ![v 0, v 1]).symm

omit [Nontrivial E] in
theorem chartFour_comp_fixed (b : Basis ι ℝ E) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    (chartFour Q (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y)).compContinuousLinearMap
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap =
    toContinuous 4 (fundamentalPower S b) := by
  rw [toContinuous_fundamentalPower]
  ext v
  simp only [chartFour, fundamental, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := ExteriorContinuousPowers.wedge_comp
    (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
    (chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) i)
    (chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) i)
  rw [chartKahler_comp_fixed S Q p y hy] at h
  exact congrArg (fun α => α v) h

theorem fundamentalForm_fixed (b : Basis ι ℝ E) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : Fin 4 → E) :
    inChartModel p (fundamentalFourForm Q) y
      (fun i => (fixedSolderEquiv S Q p y hy).symm (v i)) =
    toContinuous 4 (fundamentalPower S b) v := by
  rw [fundamentalFourForm, (fourFormData Q).inChartModel_toForm p hy]
  exact congrArg (fun α => α v) (chartFour_comp_fixed S Q b p y hy)

theorem quarterForm_fixed
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (hsp : KSWSp1CurvatureFormula S Q D) (r : ℝ)
    (hr : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = r)
    (b : Basis ι ℝ E) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : Fin 4 → E) :
    inChartModel p (quarterPontryaginCandidateForm Q D).val.val y
      (fun i => (fixedSolderEquiv S Q p y hy).symm (v i)) =
    (r / Real.pi) ^ 2 * toContinuous 4 (fundamentalPower S b) v := by
  rw [quarterForm_eq_fundamental S Q D hsp r hr]
  change inChartModel p ((r ^ 2 / Real.pi ^ 2) • fundamentalFourForm Q) y _ = _
  rw [inChartModel_smul]
  change (r ^ 2 / Real.pi ^ 2) * inChartModel p (fundamentalFourForm Q) y _ = _
  rw [fundamentalForm_fixed S Q b p y hy, div_pow]

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedFundamental
