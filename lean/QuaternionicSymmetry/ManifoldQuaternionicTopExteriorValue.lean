import QuaternionicSymmetry.ManifoldFormExteriorReflection
import QuaternionicSymmetry.ManifoldQuaternionicFixedFundamental
import QuaternionicSymmetry.ManifoldQuaternionicVolumeCoefficient

/-! Exact exterior-algebra value of the genuine quaternionic fundamental
four-form and its unscaled top wedge in a fixed quaternionic solder frame. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTopExteriorValue
open Module ManifoldDifferentialForms ManifoldFormExteriorEvaluation
open ManifoldFormExteriorReflection ManifoldQuaternionicFixedFundamental
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicFourFormGluing
open ManifoldQuaternionicVolume ManifoldQuaternionicVolumeCoefficient
open QuaternionicContinuousFundamental ExteriorContinuousPairing
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [Nonempty M] in
theorem value_fundamentalFourForm (b : Basis ι ℝ E)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 4
      (fundamentalFourForm Q) = (QuaternionicFundamental.form S b).val := by
  have hlocal : localForm p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 4
      (fundamentalFourForm Q) = toContinuous 4 (fundamentalPower S b) := by
    ext v
    exact fundamentalForm_fixed S Q b p y hy v
  have hpower : representative p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 4
      (fundamentalFourForm Q) = fundamentalPower S b := by
    apply toContinuous_injective
    rw [representative_pairing]
    exact hlocal
  exact congrArg Subtype.val hpower

theorem value_fundamentalTopForm (b : Basis ι ℝ E)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
        (Module.finrank ℝ E) (fundamentalTopForm Q) =
      (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
  have hqdim : Module.finrank ℝ E / 4 = S.quaternionicDimension := by
    have h := S.real_finrank
    omega
  rw [fundamentalTopForm,
    value_cast (p := p) (y := y)
      (L := (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap)
      (model_dimension Q)]
  rw [value_formPower, value_fundamentalFourForm S Q b p y hy, hqdim]

end
end QuaternionicSymmetry.ManifoldQuaternionicTopExteriorValue
