import QuaternionicSymmetry.ManifoldQuaternionicTopExteriorValue

/-! Intrinsic scalar density is exactly the coefficient of a genuine top
form's fixed-frame exterior value relative to the unscaled quaternionic
fundamental top power. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedDensityValue
open Module ManifoldDifferentialForms ManifoldFormExteriorEvaluation
open ManifoldFormExteriorReflection ManifoldQuaternionicTopExteriorValue
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicVolume
open ManifoldQuaternionicVolumeCoefficient ExteriorContinuousPairing
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem value_eq_density_smul_top
    (α : Form 𝓘(ℝ,E) M (Module.finrank ℝ E))
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
        (Module.finrank ℝ E) α =
      scalarDensity Q α ((extChartAt 𝓘(ℝ,E) p).symm y) •
        value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
          (Module.finrank ℝ E) (fundamentalTopForm Q) := by
  let L := (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
  let c := scalarDensity Q α ((extChartAt 𝓘(ℝ,E) p).symm y)
  have hlocal : localForm p y L (Module.finrank ℝ E) α =
      c • localForm p y L (Module.finrank ℝ E) (fundamentalTopForm Q) := by
    ext v
    have h := eq_scalarDensity_smul Q α ((extChartAt 𝓘(ℝ,E) p).symm y)
    have hv := congrArg (fun β : TangentSpace 𝓘(ℝ,E)
      ((extChartAt 𝓘(ℝ,E) p).symm y) [⋀^Fin (Module.finrank ℝ E)]→L[ℝ] ℝ =>
        β (fun i => mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,E)
          (extChartAt 𝓘(ℝ,E) p).symm (Set.range 𝓘(ℝ,E)) y (L (v i)))) h
    simpa only [localForm, inChartModel_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply] using hv
  have hrep : representative p y L (Module.finrank ℝ E) α =
      c • representative p y L (Module.finrank ℝ E) (fundamentalTopForm Q) := by
    apply toContinuous_injective
    rw [toContinuous_smul, representative_pairing, representative_pairing]
    exact hlocal
  exact congrArg Subtype.val hrep

theorem value_eq_density_smul_fixedPower
    (b : Basis ι ℝ E)
    (α : Form 𝓘(ℝ,E) M (Module.finrank ℝ E))
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
        (Module.finrank ℝ E) α =
      scalarDensity Q α ((extChartAt 𝓘(ℝ,E) p).symm y) •
        (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
  rw [value_eq_density_smul_top S Q α p y hy,
    value_fundamentalTopForm S Q b p y hy]

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedDensityValue
