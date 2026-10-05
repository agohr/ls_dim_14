import QuaternionicSymmetry.ManifoldQuaternionicFixedDensityValue

/-! The fixed quaternionic top power is nonzero, and its unique real
coefficient in each actual tangent top form equals `scalarDensity`. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedDensityCoefficient
open Module ManifoldDifferentialForms ManifoldFormExteriorEvaluation
open ManifoldFormExteriorReflection ManifoldQuaternionicTopExteriorValue
open ManifoldQuaternionicFixedDensityValue ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicVolume ManifoldQuaternionicVolumeCoefficient
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

include Q in
theorem fixedTopPower_ne_zero (b : Basis ι ℝ E) :
    (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension ≠ 0 := by
  let x : M := Classical.choice inferInstance
  let y := extChartAt 𝓘(ℝ,E) x x
  let hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  intro hz
  have hval : value x y (fixedSolderEquiv S Q x y hy).symm.toContinuousLinearMap
      (Module.finrank ℝ E) (fundamentalTopForm Q) = 0 := by
    exact (value_fundamentalTopForm S Q b x y hy).trans hz
  have hform := tangent_eq_of_value_eq x
    (fixedSolderEquiv S Q x y hy).symm
    (fundamentalTopForm Q) (0 : Form 𝓘(ℝ,E) M (Module.finrank ℝ E)) 0
    (by simpa using hval)
  have hzero : fundamentalTopForm Q x = 0 := by simpa using hform
  exact fundamentalTopForm_ne_zero Q x hzero

theorem fixedDensity_coefficient_iff
    (b : Basis ι ℝ E)
    (α : Form 𝓘(ℝ,E) M (Module.finrank ℝ E))
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (c : ℝ) :
    value p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
        (Module.finrank ℝ E) α =
      c • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension ↔
    scalarDensity Q α ((extChartAt 𝓘(ℝ,E) p).symm y) = c := by
  rw [value_eq_density_smul_fixedPower S Q b α p y hy]
  exact (smul_left_injective ℝ (fixedTopPower_ne_zero S Q b)).eq_iff

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedDensityCoefficient
