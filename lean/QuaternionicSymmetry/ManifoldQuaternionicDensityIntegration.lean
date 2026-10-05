import QuaternionicSymmetry.ManifoldQuaternionicVolumeCoefficient
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integration of the intrinsic scalar density against a supplied finite
Borel measure on a compact manifold. This provides linearity and positivity;
the canonical volume measure and Stokes theorem are separate obligations. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicDensityIntegration

open Module MeasureTheory ManifoldDifferentialForms ManifoldQuaternionicMetric
  ManifoldQuaternionicVolume ManifoldQuaternionicVolumeCoefficient
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (μ : Measure M) [IsFiniteMeasure μ]

abbrev SmoothTopForms := smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := Module.finrank ℝ E)

theorem density_integrable (α : SmoothTopForms (E := E) (M := M)) :
    Integrable (scalarDensity Q α.val) μ := by
  have h : ContinuousOn (scalarDensity Q α.val) Set.univ :=
    (scalarDensity_smooth Q α.val α.property).continuous.continuousOn
  exact integrableOn_univ.mp
    (h.integrableOn_of_subset_isCompact isCompact_univ MeasurableSet.univ
      (Set.Subset.refl Set.univ) (measure_ne_top μ Set.univ))

/-- The linear integral of the scalar density relative to the given measure. -/
def densityIntegral : SmoothTopForms (E := E) (M := M) →ₗ[ℝ] ℝ where
  toFun α := ∫ x, scalarDensity Q α.val x ∂μ
  map_add' α β := by
    have he : scalarDensity Q (α + β).val = scalarDensity Q α.val + scalarDensity Q β.val :=
      (scalarDensity Q).map_add _ _
    rw [he]
    exact integral_add (density_integrable Q μ α) (density_integrable Q μ β)
  map_smul' r α := by
    have he : scalarDensity Q (r • α).val = r • scalarDensity Q α.val :=
      (scalarDensity Q).map_smul _ _
    rw [he]
    exact integral_smul r _

theorem densityIntegral_nonneg (α : SmoothTopForms (E := E) (M := M))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (α.val x)) :
    0 ≤ densityIntegral Q μ α := by
  apply integral_nonneg
  intro x
  exact (positive_ray_iff Q α.val x).mp (hα x)

theorem densityIntegral_topForm :
    densityIntegral Q μ ⟨fundamentalTopForm Q, fundamentalTopForm_smooth Q⟩ =
      μ.real Set.univ := by
  change (∫ x, scalarDensity Q (fundamentalTopForm Q) x ∂μ) = _
  simp only [scalarDensity_topForm, integral_const, smul_eq_mul, mul_one]

theorem densityIntegral_pos [μ.IsOpenPosMeasure]
    (α : SmoothTopForms (E := E) (M := M))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (α.val x))
    (x : M) (hx : α.val x ≠ 0) : 0 < densityIntegral Q μ α := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (scalarDensity_smooth Q α.val α.property).continuous (density_integrable Q μ α)
    (fun y => (positive_ray_iff Q α.val y).mp (hα y))
  intro hz
  apply hx
  rw [eq_scalarDensity_smul Q α.val x, hz, zero_smul]

end
end QuaternionicSymmetry.ManifoldQuaternionicDensityIntegration
