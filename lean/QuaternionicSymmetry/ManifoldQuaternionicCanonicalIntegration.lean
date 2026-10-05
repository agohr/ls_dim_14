import QuaternionicSymmetry.ManifoldQuaternionicCanonicalVolume
import QuaternionicSymmetry.ManifoldQuaternionicCohomologyIntegration

/-! Canonical integration and Stokes on compact quaternionic manifolds,
using the measure constructed from the actual fundamental top form. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCanonicalIntegration

open MeasureTheory ManifoldDifferentialForms ManifoldDeRhamWedge
  ManifoldQuaternionicMetric ManifoldQuaternionicVolume
  ManifoldQuaternionicVolumeCoefficient ManifoldQuaternionicDensityIntegration
  ManifoldQuaternionicCanonicalVolume ManifoldQuaternionicGlobalStokes
  ManifoldQuaternionicCohomologyIntegration
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The actual top-form integration functional, with no supplied measure. -/
def integral : SmoothTopForms (E := E) (M := M) →ₗ[ℝ] ℝ :=
  densityIntegral Q (quaternionicVolumeMeasure Q)

theorem stokes {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : Form 𝓘(ℝ, E) M n) (hα : ChartSmooth α) :
    integral Q ⟨castForm hdim (exteriorDerivative α),
      chartSmooth_castForm _ _ (chartSmooth_exteriorDerivative _ hα)⟩ = 0 :=
  integral_exact_eq_zero Q (quaternionicVolumeMeasure Q)
    (quaternionicVolumeMeasure_restrict_chart Q) hdim α hα

/-- Canonical integration on the actual positive-degree de Rham quotient. -/
def integrateClass {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E) :
    positiveDegreeCohomology (E := E) (M₀ := M) n →ₗ[ℝ] ℝ :=
  cohomologyIntegral Q (quaternionicVolumeMeasure Q)
    (quaternionicVolumeMeasure_restrict_chart Q) hdim

theorem integrateClass_representative {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : closedForms (E := E) (M₀ := M) (n + 1)) :
    integrateClass Q hdim (closedFormClass n α) =
      integral Q ⟨castForm hdim α.val.val, chartSmooth_castForm _ _ α.val.property⟩ := rfl

theorem integral_nonneg (α : SmoothTopForms (E := E) (M := M))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (α.val x)) :
    0 ≤ integral Q α := densityIntegral_nonneg Q (quaternionicVolumeMeasure Q) α hα

theorem integral_topForm :
    integral Q ⟨fundamentalTopForm Q, fundamentalTopForm_smooth Q⟩ =
      (quaternionicVolumeMeasure Q).real Set.univ :=
  densityIntegral_topForm Q (quaternionicVolumeMeasure Q)

theorem integral_pos (α : SmoothTopForms (E := E) (M := M))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (α.val x))
    (x : M) (hx : α.val x ≠ 0) : 0 < integral Q α :=
  densityIntegral_pos Q (quaternionicVolumeMeasure Q) α hα x hx

theorem integral_topForm_pos :
    0 < integral Q ⟨fundamentalTopForm Q, fundamentalTopForm_smooth Q⟩ := by
  apply integral_pos Q _ (fun x => ⟨1, zero_le_one, (one_smul ℝ _).symm⟩)
    (Classical.arbitrary M)
  exact fundamentalTopForm_ne_zero Q _

theorem positive_class_ne_zero {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : closedForms (E := E) (M₀ := M) (n + 1))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (castForm hdim α.val.val x))
    (x : M) (hx : castForm hdim α.val.val x ≠ 0) : closedFormClass n α ≠ 0 :=
  class_ne_zero_of_positive Q (quaternionicVolumeMeasure Q)
    (quaternionicVolumeMeasure_restrict_chart Q) hdim α hα x hx

end
end QuaternionicSymmetry.ManifoldQuaternionicCanonicalIntegration
