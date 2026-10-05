import QuaternionicSymmetry.ManifoldQuaternionicGlobalStokes
import QuaternionicSymmetry.ManifoldDeRhamRing

/-! Integration descends through the actual closed/exact quotient once the
measure has the verified chart-volume restrictions. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCohomologyIntegration

open MeasureTheory ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
  ManifoldQuaternionicMetric ManifoldQuaternionicVolume
  ManifoldQuaternionicVolumeCoefficient ManifoldQuaternionicDensityIntegration
  ManifoldQuaternionicGlobalStokes ManifoldTopFormLocalMeasure
open scoped Manifold ContDiff Topology
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (μ : Measure M) [IsFiniteMeasure μ]

def closedIntegral {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E) :
    closedForms (E := E) (M₀ := M) (n + 1) →ₗ[ℝ] ℝ where
  toFun α := densityIntegral Q μ
    ⟨castForm hdim α.val.val, chartSmooth_castForm _ _ α.val.property⟩
  map_add' α β := by
    have he : (⟨castForm hdim (α + β).val.val, chartSmooth_castForm _ _ (α + β).val.property⟩ :
        SmoothTopForms (E := E) (M := M)) =
        ⟨castForm hdim α.val.val, chartSmooth_castForm _ _ α.val.property⟩ +
          ⟨castForm hdim β.val.val, chartSmooth_castForm _ _ β.val.property⟩ := by
      apply Subtype.ext
      exact castForm_add hdim α.val.val β.val.val
    rw [he, map_add]
  map_smul' c α := by
    have he : (⟨castForm hdim (c • α).val.val, chartSmooth_castForm _ _ (c • α).val.property⟩ :
        SmoothTopForms (E := E) (M := M)) =
        c • ⟨castForm hdim α.val.val, chartSmooth_castForm _ _ α.val.property⟩ := by
      apply Subtype.ext
      exact castForm_smul hdim c α.val.val
    rw [he, map_smul]
    rfl

variable (hlocal : ∀ p : M, μ.restrict (extChartAt 𝓘(ℝ, E) p).source =
    chartMeasure (fundamentalTopForm Q) p)

include hlocal in
theorem exact_le_closedIntegral_ker {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E) :
    exactClosedAddSubgroup (E := E) (M₀ := M) n ≤
      (closedIntegral Q μ hdim).toAddMonoidHom.ker := by
  intro α hα
  rcases hα with ⟨β, hβ⟩
  change closedIntegral Q μ hdim α = 0
  change (∫ x, scalarDensity Q (castForm hdim α.val.val) x ∂μ) = 0
  have he := congrArg (fun z : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := n + 1) => z.val) hβ
  change exteriorDerivative β.val = α.val.val at he
  rw [← he]
  exact integral_exact_eq_zero Q μ hlocal hdim β.val β.property

def cohomologyIntegralAddHom {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E) :
    positiveDegreeCohomology (E := E) (M₀ := M) n →+ ℝ :=
  QuotientAddGroup.lift (exactClosedAddSubgroup n) (closedIntegral Q μ hdim).toAddMonoidHom
    (exact_le_closedIntegral_ker Q μ hlocal hdim)

theorem cohomologyIntegral_class {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : closedForms (E := E) (M₀ := M) (n + 1)) :
    cohomologyIntegralAddHom Q μ hlocal hdim (closedFormClass n α) =
      closedIntegral Q μ hdim α := rfl

def cohomologyIntegral {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E) :
    positiveDegreeCohomology (E := E) (M₀ := M) n →ₗ[ℝ] ℝ where
  toFun := cohomologyIntegralAddHom Q μ hlocal hdim
  map_add' := (cohomologyIntegralAddHom Q μ hlocal hdim).map_add
  map_smul' c a := by
    refine QuotientAddGroup.induction_on a ?_
    intro α
    change closedIntegral Q μ hdim (c • α) = c • closedIntegral Q μ hdim α
    exact (closedIntegral Q μ hdim).map_smul c α

theorem cohomologyIntegral_apply_class {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : closedForms (E := E) (M₀ := M) (n + 1)) :
    cohomologyIntegral Q μ hlocal hdim (closedFormClass n α) =
      closedIntegral Q μ hdim α := rfl

theorem integral_class_nonneg {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : closedForms (E := E) (M₀ := M) (n + 1))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (castForm hdim α.val.val x)) :
    0 ≤ cohomologyIntegral Q μ hlocal hdim (closedFormClass n α) :=
  densityIntegral_nonneg Q μ _ hα

include hlocal in
theorem class_ne_zero_of_positive [μ.IsOpenPosMeasure]
    {n : ℕ} (hdim : n + 1 = Module.finrank ℝ E)
    (α : closedForms (E := E) (M₀ := M) (n + 1))
    (hα : ∀ x, PositiveRay.Contains (fundamentalTopForm Q x) (castForm hdim α.val.val x))
    (x : M) (hx : castForm hdim α.val.val x ≠ 0) : closedFormClass n α ≠ 0 := by
  have hp : 0 < cohomologyIntegral Q μ hlocal hdim (closedFormClass n α) :=
    densityIntegral_pos Q μ _ hα x hx
  intro hz
  rw [hz, map_zero] at hp
  exact (lt_irrefl (0 : ℝ)) hp

end
end QuaternionicSymmetry.ManifoldQuaternionicCohomologyIntegration
