import QuaternionicSymmetry.ManifoldQuaternionicVolume
import QuaternionicSymmetry.ContinuousTopFormCoefficient

/-! Intrinsic scalar densities relative to the smooth nonvanishing quaternionic
top form. Their chart expressions are smooth ratios of actual form values. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicVolumeCoefficient

open Module ManifoldDifferentialForms ManifoldQuaternionicMetric
  ManifoldQuaternionicVolume ContinuousTopFormCoefficient
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

private noncomputable instance tangentNormedGroup (x : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedAddCommGroup E
  infer_instance
private noncomputable instance tangentNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedSpace ℝ E
  infer_instance

def tangentBasis (x : M) : Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  Module.finBasis ℝ E

/-- The unique scalar multiplying the actual quaternionic top form. -/
def scalarDensity : Form 𝓘(ℝ, E) M (Module.finrank ℝ E) →ₗ[ℝ] (M → ℝ) where
  toFun α x := coefficient (tangentBasis x) (fundamentalTopForm Q x) (α x)
  map_add' α β := by ext x; exact (coefficient _ _).map_add _ _
  map_smul' r α := by ext x; exact (coefficient _ _).map_smul _ _

theorem eq_scalarDensity_smul (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (x : M) :
    α x = scalarDensity Q α x • fundamentalTopForm Q x :=
  eq_coefficient_smul _ _ _ (fundamentalTopForm_ne_zero Q x)

theorem scalarDensity_topForm (x : M) : scalarDensity Q (fundamentalTopForm Q) x = 1 :=
  coefficient_self _ _ (fundamentalTopForm_ne_zero Q x)

theorem scalarDensity_chart (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (p : M) {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    scalarDensity Q α ((extChartAt 𝓘(ℝ, E) p).symm y) =
      inChartModel p α y (Module.finBasis ℝ E) /
        inChartModel p (fundamentalTopForm Q) y (Module.finBasis ℝ E) := by
  symm
  apply (coefficient_eq_iff (Module.finBasis ℝ E) _ _
    (fundamentalTopForm_chart_ne_zero Q p hy) _).mpr
  ext v
  simp only [inChartModel_self_apply, ContinuousAlternatingMap.smul_apply]
  rw [eq_scalarDensity_smul Q α]
  rfl

theorem scalarDensity_chart_smooth (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hα : ChartSmooth α) (p : M) :
    ContDiffOn ℝ ∞ (fun y => scalarDensity Q α ((extChartAt 𝓘(ℝ, E) p).symm y))
      (extChartAt 𝓘(ℝ, E) p).target := by
  have hA := (hα p).continuousLinearMap_comp (evaluation (Module.finBasis ℝ E))
  have hV := (fundamentalTopForm_smooth Q p).continuousLinearMap_comp
    (evaluation (Module.finBasis ℝ E))
  have hd := hA.div hV (fun y hy =>
    eval_basis_ne_zero (Module.finBasis ℝ E) _ (fundamentalTopForm_chart_ne_zero Q p hy))
  exact hd.congr (fun y hy => scalarDensity_chart Q α p hy)

theorem scalarDensity_smooth (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hα : ChartSmooth α) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (scalarDensity Q α) := by
  intro x
  have hlocal := (scalarDensity_chart_smooth Q α hα x).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x).mem_nhds (mem_extChartAt_target x))
  have hcomp := hlocal.contMDiffAt.comp x (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x).mem_nhds
    (mem_extChartAt_source x)] with z hz
  simp only [Function.comp_apply, (extChartAt 𝓘(ℝ, E) x).left_inv hz]

theorem positive_ray_iff (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (x : M) :
    PositiveRay.Contains (fundamentalTopForm Q x) (α x) ↔ 0 ≤ scalarDensity Q α x :=
  contains_iff_coefficient_nonneg _ _ _ (fundamentalTopForm_ne_zero Q x)

end
end QuaternionicSymmetry.ManifoldQuaternionicVolumeCoefficient
