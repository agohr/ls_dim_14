import QuaternionicSymmetry.ManifoldTwistorSphereTangentSmooth
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! A smooth radial retraction from nonzero ambient Euclidean three-space
onto the genuine twistor coefficient sphere. This gives a smooth local
inverse source for the sphere tangent inclusion. -/

namespace QuaternionicSymmetry.ManifoldTwistorRadialRetraction
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

/-- Ambient three-space with the origin removed. -/
def nonzeroOpen : TopologicalSpace.Opens EuclideanThree :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
instance nonzeroNonempty : Nonempty nonzeroOpen :=
  ⟨⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp [nonzeroOpen]⟩⟩
instance nonzeroChartedSpace : ChartedSpace EuclideanThree nonzeroOpen :=
  nonzeroOpen.isOpenEmbedding'.singletonChartedSpace
instance nonzeroIsManifold : IsManifold 𝓘(ℝ,EuclideanThree) ∞ nonzeroOpen :=
  nonzeroOpen.isOpenEmbedding'.isManifold_singleton

private theorem norm_smooth :
    ContMDiff 𝓘(ℝ,EuclideanThree) 𝓘(ℝ) ∞
      (fun x : nonzeroOpen => ‖(x : EuclideanThree)‖) := by
  have hnorm : ContDiffOn ℝ ∞ (fun x : EuclideanThree => ‖x‖) nonzeroOpen := by
    intro x hx
    exact (contDiffAt_norm ℝ (by simpa using hx)).contDiffWithinAt
  exact hnorm.contMDiffOn.comp_contMDiff
    (contMDiff_isOpenEmbedding nonzeroOpen.isOpenEmbedding'
      (I := 𝓘(ℝ,EuclideanThree)) (n := ∞)) (by
      intro x
      exact x.2)

private theorem normalized_smooth :
    ContMDiff 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree) ∞
      (fun x : nonzeroOpen => (‖(x : EuclideanThree)‖)⁻¹ • (x : EuclideanThree)) := by
  have h0 : ∀ x : nonzeroOpen, ‖(x : EuclideanThree)‖ ≠ 0 := by
    intro x
    exact norm_ne_zero_iff.mpr x.2
  exact (norm_smooth.inv₀ h0).smul
    (contMDiff_isOpenEmbedding nonzeroOpen.isOpenEmbedding'
      (I := 𝓘(ℝ,EuclideanThree)) (n := ∞))

private theorem normalized_unit (x : nonzeroOpen) :
    (‖(x : EuclideanThree)‖)⁻¹ • (x : EuclideanThree) ∈
      Metric.sphere (0 : EuclideanThree) 1 := by
  have hn : ‖(x : EuclideanThree)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [norm_smul, hn]

/-- Smooth radial projection from the punctured ambient space to the
unit twistor coefficient sphere. -/
def radial : nonzeroOpen → geometricSphere :=
  Set.codRestrict
    (fun x : nonzeroOpen => (‖(x : EuclideanThree)‖)⁻¹ • (x : EuclideanThree))
    (Metric.sphere (0 : EuclideanThree) 1) normalized_unit

theorem radial_smooth :
    ContMDiff 𝓘(ℝ,EuclideanThree) (𝓡 2) ∞ radial :=
  normalized_smooth.codRestrict_sphere normalized_unit

/-- The unit sphere includes into the nonzero ambient space. -/
def sphereIntoNonzero (a : geometricSphere) : nonzeroOpen :=
  ⟨a.1, ne_zero_of_mem_unit_sphere a⟩

theorem sphereIntoNonzero_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ,EuclideanThree) ∞ sphereIntoNonzero := by
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ,EuclideanThree) ∞
      ((↑) : geometricSphere → EuclideanThree) := contMDiff_coe_sphere
  have hcoe' : ContMDiff (𝓡 2) 𝓘(ℝ,EuclideanThree) ∞
      (Subtype.val ∘ sphereIntoNonzero) := by
    simpa only [Function.comp_def] using hcoe
  exact ContMDiff.of_comp_isOpenEmbedding nonzeroOpen.isOpenEmbedding' hcoe'

theorem radial_sphereIntoNonzero (a : geometricSphere) :
    radial (sphereIntoNonzero a) = a := by
  apply Subtype.ext
  change (‖(a : EuclideanThree)‖)⁻¹ • (a : EuclideanThree) = a
  have hn : ‖(a : EuclideanThree)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using a.2
  simp [hn]

end
end QuaternionicSymmetry.ManifoldTwistorRadialRetraction
