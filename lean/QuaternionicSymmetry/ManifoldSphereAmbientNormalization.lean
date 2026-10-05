import QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt
import Mathlib.Analysis.Normed.Module.Normalize

/-! A smooth local sphere-valued normalization of an arbitrary Euclidean
ambient family at nonzero values. The fallback at zero only makes the map
globally defined; it is never used near a unit-sphere value. -/
namespace QuaternionicSymmetry.ManifoldSphereAmbientNormalization

open ManifoldQuaternionicSphereSmoothAt
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def radialAmbient (u₀ : geometricSphere) (v : EuclideanThree) : EuclideanThree :=
  if v = 0 then u₀ else NormedSpace.normalize v

theorem radialAmbient_mem_sphere (u₀ : geometricSphere) (v : EuclideanThree) :
    radialAmbient u₀ v ∈ Metric.sphere (0 : EuclideanThree) 1 := by
  by_cases hv : v = 0
  · simpa only [radialAmbient, if_pos hv] using u₀.2
  · rw [radialAmbient, if_neg hv]
    exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hv)

def radialSphere (u₀ : geometricSphere) : EuclideanThree → geometricSphere :=
  Set.codRestrict (radialAmbient u₀) (Metric.sphere (0 : EuclideanThree) 1)
    (radialAmbient_mem_sphere u₀)

theorem radialSphere_eq_of_unit (u₀ v : geometricSphere) :
    radialSphere u₀ v = v := by
  apply Subtype.ext
  have hv : (v : EuclideanThree) ≠ 0 :=
    ne_zero_of_mem_unit_sphere v
  change radialAmbient u₀ (v : EuclideanThree) = v.1
  rw [radialAmbient, if_neg hv]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere v)

variable {F H N : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ F H}
  [ChartedSpace H N] [IsManifold I ∞ N]

theorem contMDiffAt_radialSphere
    (u₀ : geometricSphere) {f : N → EuclideanThree} {x : N}
    (hf : ContMDiffAt I 𝓘(ℝ,EuclideanThree) ∞ f x)
    (hfx : f x ≠ 0) :
    ContMDiffAt I (𝓡 2) ∞ (fun y => radialSphere u₀ (f y)) x := by
  have hnorm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => ‖f y‖) x :=
    ((contDiffAt_norm ℝ hfx).contMDiffAt).comp x hf
  have hnormInv : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun y => (‖f y‖)⁻¹) x :=
    hnorm.inv₀ (norm_ne_zero_iff.mpr hfx)
  have hnormalized : ContMDiffAt I 𝓘(ℝ,EuclideanThree) ∞
      (fun y => NormedSpace.normalize (f y)) x := by
    simpa only [NormedSpace.normalize] using hnormInv.smul hf
  have hne : ∀ᶠ y in nhds x, f y ≠ 0 :=
    hf.continuousAt.eventually_ne hfx
  have hradial : ContMDiffAt I 𝓘(ℝ,EuclideanThree) ∞
      (fun y => radialAmbient u₀ (f y)) x := by
    apply hnormalized.congr_of_eventuallyEq
    filter_upwards [hne] with y hy
    simp only [radialAmbient, if_neg hy]
  exact contMDiffAt_codRestrict_sphere hradial
    (fun y => radialAmbient_mem_sphere u₀ (f y))

end
end QuaternionicSymmetry.ManifoldSphereAmbientNormalization
