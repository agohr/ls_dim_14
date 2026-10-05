import QuaternionicSymmetry.ContinuousLieHomSmooth
import QuaternionicSymmetry.QuaternionicTorusWeightKernel
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Actual integral compact-torus characters are real smooth in ANY
selected finite-dimensional real Lie atlas on the standard torus. This
uses only the already registered general continuous-hom smoothness chain. -/

namespace QuaternionicSymmetry.SelectedIntegralCharacterSmooth

open ManifoldQuaternionicTorusAction
open QuaternionicTorusWeightKernel ContinuousLieHomSmooth
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

theorem weightCharacter_contMDiff
    {r d : ℕ} (μ : Fin r → ℤ)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hManifold : letI := hChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hLie : letI := hChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := hChart
    ContMDiff 𝓘(ℝ,Fin d → ℝ) (𝓡 1) ∞ (weightCharacter μ) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hManifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hLie
  exact continuous_hom_smooth (weightCharacter μ)
    hClosed hImm hLee (continuous_weightCharacter μ)

theorem weightCharacter_complex_contMDiff
    {r d : ℕ} (μ : Fin r → ℤ)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hManifold : letI := hChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hLie : letI := hChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := hChart
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ) ∞
      (fun t : Torus r => (weightCharacter μ t : ℂ)) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
    ⟨by norm_num [Complex.finrank_real_complex]⟩
  exact (contMDiff_coe_sphere (m := ∞) (n := 1)).comp
    (weightCharacter_contMDiff μ hChart hManifold hLie hClosed hImm hLee)

end
end QuaternionicSymmetry.SelectedIntegralCharacterSmooth
