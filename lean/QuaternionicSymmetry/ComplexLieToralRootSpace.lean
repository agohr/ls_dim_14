import QuaternionicSymmetry.ComplexLieToralDifferentialSubalgebra
import QuaternionicSymmetry.AbelianToralRootSpace

/-! The actual smooth torus differential span is a nilpotent Lie
subalgebra. Its exact adjoint eigenspaces inject into Mathlib's
generalized root spaces, without asserting equality. -/

namespace QuaternionicSymmetry.ComplexLieToralRootSpace

open ComplexLieToralDifferentialSubalgebra
open AbelianToralRootSpace
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

variable {V K : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℂ,V) ∞ K] [LieGroup 𝓘(ℂ,V) ∞ K]
  {r d : ℕ}
  (ρ : Torus r →* K)
  (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
  (hManifold : letI := hChart
    IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
  (hLie : letI := hChart
    LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
  (hSmooth : letI := hChart
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞ ρ)

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem toralLie_isNilpotent :
    LieRing.IsNilpotent (toralLieSubalgebra ρ hChart hManifold hLie hSmooth) :=
  H_isNilpotent (differentialGenerators ρ hChart)
    (fun x hx y hy => differentialGenerators_bracket_zero
      ρ hChart hManifold hLie hSmooth hx hy)

theorem exactWeightSpace_le_rootSpace
    (χ : toralLieSubalgebra ρ hChart hManifold hLie hSmooth → ℂ) :
    letI := toralLie_isNilpotent ρ hChart hManifold hLie hSmooth
    LieModule.weightSpace (GroupLieAlgebra 𝓘(ℂ,V) K) χ ≤
      LieAlgebra.rootSpace
        (toralLieSubalgebra ρ hChart hManifold hLie hSmooth) χ := by
  exact AbelianToralRootSpace.exactWeightSpace_le_rootSpace
    (differentialGenerators ρ hChart)
    (fun x hx y hy => differentialGenerators_bracket_zero
      ρ hChart hManifold hLie hSmooth hx hy) χ

end
end QuaternionicSymmetry.ComplexLieToralRootSpace
