import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! The genuine real derivative of an integral compact-torus character,
viewed in the scalar model ℂ rather than an opaque tangent-space target. -/

namespace QuaternionicSymmetry.TorusWeightCharacterDifferentialLinear

open ManifoldQuaternionicTorusAction
open scoped Manifold
noncomputable section

def weightCharacterDifferentialLinear {r d : ℕ}
    (μ : Fin r → ℤ)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r)) :
    (Fin d → ℝ) →ₗ[ℝ] ℂ := by
  letI := hChart
  change (Fin d → ℝ) →ₗ[ℝ]
    TangentSpace 𝓘(ℝ,ℂ) ((weightCharacter μ (1 : Torus r) : Circle) : ℂ)
  exact (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
    (fun t : Torus r => (weightCharacter μ t : ℂ)) 1).toLinearMap

@[simp] theorem weightCharacterDifferentialLinear_apply {r d : ℕ}
    (μ : Fin r → ℤ)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (w : Fin d → ℝ) :
    weightCharacterDifferentialLinear μ hChart w =
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 w : ℂ) := rfl

end
end QuaternionicSymmetry.TorusWeightCharacterDifferentialLinear
