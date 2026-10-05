import QuaternionicSymmetry.SmoothLieFactorOpenImage
import QuaternionicSymmetry.ComplexTorusOpenImageComponent
import QuaternionicSymmetry.ComplexTorusHolomorphicStructure
import QuaternionicSymmetry.ComplexLieRealCompanion

/-! The exact centralizer identity-component criterion for a genuine
complex-torus action. The target may be disconnected; the conclusion does
not falsely identify the image with every centralizer component. -/

namespace QuaternionicSymmetry.ComplexTorusCentralizerImageCriterion

open QuaternionicSymmetry.SmoothLieFactorOpenImage
open QuaternionicSymmetry.ComplexTorusOpenImageComponent
open IdentityComponentLie TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {F V H K : Type*} {r : ℕ}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [ChartedSpace F H] [IsManifold 𝓘(ℝ,F) ∞ H]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℝ,V) ∞ K]

local instance : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) :=
  ComplexLieRealCompanion.realManifold

theorem range_eq_component_of_exact_tangent
    (f : ComplexTorus r →* H) (i : H →* K)
    (hf : ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,F) ∞ f)
    (hfc : Continuous f)
    (hi : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ i)
    (hdi : Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1))
    (S : Submodule ℝ V)
    (hComposite : LinearMap.range
      ((mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,V) (i.comp f) 1).toLinearMap) = S)
    (hUpper : LinearMap.range
      ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) i 1).toLinearMap) ≤ S) :
    f.range = Component H := by
  letI : CompleteSpace (Fin r → ℂ) := FiniteDimensional.complete ℝ _
  have hOpen := isOpen_range_of_composite_range_exact f i hf hi hdi
    S hComposite hUpper
  exact range_eq_component f hfc hOpen

end
end QuaternionicSymmetry.ComplexTorusCentralizerImageCriterion
