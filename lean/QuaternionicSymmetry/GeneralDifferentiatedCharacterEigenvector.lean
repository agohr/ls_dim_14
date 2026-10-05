import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The elementary derivative bridge for a genuine family of eigenvectors:
differentiate the *same* character equality, with no Lie-root assumption.
The separate identification of the derivative of group conjugation with
the Lie bracket is not included here. -/

namespace QuaternionicSymmetry.GeneralDifferentiatedCharacterEigenvector

open scoped Manifold ContDiff
noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_eigenvector_of_character
    (ρ : E → V →ₗ[ℂ] V) (χ : E → ℂ) (v : V) (x : E)
    (hEig : ∀ y, ρ y v = χ y • v)
    (hχ : DifferentiableAt ℝ χ x) (w : E) :
    fderiv ℝ (fun y => ρ y v) x w = (fderiv ℝ χ x w) • v := by
  have hfun : (fun y => ρ y v) = (fun y => χ y • v) := funext hEig
  rw [hfun, fderiv_smul_const hχ]
  rfl

variable {G : Type*} [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G]

/-- Fixed-vector scalar multiplication between the genuine opaque tangent
models of the scalar line and the vector-space target. -/
def tangentScalarSmul (c : ℂ) (v : V) :
    TangentSpace 𝓘(ℝ,ℂ) c →L[ℝ] TangentSpace 𝓘(ℝ,V) (c • v) := by
  change ℂ →L[ℝ] V
  exact (1 : ℂ →L[ℝ] ℂ).smulRight v

/-- The same derivative identity for a genuine real manifold parameter,
such as the selected compact torus in its Lie atlas. -/
theorem mfderiv_eigenvector_of_character
    (ρ : G → V →ₗ[ℂ] V) (χ : G → ℂ) (v : V) (x : G)
    (hEig : ∀ y, ρ y v = χ y • v)
    (hχ : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℂ) χ x)
    (w : TangentSpace 𝓘(ℝ,E) x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (fun y => ρ y v) x w =
      tangentScalarSmul (χ x) v (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℂ) χ x w) := by
  let L : ℂ →L[ℝ] V := (1 : ℂ →L[ℝ] ℂ).smulRight v
  have hL (c : ℂ) : L c = c • v := rfl
  have hfun : (fun y => ρ y v) = L ∘ χ := by
    funext y
    exact (hEig y).trans (hL (χ y)).symm
  rw [hfun, mfderiv_comp x L.mdifferentiableAt hχ]
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

end
end QuaternionicSymmetry.GeneralDifferentiatedCharacterEigenvector
