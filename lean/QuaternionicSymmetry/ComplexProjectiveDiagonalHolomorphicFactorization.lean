import QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphic
import QuaternionicSymmetry.ComplexProjectiveRealManifold
import QuaternionicSymmetry.ComplexRealDerivativeComparison
import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization

/-! An embedded holomorphic immersion into literal projective space detects
holomorphicity of a point action equivariant for the diagonal maps. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphicFactorization

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalHolomorphic
open ComplexRealDerivativeComparison
open ManifoldComplexHolomorphicFactorization
open GeneralSmoothMapSource TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [ChartedSpace E X]
  [IsManifold 𝓘(ℂ,E) ∞ X] [IsManifold 𝓘(ℝ,E) ∞ X]
  {r d : ℕ} [T2Space (Space d)] [SecondCountableTopology (Space d)]

theorem fixed_action_holomorphic
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (μ : Fin (d + 1) → Fin r → ℤ)
    (ι : X → Space d)
    (hEmb : Topology.IsEmbedding ι)
    (hι : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ, Fin d → ℂ) ∞ ι)
    (hImm : ∀ x : X, Function.Injective
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ, Fin d → ℂ) ι x))
    (ρ : ComplexTorus r →* Equiv.Perm X)
    (hEq : ∀ z : ComplexTorus r, ∀ x : X,
      ι (ρ z x) = projectiveAction μ z (ι x))
    (z : ComplexTorus r) :
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ (ρ z) := by
  have hιR : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ, Fin d → ℂ) ∞ ι :=
    holomorphic_is_real_smooth hι
  have hImmR : ∀ x : X, Function.Injective
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ, Fin d → ℂ) ι x) :=
    real_mfderiv_injective_of_complex hι hιR hImm
  have hcomp : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ, Fin d → ℂ) ∞
      (ι ∘ (ρ z)) := by
    apply ((contMDiff_projectiveAction μ z).comp hι).congr
    intro x
    exact hEq z x
  exact holomorphic_of_embedded_holomorphic_composite
    hLee ι (ρ z) hEmb hι hImmR hcomp

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphicFactorization
