import QuaternionicSymmetry.ComplexProjectiveDiagonalJointHolomorphic
import QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphicFactorization
import QuaternionicSymmetry.ComplexTorusRealManifold

/-! Joint holomorphicity descends from diagonal projective equivariance
through a genuinely embedded holomorphic immersion. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalJointFactorization

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalJointHolomorphic
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

theorem joint_action_holomorphic
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (μ : Fin (d + 1) → Fin r → ℤ)
    (ι : X → Space d)
    (hEmb : Topology.IsEmbedding ι)
    (hι : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ, Fin d → ℂ) ∞ ι)
    (hImm : ∀ x : X, Function.Injective
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ, Fin d → ℂ) ι x))
    (ρ : ComplexTorus r →* Equiv.Perm X)
    (hEq : ∀ z : ComplexTorus r, ∀ x : X,
      ι (ρ z x) = projectiveAction μ z (ι x)) :
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ,E)) 𝓘(ℂ,E) ∞
      (fun q : ComplexTorus r × X => ρ q.1 q.2) := by
  letI : SecondCountableTopology (ComplexTorus r) :=
    (ComplexTorusHolomorphicStructure.torusVal_isOpenEmbedding r).isEmbedding.secondCountableTopology
  letI : ChartedSpace ((Fin r → ℂ) × E) (ComplexTorus r × X) :=
    prodChartedSpace (Fin r → ℂ) (ComplexTorus r) E X
  letI : IsManifold 𝓘(ℂ, (Fin r → ℂ) × E) ∞
      (ComplexTorus r × X) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (ComplexTorus r) X
  letI : IsManifold 𝓘(ℝ, (Fin r → ℂ) × E) ∞
      (ComplexTorus r × X) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (ComplexTorus r) X
  have hιR : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ, Fin d → ℂ) ∞ ι :=
    holomorphic_is_real_smooth hι
  have hImmR : ∀ x : X, Function.Injective
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ, Fin d → ℂ) ι x) :=
    real_mfderiv_injective_of_complex hι hιR hImm
  have hprod : ContMDiff
      (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ,E))
      (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, Fin d → ℂ)) ∞
      (Prod.map id ι) :=
    (contMDiff_id : ContMDiff 𝓘(ℂ, Fin r → ℂ)
      𝓘(ℂ, Fin r → ℂ) ∞
      (id : ComplexTorus r → ComplexTorus r)).prodMap hι
  have hcomp : ContMDiff 𝓘(ℂ, (Fin r → ℂ) × E)
      𝓘(ℂ, Fin d → ℂ) ∞
      (ι ∘ fun q : ComplexTorus r × X => ρ q.1 q.2) := by
    have h := (jointAction_contMDiff μ).comp hprod
    rw [modelWithCornersSelf_prod]
    apply h.congr
    intro q
    exact hEq q.1 q.2
  have hfinal := holomorphic_of_embedded_holomorphic_composite
    hLee ι (fun q : ComplexTorus r × X => ρ q.1 q.2)
    hEmb hι hImmR hcomp
  rwa [modelWithCornersSelf_prod] at hfinal

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalJointFactorization
