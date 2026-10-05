import QuaternionicSymmetry.ManifoldQuaternionicFundamentalSymmetry

/-! BG-R1: Petersen, Riemannian Geometry, Proposition 5.6.2, printed
p. 164 in the author-hosted third-edition manuscript. On a connected
domain, Riemannian isometries are determined by their value and differential
at one point. The interface is restricted here to the actual tangent metrics
constructed by this project. `ManifoldRiemannianOneJetFromFixedComponents`
derives it from the retained general fixed-component source and mathlib's
inverse function theorem, removing it as an independent premise. It makes no claim
about quaternionic fixed components or their dimension. -/

namespace QuaternionicSymmetry.ManifoldRiemannianOneJetInput

open ManifoldQuaternionicFundamentalSymmetry
open scoped Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The cited uniqueness theorem, with the actual manifold differential.
Tangent fibers in this model are definitionally copies of `E`; the
value equality ensures the two target fibers are the same geometric fiber. -/
def RiemannianOneJetRigidityOnModel : Prop :=
  ∀ [FiniteDimensional ℝ E] [Nontrivial E] [IsManifold 𝓘(ℝ,E) ∞ M]
    [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M],
    ∀ (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞),
    PreservesMetric Q f → PreservesMetric Q g →
    ∀ x : M, f x = g x →
      (∀ v : TangentSpace 𝓘(ℝ,E) x,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) x v) → f = g

end QuaternionicSymmetry.ManifoldRiemannianOneJetInput
