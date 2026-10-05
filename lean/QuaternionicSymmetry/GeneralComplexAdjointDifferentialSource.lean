import QuaternionicSymmetry.ComplexLieRealCompanion
import QuaternionicSymmetry.ComplexGroupLieBracketRestriction

/-!
# Derived complex-atlas target for Lee's real adjoint derivative

Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 20.24
and Theorem 20.27, printed pp. 534--535 (PDF pp. 551--552), defines
`Ad_g = d(h ↦ g*h*g⁻¹)_1` and gives `d(Ad)_1(u)v = [u,v]` with the
left-invariant Lie bracket. Here the complex Lie atlas is also used as its
canonical real-smooth companion; no independent real atlas or model-specific
torus/root conclusion is supplied. The predicate below is a *derived target*,
proved from the separately registered real BG-L9 source in
`GeneralComplexAdjointFromReal`; it is not a second external source. -/

namespace QuaternionicSymmetry.GeneralComplexAdjointDifferentialSource

open ComplexLieRealCompanion
open scoped Manifold ContDiff
noncomputable section

/-- The literal adjoint-orbit map in a selected complex Lie atlas. -/
def adjointOrbit {V G : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [Group G] [TopologicalSpace G] [ChartedSpace V G]
    [IsManifold 𝓘(ℂ,V) ∞ G] [LieGroup 𝓘(ℂ,V) ∞ G]
    (v : GroupLieAlgebra 𝓘(ℂ,V) G) (g : G) : V :=
  (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (fun h : G => g * h * g⁻¹) 1) v

/-- The general adjoint-differential target, realified in the
*same* complex charts. The first clause records the differentiability
needed for an internal torus-chain calculation; the second is Lee's exact
positive-sign left-invariant bracket identity. -/
def LeeComplexAdjointDifferentialSource : Prop :=
  ∀ {V G : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G]
    [LieGroup 𝓘(ℂ,V) ∞ G],
    letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
    letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
    letI : ENat.LEInfty (minSmoothness ℂ 3) := by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
    ∀ (v : GroupLieAlgebra 𝓘(ℂ,V) G),
      MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbit v) 1 ∧
      ∀ (u : GroupLieAlgebra 𝓘(ℂ,V) G),
        mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbit v) 1 u = ⁅u,v⁆

end
end QuaternionicSymmetry.GeneralComplexAdjointDifferentialSource
