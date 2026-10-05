import QuaternionicSymmetry.ComplexProjectivePolynomialLocus
import QuaternionicSymmetry.ComplexProjectiveHausdorff
import QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource
import Mathlib.Topology.Maps.Proper.Basic

/-! BG-C6/C7, published locators: Greuel–Lossen–Shustin, *Introduction to
Singularities and Deformations* (Springer, 2007), §I.1.5, Remarks (A), p.74
(Remmert proper mapping); Serre, *Géométrie algébrique et géométrie analytique*,
Ann. Inst. Fourier 6 (1956), §19, Proposition 13, p.29 (Chow).
The finite homogeneous-equation formulation uses the usual homogeneous ideal
and Hilbert basis theorem. These replace the older unpublished Demailly
locators without changing the predicates. Proper-image analyticity and Chow
remain separate general literature premises; compactness supplies properness
internally. -/
namespace QuaternionicSymmetry.ProjectiveAnalyticAlgebraicSources

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open HolomorphicAnalyticSubsetFiniteSource
open scoped Manifold ContDiff
noncomputable section

/-- Remmert's proper-image theorem, specialized to a smooth finite-dimensional
complex source and the actual standard projective target. -/
def RemmertProjectiveImageTheorem : Prop :=
  ∀ {X F : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]
    (d : ℕ) (f : X → Space d),
    ContMDiff 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ) ∞ f → IsProperMap f →
    AnalyticSubsetOn (F := Fin d → ℂ) Set.univ (Set.range f)

/-- Chow's literal finite-equation conclusion for an actual projective
analytic subset. No group action or linearization is present. -/
def ChowProjectiveAnalyticTheorem : Prop :=
  ∀ (d : ℕ) (A : Set (Space d)),
    AnalyticSubsetOn (F := Fin d → ℂ) Set.univ A → HasHomogeneousEquations A

theorem compact_holomorphic_image_has_equations
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    {X F : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [CompactSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]
    (d : ℕ) (f : X → Space d)
    (hf : ContMDiff 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ) ∞ f) :
    HasHomogeneousEquations (Set.range f) :=
  hChow d (Set.range f) (hRemmert d f hf hf.continuous.isProperMap)

end
end QuaternionicSymmetry.ProjectiveAnalyticAlgebraicSources
