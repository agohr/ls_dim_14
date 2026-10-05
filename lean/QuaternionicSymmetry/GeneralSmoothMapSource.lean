import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
General source interfaces for Lee, *Introduction to Smooth Manifolds*,
second edition, Theorem 4.29 (p.90) and the injective case of Theorem 7.25
(p.165), together with Corollary 5.30 (p.113). These are explicit
literature premises, not axioms. All spaces
are actual finite-dimensional, Hausdorff, second-countable real manifolds
without boundary. No quotient, orbit, metric, or model identification is
provided by either interface.
-/

namespace QuaternionicSymmetry.GeneralSmoothMapSource

open Manifold
open scoped Manifold ContDiff
noncomputable section

/-- BG-D2: smoothness descends through an actual surjective smooth map
whose genuine differential is surjective everywhere (Lee 4.29). -/
def LeeSurjectiveSubmersionDescentTheorem : Prop :=
  ∀ {E F V M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [TopologicalSpace P] [T2Space P] [SecondCountableTopology P]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
    [ChartedSpace V P] [IsManifold 𝓘(ℝ,V) ∞ P]
    (π : M → N) (f : N → P),
    Function.Surjective π →
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ π →
    (∀ x, Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) π x)) →
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (f ∘ π) →
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ f

/-- BG-D3: smoothness into an embedded submanifold is detected by its
ambient inclusion (Lee 5.30). The smooth embedding is expressed by its
actual topology and injective differential, not an abstract subset label. -/
def LeeEmbeddedCodomainRestrictionTheorem : Prop :=
  ∀ {E F V M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [TopologicalSpace P] [T2Space P] [SecondCountableTopology P]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
    [ChartedSpace V P] [IsManifold 𝓘(ℝ,V) ∞ P]
    (ι : N → P) (f : M → N),
    Topology.IsEmbedding ι →
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ ι →
    (∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι x)) →
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (ι ∘ f) →
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f

/-- A genuine smooth left action, with its group laws and joint smoothness
on the specified manifolds. This contains no transitivity conclusion. -/
structure SmoothLeftAction
    (E F G M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [TopologicalSpace M] [ChartedSpace F M] where
  act : G → M → M
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ g h x, act (g * h) x = act g (act h x)
  smooth : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) ∞
    (fun p : G × M => act p.1 p.2)

/-- BG-L6: the injective case of Lee's equivariant rank theorem (7.25).
Both smooth actions, source transitivity, and actual equivariance must
be supplied. The conclusion concerns the genuine manifold derivative. -/
def LeeEquivariantImmersionTheorem : Prop :=
  ∀ {E F V G M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [ChartedSpace F M] [IsManifold 𝓘(ℝ,F) ∞ M]
    [ChartedSpace V N] [IsManifold 𝓘(ℝ,V) ∞ N]
    (a : SmoothLeftAction E F G M) (b : SmoothLeftAction E V G N)
    (f : M → N),
    (∀ x y : M, ∃ g : G, a.act g x = y) →
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ f →
    (∀ g x, f (a.act g x) = b.act g (f x)) →
    Function.Injective f →
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f x)

end
end QuaternionicSymmetry.GeneralSmoothMapSource
