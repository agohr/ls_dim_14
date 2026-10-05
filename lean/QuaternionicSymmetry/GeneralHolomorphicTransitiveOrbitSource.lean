import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Analysis.Complex.Basic

/-!
# Derived general transitive-orbit submersion source

John M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem
7.25 (printed p. 165; PDF p. 182) proves that a smooth equivariant map
from a transitive smooth Lie-group manifold has constant rank and, when
surjective, is a submersion. The proof of Proposition 7.26 (printed p. 166;
PDF p. 183) explicitly applies this to the orbit map, equivariant under
left translation. The complex statement below is the finite-dimensional
holomorphic specialization: regard complex manifolds as real, apply Lee,
then identify surjectivity of the real derivative with the complex-linear
derivative. This derivation and the actual type were reviewed against the
cited text on 28 September 2026 (registry BG-L7). Realification is part of
the disclosed derived literature input, not an internal Lean proof of Lee.
It is an explicit general premise, not an axiom or a theorem asserted for
a particular twistor. It supplies no contact-group atlas or transitivity.

Second countability of the acting Lie group is essential: an uncountable
discrete group can otherwise act transitively by translations on a
positive-dimensional manifold while its orbit map has zero derivative.
-/

namespace QuaternionicSymmetry.GeneralHolomorphicTransitiveOrbitSource

open scoped Manifold ContDiff

/-- Narrow general complex version of Lee's equivariant rank theorem for
an actual jointly holomorphic transitive Lie action. It concludes only the
submersivity of the genuine orbit map at the group identity. -/
def LeeHolomorphicTransitiveOrbitSubmersion : Prop :=
  ∀ {V G W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace V G]
    [IsManifold 𝓘(ℂ,V) ∞ G] [Group G] [LieGroup 𝓘(ℂ,V) ∞ G]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [TopologicalSpace Z] [T2Space Z]
    [SecondCountableTopology Z] [ChartedSpace W Z]
    [IsManifold 𝓘(ℂ,W) ∞ Z]
    (a : G × Z → Z),
    ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,W)) 𝓘(ℂ,W) ∞ a →
    (∀ z : Z, a (1,z) = z) →
    (∀ (g h : G) (z : Z), a (g*h,z) = a (g,a (h,z))) →
    (∀ z w : Z, ∃ g : G, a (g,z) = w) →
    ∀ z : Z,
      Function.Surjective
        (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) (fun g : G => a (g,z)) 1)

end QuaternionicSymmetry.GeneralHolomorphicTransitiveOrbitSource
