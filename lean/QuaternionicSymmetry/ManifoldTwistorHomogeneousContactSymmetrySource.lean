import QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorLeBrunContactNondegenerate
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! A *derived general literature corollary*, not a model-specific recognition
axiom: Wolf's compact symmetric quaternionic/contact correspondence
(Theorems 5.4 and 6.1), applied to a homogeneous complex contact twistor,
followed by LeBrun's normalized twistor metric recognition (Corollary 3.4).

LeBrun, *Fano Manifolds, Contact Structures, and Quaternionic Geometry*,
printed pp. 9–10, defines contact homogeneity by transitivity of the full
contact-transformation group and describes these contact manifolds as
twistors of compact quaternionic symmetric spaces. His Corollary 3.4,
printed p. 18, identifies normalized positive metrics whose genuine twistor
spaces are biholomorphic. Twistor simple connectedness is retained as an
explicit premise because the existing Fano-to-simply-connected deduction
is not yet checked internally. Scalar rescaling is part of the general
derived corollary; this interface does not assert a carrier for any
particular Wolf space.

The proposition below is a **literature premise**, to be passed explicitly
to a final theorem. It is not established by its definition and is not a
Lean axiom. Its transitivity assumption concerns the actual contact
automorphism group of the actual twistor sphere bundle, not an abstract
homogeneous space or a named adjoint variety. -/

namespace QuaternionicSymmetry.ManifoldTwistorHomogeneousContactSymmetrySource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorContactAutomorphisms
open ManifoldRiemannianIntrinsicSymmetry
open scoped Manifold ContDiff
noncomputable section

/-- Wolf–LeBrun homogeneous-contact-to-intrinsic-symmetry corollary,
restricted to genuine compact connected positive quaternionic-Kähler
geometries of quaternionic dimension at least two. -/
def HomogeneousContactTwistorSymmetryCorollary : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (_hn : 2 ≤ n)
    (_hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A),
    SimplyConnectedSpace (SphereBundleTotal P.tangent) →
    (∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) →
    IsRiemannianSymmetric P.tangent

/-- Apply the precisely typed general correspondence to one actual
positive geometry and its genuine contact-automorphism action. -/
theorem intrinsicSymmetric_of_contactAutomorphisms_transitive
    (hSource : HomogeneousContactTwistorSymmetryCorollary)
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n)
    (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hSC : SimplyConnectedSpace (SphereBundleTotal P.tangent))
    (hTransitive : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) :
    IsRiemannianSymmetric P.tangent :=
  hSource P n hn hDim A C hSC hTransitive

end
end QuaternionicSymmetry.ManifoldTwistorHomogeneousContactSymmetrySource
