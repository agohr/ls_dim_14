import QuaternionicSymmetry.ManifoldTwistorContactContraction
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismIsometrySections
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! An exact actual-object interface for Nitta--Takeuchi, Theorem 1.6.

The source supplies a complex Lie atlas on the *existing* contact
automorphism group, its holomorphic joint evaluation action, and its
infinitesimal-action map to genuine holomorphic vector fields. Its Hamiltonian
theorem says that contraction by the actual contact form is bijective on the
image of that infinitesimal action. The pointwise derivative formula pins
down the source map; an arbitrary abstract vector-space equivalence would not
do so. Conjugation naturality is proved internally by the chain rule. The underlying
isometry and contact-section actions are already constructed internally.

This is a theorem-valued literature premise, not an axiom or a proof of NT.
It does not assert group complexification, algebraicity, or holomorphicity
of the separately constructed complex-torus homomorphism. -/

namespace QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianSource

open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorContactContraction
open ManifoldTwistorContactAutomorphismSections
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open HolomorphicVectorFieldPushforward
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

/-- The actual contact-group and infinitesimal-field conclusion of NT's
Theorem 1.6. Its `field` is the derivative of the genuine contact-group
point action; joint evaluation is holomorphic in the same Lie atlas. The
bijection is precisely the published contact-Hamiltonian map, expressed
using the internally constructed contraction. -/
def ContactHamiltonianConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  letI : TopologicalSpace (ContactAutomorphisms Q D B C.line) := inferInstance
  let G := ContactAutomorphisms Q D B C.line
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
      (hChart : ChartedSpace V G),
      letI : NormedSpace ℂ V := hSpace
      letI : FiniteDimensional ℂ V := hFinite
      letI : ChartedSpace V G := hChart
      ∃ hManifold : IsManifold 𝓘(ℂ,V) ∞ G,
        letI : IsManifold 𝓘(ℂ,V) ∞ G := hManifold
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ G,
          letI : LieGroup 𝓘(ℂ,V) ∞ G := hLie
          ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
            𝓘(ℂ,ComplexTwistorModel n) ∞
            (fun p : G × SphereBundleTotal Q => p.1.1 p.2) ∧
          ∃ field : GroupLieAlgebra 𝓘(ℂ,V) G →ₗ[ℂ]
              Fields (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q),
            (∀ (v : GroupLieAlgebra 𝓘(ℂ,V) G) (z : SphereBundleTotal Q),
              field v z =
                (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
                  (fun f : G => f.1 z) 1) v) ∧
            Function.Bijective ((contraction Q D B C).comp field)

/-- Nitta--Takeuchi Theorem 1.6 (JMSJ 39 (1987), p.142), combined with
the compact-contact Lie-group statement on p.140 and the general
compact-complex-automorphism transformation theorem (Kobayashi,
`Transformation Groups in Differential Geometry`, III §1, Thm 1.1).
The same compact-open topology, contact-subgroup atlas, and joint
holomorphic evaluation remain explicit source-fidelity gates before
instantiation; this contract is not silently discharged. -/
def ContactHamiltonianSource : Prop :=
  ∀ {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : ManifoldPositiveQuaternionicKahlerGeometry.CompactConnectedPositiveQuaternionicKahlerGeometry
      (E := E) (M := M))
    (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
    ∀ (B : CompatibleComplexAtlas P.tangent P.connection n)
      (C : NondegenerateHolomorphicContactData P.tangent P.connection n B),
      ContactHamiltonianConclusion P.tangent P.connection B C.contact

end
end QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianSource
