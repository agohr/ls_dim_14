import QuaternionicSymmetry.GeneralContactFanoPicardHomogeneitySource
import QuaternionicSymmetry.GeneralHolomorphicDistributionUniqueFull
import QuaternionicSymmetry.HolomorphicFamilyInfinitesimalLinear
import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphismLieSource
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Reviewed derived general companion for the Picard-unique route.
Kobayashi III §1 Thm 1.1 identifies the Lie algebra of the
full automorphism transformation group with global holomorphic vector
fields on a compact complex manifold. When every biholomorphism preserves
the actual contact kernel, the complete real flows of global holomorphic
fields preserve it; hence the infinitesimal fields are contact fields.
Nitta--Takeuchi Thm 1.6 (JMSJ 39, p. 142) identifies contact fields with
holomorphic contact-line sections by contraction. Lee, *Introduction to
Smooth Manifolds*, 2nd ed., Problem 20-11(b,c), printed pp. 537–538,
provides continuous-homomorphism smoothness and uniqueness of a smooth Lie
structure on this fixed compact-open group. Therefore the derivative field
identification transfers to any supplied compatible complex Lie atlas with
holomorphic joint evaluation. This is a **derived general input**, not a
literal statement of any one cited theorem. It asserts only that the
canonical composition is bijective: the orbit-derivative field map is
constructed below, not supplied as arbitrary literature data. No
quaternionic, rank, or classification condition occurs here. -/

namespace QuaternionicSymmetry.GeneralUniqueContactHamiltonianSource

open GeneralComplexContactData
open GeneralContactFanoPicardHomogeneitySource
open GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicDistributionUniqueFull
open HolomorphicFamilyInfinitesimalLinear
open ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 200000

variable {R H Z V : Type}
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The checked genuine holomorphic vector field obtained by
differentiating the actual full-biholomorphism evaluation at the identity. -/
def fullInfinitesimalActionLinear
    [ChartedSpace V (letI := C.charts; letI := C.complexManifold
      HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    [IsManifold 𝓘(ℂ,V) ∞ (letI := C.charts; letI := C.complexManifold
      HolomorphicAutomorphisms (ComplexTwistorModel n) Z)]
    (hJoint :
      letI := C.charts
      letI := C.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : HolomorphicAutomorphisms (ComplexTwistorModel n) Z × Z =>
          p.1.1 p.2)) :
    letI := C.charts
    letI := C.complexManifold
    GroupLieAlgebra 𝓘(ℂ,V)
      (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) →ₗ[ℂ]
      C.HolomorphicTangentSections := by
  letI := C.charts
  letI := C.complexManifold
  exact infinitesimalActionLinear
    (fun p : HolomorphicAutomorphisms (ComplexTwistorModel n) Z × Z => p.1.1 p.2)
    1 hJoint (by intro z; rfl)

/-- Reviewed derived general literature consequence. The full Aut Lie
atlas/action must already be supplied in one compatible structure (e.g.
by the independently reviewed Kobayashi transformation-group input).
The only asserted conclusion is bijectivity of the canonical, internally
constructed derivative-and-contraction function. -/
def UniqueContactHamiltonianBijection : Prop :=
  ∀ {R H Z V : Type}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
    [CompactSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [ConnectedSpace Z]
    (n : ℕ) (_hn : 1 ≤ n)
    (C : ContactGeometry (IR := IR) (Z := Z) n)
    (D : Z → Submodule ℂ (ComplexTwistorModel n)),
    GeneralContactFanoPicardHomogeneitySource.ContactGeometry.IsComplexContactKernel IR C D →
    letI := C.charts
    letI := C.complexManifold
    AllAutomorphismsPreserve D →
    ∀ [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      letI := C.charts
      letI := C.complexManifold
      ∀ (hChart : ChartedSpace V
          (HolomorphicAutomorphisms (ComplexTwistorModel n) Z)),
        letI : ChartedSpace V
          (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) := hChart
        ∀ (hManifold : IsManifold 𝓘(ℂ,V) ∞
            (HolomorphicAutomorphisms (ComplexTwistorModel n) Z)),
          letI : IsManifold 𝓘(ℂ,V) ∞
            (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) := hManifold
          ∀ (hLie : LieGroup 𝓘(ℂ,V) ∞
              (HolomorphicAutomorphisms (ComplexTwistorModel n) Z)),
            letI : LieGroup 𝓘(ℂ,V) ∞
              (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) := hLie
            ∀ hJoint : ContMDiff
                (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
                𝓘(ℂ,ComplexTwistorModel n) ∞
                (fun p : HolomorphicAutomorphisms
                    (ComplexTwistorModel n) Z × Z => p.1.1 p.2),
              Function.Bijective (fun v : GroupLieAlgebra 𝓘(ℂ,V)
                  (HolomorphicAutomorphisms (ComplexTwistorModel n) Z) =>
                C.sectionOfTangent (fullInfinitesimalActionLinear
                  (V := V) C hJoint v))

end
end QuaternionicSymmetry.GeneralUniqueContactHamiltonianSource
