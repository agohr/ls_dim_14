import QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianFromSources
import QuaternionicSymmetry.ManifoldTwistorCanonicalHamiltonianEquivariance

/-! The canonical contact Hamiltonian equivalence in the actual contact-group
atlas transported from a *supplied* full-automorphism atlas.  In particular,
this does not select a second atlas or use the old universal NT source. -/

namespace QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources

open ManifoldTwistorUniqueContactHamiltonianFromSources
open ManifoldTwistorCanonicalHamiltonianEquivariance
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorContactAutomorphismIsometrySections
open ManifoldPositiveQuaternionicKahlerGeometry
open GeneralUniqueContactHamiltonianSource
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 200000

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The actual contact Hamiltonian equivalence in the SAME complex Lie atlas
transported from the supplied full holomorphic automorphism group. -/
def canonicalHamiltonianEquiv_of_fullPreserves_atlas
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) ≃ₗ[ℂ]
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  let hContactJoint := contact_joint_holomorphic_of_full (V := V)
    P.tangent P.connection A C.contact.line hPreserve hJoint
  let hBij := contactHamiltonian_bijective_of_fullPreserves_atlas (V := V)
    hNTU P n hn A C hPreserve hJoint
  exact canonicalHamiltonianEquiv (V := V) P.tangent P.connection A C.contact
    hContactJoint hBij

/-- Conjugation equivariance of the actual Hamiltonian equivalence in the
contact-group atlas transported from the supplied full-Aut atlas. -/
theorem canonicalHamiltonianEquiv_of_fullPreserves_conjugation
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2))
    (f : ContactAutomorphisms P.tangent P.connection A C.contact.line)
    (v : V) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
      hNTU P n hn A C hPreserve hJoint
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms P.tangent P.connection A C.contact.line =>
          f * g * f⁻¹) 1) v) =
      ManifoldTwistorContactAutomorphismSections.contactSectionEquiv
        P.tangent P.connection A C.contact f
        (canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
          hNTU P n hn A C hPreserve hJoint v) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  let hContactJoint := contact_joint_holomorphic_of_full (V := V)
    P.tangent P.connection A C.contact.line hPreserve hJoint
  let hBij := contactHamiltonian_bijective_of_fullPreserves_atlas (V := V)
    hNTU P n hn A C hPreserve hJoint
  exact canonicalHamiltonianEquiv_conjugation
    P.tangent P.connection A C.contact hContactJoint hBij f v

/-- The same supplied-atlas Hamiltonian equivalence restricts to the
actual quaternionic-isometry lift and its contact-section action. -/
theorem canonicalHamiltonianEquiv_of_fullPreserves_isometry
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2))
    (f : ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)
    (v : V) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
      hNTU P n hn A C hPreserve hJoint
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms P.tangent P.connection A C.contact.line =>
          isometryContactLift P.tangent P.connection A C.contact.line f * g *
            (isometryContactLift P.tangent P.connection A C.contact.line f)⁻¹) 1) v) =
      ManifoldQuaternionicIsometryContactSections.contactSectionEquiv
        P.tangent P.connection A C.contact f
        (canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
          hNTU P n hn A C hPreserve hJoint v) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  exact (canonicalHamiltonianEquiv_of_fullPreserves_conjugation (V := V)
    hNTU P n hn A C hPreserve hJoint
    (isometryContactLift P.tangent P.connection A C.contact.line f) v).trans
    (congrArg (fun F => F (canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
      hNTU P n hn A C hPreserve hJoint v))
      (contactSectionEquiv_isometry P.tangent P.connection A C.contact f))

end
end QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
