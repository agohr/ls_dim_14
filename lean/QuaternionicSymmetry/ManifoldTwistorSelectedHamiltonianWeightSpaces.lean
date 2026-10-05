import QuaternionicSymmetry.GeneralEquivariantWeightSpace
import QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology

/-! The selected actual isometry torus has a literal derivative-of-conjugation
weight space in the contact Lie algebra. Its canonical Hamiltonian image is
the weight space of the already constructed action on H⁰(L). -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianWeightSpaces

open GeneralEquivariantWeightSpace
open ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorContactAutomorphismSections
open ManifoldTwistorContactAutomorphismIsometrySections
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldQuaternionicTorusAction
open ManifoldPositiveQuaternionicKahlerGeometry
open CompactLieTorusInputs
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

/-- Actual derivative of conjugation by one selected quaternionic isometry
torus element, in the contact atlas transported from the supplied full-Aut
atlas. The underlying complex Lie-algebra tangent model is `V`. -/
def selectedAdjointOperator
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (t : Torus r) : V →ₗ[ℂ] V := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  exact (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
    (fun g : ContactAutomorphisms P.tangent P.connection A C.contact.line =>
      isometryContactLift P.tangent P.connection A C.contact.line (T.hom t) * g *
        (isometryContactLift P.tangent P.connection A C.contact.line (T.hom t))⁻¹)
    1).toLinearMap

/-- Existing genuine contact-section action, restricted to the selected
isometry torus; this is not a new independently supplied representation. -/
def selectedSectionOperator
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (t : Torus r) :
    letI := A.charts
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) →ₗ[ℂ]
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  letI := A.charts
  exact contactSectionRepresentation P.tangent P.connection A C.contact
    (isometryContactLift P.tangent P.connection A C.contact.line (T.hom t))

theorem selectedSectionOperator_eq_isometry
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (t : Torus r) :
    letI := A.charts
    selectedSectionOperator P n A C T t =
      ManifoldQuaternionicIsometryContactSectionAction.contactSectionRepresentation
        P.tangent P.connection A C.contact (T.hom t) := by
  letI := A.charts
  change (contactSectionEquiv P.tangent P.connection A C.contact
      (isometryContactLift P.tangent P.connection A C.contact.line (T.hom t))).toLinearMap =
    (ManifoldQuaternionicIsometryContactSections.contactSectionEquiv
      P.tangent P.connection A C.contact (T.hom t)).toLinearMap
  exact congrArg LinearEquiv.toLinearMap
    (contactSectionEquiv_isometry P.tangent P.connection A C.contact (T.hom t))

def selectedAdjointWeightSpace
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (μ : Fin r → ℤ) : Submodule ℂ V :=
  weightSubmodule
    (selectedAdjointOperator (V := V) P n A C hPreserve T)
    (fun t => (weightCharacter μ t : ℂ))

def selectedSectionWeightSpace
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (μ : Fin r → ℤ) :
    letI := A.charts
    Submodule ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line)) := by
  letI := A.charts
  exact weightSubmodule (selectedSectionOperator P n A C T)
    (fun t => (weightCharacter μ t : ℂ))

/-- The actual derivative-adjoint and contact-section weight spaces agree
via the source-derived canonical Hamiltonian equivalence, in the SAME
full-Aut/contact transported atlas. -/
def selectedHamiltonianWeightEquiv
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
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (μ : Fin r → ℤ) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    selectedAdjointWeightSpace (V := V) P n A C hPreserve T μ ≃ₗ[ℂ]
      selectedSectionWeightSpace P n A C T μ := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  let F := canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
    hNTU P n hn A C hPreserve hJoint
  apply weightSubmoduleEquiv
    (selectedAdjointOperator (V := V) P n A C hPreserve T)
    (selectedSectionOperator P n A C T)
    (fun t => (weightCharacter μ t : ℂ)) F
  intro t v
  change F ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
      (fun g : ContactAutomorphisms P.tangent P.connection A C.contact.line =>
        isometryContactLift P.tangent P.connection A C.contact.line (T.hom t) * g *
          (isometryContactLift P.tangent P.connection A C.contact.line (T.hom t))⁻¹)
      1) v) =
    contactSectionEquiv P.tangent P.connection A C.contact
      (isometryContactLift P.tangent P.connection A C.contact.line (T.hom t)) (F v)
  exact canonicalHamiltonianEquiv_of_fullPreserves_conjugation (V := V)
    hNTU P n hn A C hPreserve hJoint
    (isometryContactLift P.tangent P.connection A C.contact.line (T.hom t)) v

theorem selectedHamiltonianWeight_finrank_eq
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
    {r : ℕ} (T : TorusEmbedding
      (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) r)
    (μ : Fin r → ℤ) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    Module.finrank ℂ (selectedAdjointWeightSpace (V := V)
      P n A C hPreserve T μ) =
    Module.finrank ℂ (selectedSectionWeightSpace P n A C T μ) := by
  letI := A.charts
  letI := A.complexManifold
  letI := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  exact (selectedHamiltonianWeightEquiv (V := V)
    hNTU P n hn A C hPreserve hJoint T μ).finrank_eq

end
end QuaternionicSymmetry.ManifoldTwistorSelectedHamiltonianWeightSpaces
