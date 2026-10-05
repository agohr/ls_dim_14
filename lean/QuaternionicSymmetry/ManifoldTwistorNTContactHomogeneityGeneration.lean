import QuaternionicSymmetry.GeneralComplexContactHomogeneousLieBridge
import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianSource
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! The actual contact-automorphism group's NT Lie atlas and jointly
holomorphic evaluation, combined with genuine point-transitivity, produce
generation of the same geometric contact quotient line. Orbit submersivity
is supplied only by the explicit source-review-pending *general* Lee
corollary; it is not part of the contact/PQK conclusion premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorNTContactHomogeneityGeneration

open GeneralComplexContactData
open GeneralComplexContactHomogeneousLieBridge
open GeneralHolomorphicTransitiveOrbitSource
open ManifoldTwistorNittaTakeuchiHamiltonianSource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCorePullback
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- Conditional only on the named general Lee orbit corollary, the
Nitta–Takeuchi contact-group data, and *actual* contact-automorphism
transitivity, the genuine twistor contact line is globally generated.
No generation, orbit submersivity, or model recognition is assumed for this
particular twistor. -/
theorem actual_contactLine_generated_of_NT_transitive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hNT : ContactHamiltonianConclusion P.tangent P.connection A C.contact)
    (hTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : T2Space
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := inferInstance
  letI : SecondCountableTopology
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := by
    change SecondCountableTopology
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line))
    infer_instance
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,field,hField,hBij⟩ := hNT
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) := hLie
  let G := C.toGeneralContactGeometry
  have hOne : ∀ z : SphereBundleTotal P.tangent,
      (fun p : ContactAutomorphisms P.tangent P.connection A C.contact.line ×
          SphereBundleTotal P.tangent => p.1.1 p.2)
        (1,z) = z := by
    intro z
    rfl
  have hMul : ∀ (g h : ContactAutomorphisms P.tangent P.connection A C.contact.line)
      (z : SphereBundleTotal P.tangent),
      ((g*h).1 : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) z =
        g.1 (h.1 z) := by
    intro g h z
    rfl
  have hGenerated := contactLine_generated_of_transitiveLieAction
    (IR := RealModel (E := E)) G hLee
    (fun p : ContactAutomorphisms P.tangent P.connection A C.contact.line ×
      SphereBundleTotal P.tangent => p.1.1 p.2)
    hJoint hOne hMul hTrans
  exact hGenerated

end
end QuaternionicSymmetry.ManifoldTwistorNTContactHomogeneityGeneration
