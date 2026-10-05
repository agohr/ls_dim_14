import QuaternionicSymmetry.GeneralContactFanoPicardUniquenessSource
import QuaternionicSymmetry.ManifoldTwistorBKKAnalyticPicardApplication
import QuaternionicSymmetry.ManifoldTwistorUniqueContactFullEquiv

/-!
# Analytic Picard generation forces preservation on the same twistor

This is the actual-object adapter for the separately passed, reviewed
universal derived BKK uniqueness implication T2-U. The first premise concerns
every analytic locally-free rank-one sheaf class, using the already proved
equivalence with represented holomorphic line cores. The conclusion refers
to all actual biholomorphisms of the same selected twistor and the literal
contact-kernel distribution of its selected contact form.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication

open GeneralContactFanoPicardUniquenessSource
open GeneralContactFanoPicardHomogeneitySource
open GeneralComplexContactData
open ManifoldTwistorBKKPicardHomogeneityApplication
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open HolomorphicLineCoreSheafPicardGenerator
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- A generator in the full analytic sheaf Picard group yields literal
contact-distribution preservation by every biholomorphism of the same
twistor, conditional only on the explicit general uniqueness source and
the already selected actual ample contact data. -/
theorem fullPreservesContact_of_analyticPicard_generator
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple :
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic :
      letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun r : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ r)) :
    FullPreservesContact P.tangent P.connection A C.contact.line := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : ConnectedSpace M := {
    toPreconnectedSpace := inferInstance
    toNonempty := inferInstance }
  letI := A.charts
  letI := A.complexManifold
  let G := C.toGeneralContactGeometry
  have hKernel := actual_contact_kernel P.tangent P.connection A C
  have hAmpleG : AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
      (ContactGeometry.lineCore (RealModel (E := E)) G) := by
    exact hAmple
  have hCore : Function.Bijective (fun r : ℤ =>
      (contactClass P.tangent P.connection C.contact.line) ^ r) :=
    (core_zpow_bijective_iff_analyticPicard
      (B := SphereBundleTotal P.tangent)
      𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line)).mpr hPic
  exact hUnique (RealModel (E := E)) n hn G
    (contactDistribution P.tangent P.connection A C.contact.line)
    hKernel hAmpleG hCore

end
end QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication
