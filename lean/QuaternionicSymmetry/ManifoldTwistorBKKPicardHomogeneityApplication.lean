import QuaternionicSymmetry.GeneralContactFanoPicardHomogeneitySource
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-!
# Source-relative contact-Fano dichotomy on the actual twistor

This file *applies* the explicitly passed, reviewed derived analytic
corollary. It proves the contact-kernel identification internally and keeps
both alternatives on the same genuine sphere bundle: bijective integral
powers of its represented contact-line class, or transitivity of its actual
biholomorphic contact automorphisms. It neither asserts BKK's algebraic
statement directly nor supplies the literature corollary as an axiom.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPicardHomogeneityApplication

open GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The complex distribution used by the genuine contact-automorphism group
is exactly the kernel of the actual LeBrun quotient contact form, after the
complex-to-real tangent comparison in the selected compatible atlas. -/
theorem actual_contact_kernel
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (A : CompatibleComplexAtlas Q D n)
    (C : NondegenerateHolomorphicContactData Q D n A) :
    ContactGeometry.IsComplexContactKernel (RealModel (E := E))
      C.toGeneralContactGeometry
      (contactDistribution Q D A C.contact.line) := by
  intro z v
  rfl

/-- The exact actual-twistor specialization of the reviewed derived
contact-Fano dichotomy T2-A. The literature premise remains visible. -/
theorem contactClass_generator_or_contactAut_transitive
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple :
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)) :
    letI := A.charts
    letI := A.complexManifold
    Function.Bijective (fun r : ℤ =>
      (contactClass P.tangent P.connection C.contact.line) ^ r) ∨
    (∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) := by
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
  have h := hBKK (RealModel (E := E)) n hn G
    (contactDistribution P.tangent P.connection A C.contact.line)
    hKernel hAmpleG
  exact h

end
end QuaternionicSymmetry.ManifoldTwistorBKKPicardHomogeneityApplication
