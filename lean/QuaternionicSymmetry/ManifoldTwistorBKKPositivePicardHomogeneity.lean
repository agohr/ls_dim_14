import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
import QuaternionicSymmetry.ManifoldTwistorBKKAnalyticPicardApplication

/-!
# Normalized positive twistor: analytic Picard or contact homogeneity

This assembles the already established actual T1/contact-canonical/Kodaira
ampleness construction with the explicitly *passed*, reviewed derived
universal derived BKK analytic corollary. There is no supplied complex atlas,
contact form, or ampleness premise. Both alternatives refer to the same
selected genuine twistor and its actual contact quotient line/distribution.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardHomogeneity

open GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldTwistorBKKAnalyticPicardApplication
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- On the actual normalized positive quaternionic-Kähler twistor, either
the same contact line generates the full analytic locally-free rank-one
sheaf Picard group or the actual biholomorphic contact automorphisms act
transitively. The only BKK input is the explicitly named, reviewed
*general derived analytic corollary*; T1, canonical contact, and Kodaira are
separate registered general inputs. -/
theorem exists_normalized_analyticPicard_generator_or_contactAut_transitive
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        letI := A.charts
        letI := A.complexManifold
        Function.Bijective (fun r : ℤ =>
          (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
            (contactClass P.tangent P.connection C.contact.line) :
            SheafClass (B := SphereBundleTotal P.tangent)
              𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∨
        (∀ z w : SphereBundleTotal P.tangent,
          ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
            f.1 z = w) := by
  obtain ⟨A, C, hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  refine ⟨A, C, ?_⟩
  exact analyticPicard_generator_or_contactAut_transitive
    hBKK P n (by omega) A C hAmple

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardHomogeneity
