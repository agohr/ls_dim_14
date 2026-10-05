import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardHomogeneity
import QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication

/-!
# Normalized positive twistor: analytic Picard with uniqueness, or homogeneity

The selected T1/contact-canonical/Kodaira data furnish the genuine contact
line's ampleness. Two explicitly passed, reviewed *general derived* BKK clauses then
give the dichotomy, retaining BKK's uniqueness on the Picard branch. Neither
clause is a project-specific premise, and neither is silently asserted here.
The contact line, kernel distribution, and full/contact automorphism groups
all belong to the same selected actual twistor sphere bundle.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardUniqueness

open GeneralContactFanoPicardHomogeneitySource
open GeneralContactFanoPicardUniquenessSource
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldTwistorBKKAnalyticPicardApplication
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The normalized actual positive-PQK twistor has either full analytic
Picard generation *and* preservation of its contact distribution by every
biholomorphism, or transitivity of its genuine contact automorphism group.
The normalized scalar and dimension are stated, not inferred from positivity.
-/
theorem exists_normalized_analyticPicard_unique_or_contactAut_transitive
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        letI := A.charts
        letI := A.complexManifold
        (Function.Bijective (fun r : ℤ =>
          (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
            (contactClass P.tangent P.connection C.contact.line) :
            SheafClass (B := SphereBundleTotal P.tangent)
              𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∧
          FullPreservesContact P.tangent P.connection A C.contact.line) ∨
        (∀ z w : SphereBundleTotal P.tangent,
          ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
            f.1 z = w) := by
  obtain ⟨A, C, hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  refine ⟨A, C, ?_⟩
  rcases analyticPicard_generator_or_contactAut_transitive
      hBKK P n (by omega) A C hAmple with hPic | hHom
  · exact Or.inl ⟨hPic,
      fullPreservesContact_of_analyticPicard_generator
        hUnique P n (by omega) A C hAmple hPic⟩
  · exact Or.inr hHom

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardUniqueness
