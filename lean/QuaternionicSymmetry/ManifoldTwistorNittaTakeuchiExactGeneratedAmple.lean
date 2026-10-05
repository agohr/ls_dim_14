import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiPositiveContactAmple
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyExactContactGeneration

/-! The published unnormalized positive twistor input selects an ample
actual contact line. Independently, normalized holomorphic homogeneity
transports through the checked homothety biholomorphism to *that same*
selected unscaled atlas, where the general orbit theorem generates its
exact contact quotient. No contact-line transport or arbitrary positive
contact selection is assumed. -/

namespace QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiExactGeneratedAmple

open ManifoldTwistorNittaTakeuchiPositiveRicciInput
open ManifoldTwistorNittaTakeuchiPositiveContactAmple
open ManifoldQuaternionicHomothetyExactContactGeneration
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldTwistorFullAutomorphisms ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open GeneralHolomorphicTransitiveOrbitSource
open GeneralHolomorphicFullAutomorphismLieSource
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCorePullback
open HolomorphicPositiveLineKodairaSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The positive-scale Nitta–Takeuchi source and normalized full
biholomorphism transitivity give both useful properties of one and the
same actual unscaled contact line. -/
theorem exists_actual_generated_ample_contact_core
    (hNT : PositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (s : ℝ) (hs : s ≠ 0)
    (A : CompatibleComplexAtlas (rescaleMetric P.tangent s hs)
      (rescaleConnection P.tangent P.connection s hs) n)
    (hTrans : ∀ z w : SphereBundleTotal (rescaleMetric P.tangent s hs),
      ∃ f : TwistorHolomorphicAutomorphisms
        (rescaleMetric P.tangent s hs)
        (rescaleConnection P.tangent P.connection s hs) A,
        f.1 z = w) :
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
      letI := B.charts
      letI := B.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) ∧
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) := by
  obtain ⟨B,C,hAmple⟩ := exists_actual_ample_contact_core
    hNT hKodaira P n hn hDim
  letI := B.charts
  letI := B.complexManifold
  have hGen := exact_contactLine_generated_of_normalized_fullAut_transitive_of_reductive
    hLee hAutSource P s hs A B C hn hDim hTrans
  exact ⟨B,C,hGen,hAmple⟩

end
end QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiExactGeneratedAmple
