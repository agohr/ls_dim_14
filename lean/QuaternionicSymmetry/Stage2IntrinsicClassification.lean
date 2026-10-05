import QuaternionicSymmetry.Stage2ContactInduction
import QuaternionicSymmetry.Stage2IntrinsicMetricApplication
import QuaternionicSymmetry.Stage2IntrinsicGenerationApplication

/-! The Stage 2 intrinsic metric endpoints. C12 has no Amann premise; E14
adds precisely the separately registered sign source. The argument constructs
all twistor, Picard, group, torus, weight, fixed-component and induction data
internally from the disclosed general literature. Dimension one uses the
actual Einstein/Weyl geometric convention, not quaternionic-span preservation
alone. No simple-connectedness assumption is imposed on the input manifold. -/

namespace QuaternionicSymmetry.Stage2IntrinsicClassification

open Stage2IntrinsicSources Stage2IntrinsicGeometry Stage2ContactInduction
open Stage2IntrinsicMetricApplication Stage2IntrinsicGenerationApplication
open ManifoldFourDerdzinskiIntrinsicSymmetry ManifoldRiemannianIntrinsicSymmetry
open ManifoldTwistorNittaTakeuchiPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open HolomorphicLineCorePullback HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Intrinsic symmetry of the given metric in quaternionic dimensions 1–12,
conditional only on the explicit literature boundary. No H1 input occurs. -/
theorem intrinsicSymmetric_c12 (sources : Sources)
    (hFour : DerdzinskiFourSymmetrySource)
    {n : ℕ} (P : CompactConnectedPositiveTwistorGeometry (E := E) (M := M) n)
    (hn : n ≤ 12) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_through_bound 12 (normalizedContactHomogeneity_c12 sources)
    sources.kswDecomposition (normalized_of_positive sources.positiveContact)
    sources.ballmann sources.wolfLeBrun hFour P hn

/-- The extended endpoint through quaternionic dimension 14, with Amann's
approved sign source visible as its sole additional source argument. -/
theorem intrinsicSymmetric_e14 (sources : Sources)
    (hFour : DerdzinskiFourSymmetrySource) (hAmann : AmannInput)
    {n : ℕ} (P : CompactConnectedPositiveTwistorGeometry (E := E) (M := M) n)
    (hn : n ≤ 14) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_through_bound 14 (normalizedContactHomogeneity_e14 sources hAmann)
    sources.kswDecomposition (normalized_of_positive sources.positiveContact)
    sources.ballmann sources.wolfLeBrun hFour P hn

/-- Generation and ampleness of the same original contact line, for every
actual higher-dimensional C12 geometry. -/
theorem exists_generated_ample_contact_c12 (sources : Sources)
    (n : ℕ) (hn : 2 ≤ n) (hn12 : n ≤ 12)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      letI := A.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) ∧
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) :=
  exists_generated_ample_of_normalizedContactHomogeneity sources n hn
    (normalizedContactHomogeneity_c12 sources n hn hn12) P hDim

/-- The E14 original-line generation theorem, with its extra sign input. -/
theorem exists_generated_ample_contact_e14 (sources : Sources) (hAmann : AmannInput)
    (n : ℕ) (hn : 2 ≤ n) (hn14 : n ≤ 14)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      letI := A.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) ∧
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) :=
  exists_generated_ample_of_normalizedContactHomogeneity sources n hn
    (normalizedContactHomogeneity_e14 sources hAmann n hn hn14) P hDim

end
end QuaternionicSymmetry.Stage2IntrinsicClassification
