import QuaternionicSymmetry.Stage2IntrinsicSources
import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiExactGeneratedAmple

/-! Recover generation of the genuine unscaled contact line from the actual
normalized contact-homogeneity induction. The chosen line is also ample; no
generation or contact-line identification is supplied by the caller. -/

namespace QuaternionicSymmetry.Stage2IntrinsicGenerationApplication

open Stage2ActualInduction Stage2IntrinsicSources
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorNittaTakeuchiExactGeneratedAmple
open HolomorphicLineCorePullback HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_generated_ample_of_normalizedContactHomogeneity
    (sources : Sources) (n : ℕ) (hn : 2 ≤ n)
    (hHom : NormalizedContactHomogeneity n)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      letI := A.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) ∧
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) := by
  obtain ⟨s,hs,A,hTrans⟩ := exists_rescaled_fullAut_transitive
    n hn hHom P hDim sources.kswDecomposition
  exact exists_actual_generated_ample_contact_core
    sources.positiveContact sources.kodaira
    sources.orbitSubmersion sources.bwwReductive P n hn hDim s hs A hTrans

end
end QuaternionicSymmetry.Stage2IntrinsicGenerationApplication
