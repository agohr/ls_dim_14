import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! The positive-contact-ampleness conclusion on the explicitly normalized
homothety of an arbitrary compact connected positive quaternionic-Kähler
input. Normalization is supplied by the checked scalar-curvature scaling
construction, not baked into a new source premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicKSWEq38Input
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open HolomorphicPositiveLineKodairaSource
open HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The original positive metric needs no scalar normalization in its
hypotheses: an actual positive homothety is chosen, then the same selected
contact line on that normalized twistor is ample. -/
theorem exists_rescaled_ample_contact_core
    (hT1 : ManifoldTwistorPositiveRicciInput.NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∃ A : CompatibleComplexAtlas
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension,
      ∃ C : NondegenerateHolomorphicContactData
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension A,
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
        (contactLineCore (rescaleCompact P s hs).tangent
          (rescaleCompact P s hs).connection C.contact.line) := by
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 hn
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira (rescaleCompact P s hs)
    S.quaternionicDimension hn S.real_finrank hScalar
  exact ⟨s,hs,A,C,hAmple⟩

end
end QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
