import QuaternionicSymmetry.QuaternionicRecoveredSourceComparison
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuarterBounds

/-! The actual canonical recovered characteristic numbers satisfy the C12
bounds.  Source/recovered identification is proved internally; the only
literature premises here are the registered orbital and KSW statements. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerRecoveredBounds
open QuaternionicRecoveredSourceComparison ManifoldIntegratedRecoveredCertificates
open ManifoldPositiveQuaternionicKahlerQuarterBounds
open ManifoldPositiveQuaternionicKahlerPositiveNumbers
open ManifoldQuaternionicQuarterVolume ManifoldQuaternionicCanonicalIntegration
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem density11_recovered_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) :
    288 * integral P.tangent (quarterTop P.tangent P.connection 11
      (by have h := S.real_finrank; omega)) ≤
      sixCandidateNumber P.tangent P.connection S.quaternionicDimension 10
        (by have h := S.real_finrank; omega)
        DimensionElevenTwelveDensity.density11 := by
  have h := density11_quarter_bound S P hsource hsp heq38 hn 0
  rw [sourceNumber_eq_sixCandidate S P.tangent P.connection] at h
  exact h

theorem density11_recovered_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) :
    0 < sixCandidateNumber P.tangent P.connection S.quaternionicDimension 10
      (by have h := S.real_finrank; omega)
      DimensionElevenTwelveDensity.density11 := by
  have h := density11_sourceNumber_positive S P hsource hsp heq38 hn
    (Module.finBasis ℝ E) 0
  rw [sourceNumber_eq_sixCandidate S P.tangent P.connection] at h
  exact h

theorem density12_recovered_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) :
    336 * integral P.tangent (quarterTop P.tangent P.connection 12
      (by have h := S.real_finrank; omega)) ≤
      sixCandidateNumber P.tangent P.connection S.quaternionicDimension 11
        (by have h := S.real_finrank; omega)
        DimensionElevenTwelveDensity.density12 := by
  have h := density12_quarter_bound S P hsource hsp heq38 hn 0
  rw [sourceNumber_eq_sixCandidate S P.tangent P.connection] at h
  exact h

theorem density12_recovered_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) :
    0 < sixCandidateNumber P.tangent P.connection S.quaternionicDimension 11
      (by have h := S.real_finrank; omega)
      DimensionElevenTwelveDensity.density12 := by
  have h := density12_sourceNumber_positive S P hsource hsp heq38 hn
    (Module.finBasis ℝ E) 0
  rw [sourceNumber_eq_sixCandidate S P.tangent P.connection] at h
  exact h

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerRecoveredBounds
