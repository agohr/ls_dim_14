import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerRecoveredBounds
import QuaternionicSymmetry.ManifoldTangentCharacterNumber
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuarterBounds

/-! Positive canonical virtual-character numbers for the actual tangent
A-hat functional. Identifying it with the holomorphic index, and hence with
the isometry dimension minus the numerical threshold, remains separate. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerVirtualBounds
open ManifoldTangentCharacterNumber ManifoldPositiveQuaternionicKahlerRecoveredBounds
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

theorem virtual11_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) :
    288 * integral P.tangent (quarterTop P.tangent P.connection 11
      (by have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 11 10
        (by have h := S.real_finrank; omega) (Characters.virtual 11) := by
  rw [virtual11_eq_recovered]
  have h := density11_recovered_quarter_bound S P hsource hsp heq38 hn
  simpa only [hn] using h

theorem virtual11_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) :
    0 < characteristicFunctional P.tangent P.connection 11 10
      (by have h := S.real_finrank; omega) (Characters.virtual 11) := by
  rw [virtual11_eq_recovered]
  have h := density11_recovered_positive S P hsource hsp heq38 hn
  simpa only [hn] using h

theorem virtual12_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) :
    336 * integral P.tangent (quarterTop P.tangent P.connection 12
      (by have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 12 11
        (by have h := S.real_finrank; omega) (Characters.virtual 12) := by
  rw [virtual12_eq_recovered]
  have h := density12_recovered_quarter_bound S P hsource hsp heq38 hn
  simpa only [hn] using h

theorem virtual12_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) :
    0 < characteristicFunctional P.tangent P.connection 12 11
      (by have h := S.real_finrank; omega) (Characters.virtual 12) := by
  rw [virtual12_eq_recovered]
  have h := density12_recovered_positive S P hsource hsp heq38 hn
  simpa only [hn] using h

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerVirtualBounds
