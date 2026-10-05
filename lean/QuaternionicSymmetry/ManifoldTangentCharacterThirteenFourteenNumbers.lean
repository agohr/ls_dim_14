import QuaternionicSymmetry.ManifoldTangentCharacterThirteenFourteen
import QuaternionicSymmetry.QuaternionicRecoveredSourceComparison

/-! The actual tangent virtual-character numbers in dimensions 13 and 14
agree with the recovered and corrected-source characteristic numbers. -/
namespace QuaternionicSymmetry.ManifoldTangentCharacterThirteenFourteenNumbers
open ManifoldEvenCharacteristicAlgebra ManifoldTangentTraceRootCandidates
open ManifoldIntegratedDensityCertificates ManifoldIntegratedRecoveredCertificates
open ManifoldTangentCharacterNumber ManifoldTangentCharacterThirteenFourteen
open TangentAhatCharacterDensity
open QuaternionicRecoveredSourceComparison QuaternionicClosedSourceNumbers
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

theorem virtual13_eq_recovered (hdim : 52 = Module.finrank ℝ E) :
    characteristicFunctional Q D 13 12 hdim (Characters.virtual 13) =
      sevenCandidateNumber Q D 13 12 hdim DimensionThirteenFourteenDensity.density13 := by
  exact characteristicFunctional_eq_of_density Q D 13 12 hdim
    (Characters.virtual 13) DimensionThirteenFourteenDensity.density13
    ((TangentAhatThirteenFourteen.characterDensity_13
      (quarterUTotal Q D) (normalizedTangentHalfTrace Q D 13)).trans
      (standard_evaluation_seven Q D 13 DimensionThirteenFourteenDensity.density13))

theorem virtual14_eq_recovered (hdim : 56 = Module.finrank ℝ E) :
    characteristicFunctional Q D 14 13 hdim (Characters.virtual 14) =
      sevenCandidateNumber Q D 14 13 hdim DimensionThirteenFourteenDensity.density14 := by
  exact characteristicFunctional_eq_of_density Q D 14 13 hdim
    (Characters.virtual 14) DimensionThirteenFourteenDensity.density14
    ((TangentAhatThirteenFourteen.characterDensity_14
      (quarterUTotal Q D) (normalizedTangentHalfTrace Q D 14)).trans
      (standard_evaluation_seven Q D 14 DimensionThirteenFourteenDensity.density14))

variable (S : QuaternionicStructure E)

theorem virtual13_eq_source (hqdim : S.quaternionicDimension = 13)
    (hdim : 52 = Module.finrank ℝ E) (t : ℝ) :
    characteristicFunctional Q D 13 12 hdim (Characters.virtual 13) =
      sourcePolynomialNumber S Q D t 12 hdim
        DimensionThirteenFourteenDensity.density13 := by
  rw [virtual13_eq_recovered Q D hdim,
    sourceNumber_eq_sevenCandidate S Q D t 12 hdim, hqdim]

theorem virtual14_eq_source (hqdim : S.quaternionicDimension = 14)
    (hdim : 56 = Module.finrank ℝ E) (t : ℝ) :
    characteristicFunctional Q D 14 13 hdim (Characters.virtual 14) =
      sourcePolynomialNumber S Q D t 13 hdim
        DimensionThirteenFourteenDensity.density14 := by
  rw [virtual14_eq_recovered Q D hdim,
    sourceNumber_eq_sevenCandidate S Q D t 13 hdim, hqdim]

end
end QuaternionicSymmetry.ManifoldTangentCharacterThirteenFourteenNumbers
