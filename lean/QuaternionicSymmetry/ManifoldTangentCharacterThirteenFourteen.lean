import QuaternionicSymmetry.TangentAhatThirteenFourteen
import QuaternionicSymmetry.ManifoldTangentCharacterNumber
import QuaternionicSymmetry.SevenStandardValuesCompact

/-! Canonical characteristic-number comparison for the actual tangent
formal A-hat character convolution in quaternionic dimensions 13 and 14. -/
namespace QuaternionicSymmetry.ManifoldTangentCharacterThirteenFourteen
open ManifoldEvenCharacteristicAlgebra ManifoldTangentTraceRootCandidates
open ManifoldIntegratedDensityCertificates ManifoldIntegratedRecoveredCertificates
open ManifoldRecoveredCharacteristicCertificates ManifoldTangentCharacterNumber
open TangentAhatCharacterDensity RecoveredLogAhatSix
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

private theorem standard_C (qdim : ℕ) (r : ℚ) :
    MvPolynomial.aeval (standardValues qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim))
        (MvPolynomial.C r : DimensionThirteenFourteenDensity.P) =
      evaluateSeven Q D qdim (MvPolynomial.C r) := by
  rw [MvPolynomial.aeval_C]
  simp only [evaluateSeven, ManifoldSevenVariableGradedEvaluation.evaluate,
    MvPolynomial.eval₂Hom_C]
  change (algebraMap ℚ (Total (E := E) (M := M))) r = rationalConstants r
  rfl

private theorem generatorValues_eq_compact (qdim : ℕ) :
    ManifoldSevenVariableGradedEvaluation.generatorValues
      (candidateGenerators Q D qdim) =
        fun i : Fin 7 => if i = 0 then quarterUTotal Q D else
          DirectSum.of (Grade (E := E) (M := M)) i.val
            (candidatePowerClass Q D qdim i) := by
  funext i
  fin_cases i <;> rfl

private theorem standard_X (qdim : ℕ) (i : Fin 7) :
    MvPolynomial.aeval (standardValues qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim))
        (MvPolynomial.X i : DimensionThirteenFourteenDensity.P) =
      evaluateSeven Q D qdim (MvPolynomial.X i) := by
  rw [MvPolynomial.aeval_X]
  simp only [evaluateSeven, ManifoldSevenVariableGradedEvaluation.evaluate,
    MvPolynomial.eval₂Hom_X']
  rw [SevenStandardValuesCompact.standardValues_eq,
    generatorValues_eq_compact Q D qdim]
  by_cases hi : i = 0
  · simp [hi]
  · simpa only [hi, ↓reduceIte, candidatePower] using
      candidatePower_eq_of_class Q D qdim i

private theorem standard_hom (qdim : ℕ) :
    (MvPolynomial.aeval (standardValues qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim))).toRingHom =
      evaluateSeven Q D qdim :=
  MvPolynomial.ringHom_ext (standard_C Q D qdim) (standard_X Q D qdim)

theorem standard_evaluation_seven (qdim : ℕ)
    (P : DimensionThirteenFourteenDensity.P) :
    MvPolynomial.aeval (standardValues qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) P =
        evaluateSeven Q D qdim P :=
  DFunLike.congr_fun (standard_hom Q D qdim) P

variable [MeasurableSpace E] [BorelSpace E]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

theorem characteristicFunctional_eq_of_density (qdim k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (χ : LaurentPolynomial ℚ) (P : DimensionThirteenFourteenDensity.P)
    (h : characterDensity (k+1) (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim) χ = evaluateSeven Q D qdim P) :
    characteristicFunctional Q D qdim k hdim χ =
      sevenCandidateNumber Q D qdim k hdim P := by
  unfold characteristicFunctional sevenCandidateNumber
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  exact congrArg (fun z : Total (E := E) (M := M) =>
    integrateGrade Q k hdim
      (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k+1) z)) h

end
end QuaternionicSymmetry.ManifoldTangentCharacterThirteenFourteen
