import QuaternionicSymmetry.ManifoldTangentCharacterThirteenFourteenNumbers
import QuaternionicSymmetry.ManifoldE14OrbitalNumbers
import QuaternionicSymmetry.ManifoldAmannIntersectionInput
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
import QuaternionicSymmetry.QuaternionicQuarterPowerNumber
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.LinearMap.Rat

/-! Actual virtual-character reserves in dimensions thirteen and fourteen.
The two nonnegative remainders come from the scalar orbital formula and the
registered generalized intersection theorem on actual de Rham classes. -/
namespace QuaternionicSymmetry.ManifoldE14VirtualBounds
open Module MvPolynomial ManifoldEvenCharacteristicAlgebra
open ManifoldIntegratedRecoveredCertificates ManifoldTangentCharacterNumber
open ManifoldTangentCharacterThirteenFourteenNumbers
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
open ManifoldE14OrbitalNumbers ManifoldAmannIntersectionInput
open QuaternionicQuarterPowerNumber QuaternionicRecoveredSourceComparison
open QuaternionicClosedSourceNumbers ManifoldHodgeSquareApplication
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

noncomputable def candidateFunctional (qdim k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E) :
    DimensionThirteenFourteenDensity.P →ₗ[ℚ] ℝ :=
  ((topIntegral Q k hdim).toAddMonoidHom.comp
    (ManifoldRecoveredCharacteristicCertificates.evaluateSeven Q D qdim).toAddMonoidHom).toRatLinearMap

theorem candidateFunctional_apply (qdim k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (p : DimensionThirteenFourteenDensity.P) :
    candidateFunctional Q D qdim k hdim p =
      sevenCandidateNumber Q D qdim k hdim p := by
  rfl

theorem density13_linear (hdim : 52 = Module.finrank ℝ E) :
    candidateFunctional Q D 13 12 hdim DimensionThirteenFourteenDensity.density13 =
      392 * candidateFunctional Q D 13 12 hdim
        (DimensionThirteenFourteenDensity.u ^ 13) +
      candidateFunctional Q D 13 12 hdim H2WitnessThirteen.orbitalSum +
      18 * candidateFunctional Q D 13 12 hdim
        (H2WitnessThirteen.factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 7) := by
  rw [H2WitnessThirteen.density13_witness, H2WitnessThirteen.witness]
  rw [mul_assoc (MvPolynomial.C (18 : ℚ)) (H2WitnessThirteen.factor ^ 2)
    (DimensionThirteenFourteenDensity.u ^ 7)]
  simp only [map_add, ← smul_eq_C_mul,
    map_smul, Rat.smul_def]
  norm_num

theorem density14_linear (hdim : 56 = Module.finrank ℝ E) :
    candidateFunctional Q D 14 13 hdim DimensionThirteenFourteenDensity.density14 =
      448 * candidateFunctional Q D 14 13 hdim
        (DimensionThirteenFourteenDensity.u ^ 14) +
      candidateFunctional Q D 14 13 hdim H2WitnessFourteen.orbitalSum +
      20 * candidateFunctional Q D 14 13 hdim
        (H2WitnessFourteen.factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 8) := by
  rw [H2WitnessFourteen.density14_witness, H2WitnessFourteen.witness]
  rw [mul_assoc (MvPolynomial.C (20 : ℚ)) (H2WitnessFourteen.factor ^ 2)
    (DimensionThirteenFourteenDensity.u ^ 8)]
  simp only [map_add, ← smul_eq_C_mul,
    map_smul, Rat.smul_def]
  norm_num

variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

private theorem candidate_u_power (n k : ℕ)
    (hqdim : S.quaternionicDimension = n)
    (hdim : 4*(k+1) = Module.finrank ℝ E) (t : ℝ) :
    sevenCandidateNumber P.tangent P.connection n k hdim
      (DimensionThirteenFourteenDensity.u ^ (k+1)) =
        ManifoldQuaternionicCanonicalIntegration.integral P.tangent
          (ManifoldQuaternionicQuarterVolume.quarterTop P.tangent P.connection
            (k+1) hdim) := by
  have h := sourcePolynomialNumber_u_power S P.tangent P.connection t k hdim
  rw [sourceNumber_eq_sevenCandidate S P.tangent P.connection t k hdim,
    hqdim] at h
  simpa only [DimensionThirteenFourteenDensity.u] using h

theorem virtual13_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 13) :
    392 * ManifoldQuaternionicCanonicalIntegration.integral P.tangent
      (ManifoldQuaternionicQuarterVolume.quarterTop P.tangent P.connection 13
        (show 4*13 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 13 12
        (show 4*(12+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega) (Characters.virtual 13) := by
  have hdim : 4*(12+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have hOrbital := orbital13_recovered_nonnegative S P hsource hsp heq38 hn hdim
  have hSquare := amann_witness13_square_nonnegative S P hAmann hsp heq38 hn hdim
  have hu := candidate_u_power S P 13 12 hn hdim 0
  have hlinear := density13_linear P.tangent P.connection hdim
  simp only [candidateFunctional_apply] at hlinear
  rw [virtual13_eq_recovered P.tangent P.connection hdim]
  rw [← hu]
  linarith

theorem virtual13_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 13) :
    0 < characteristicFunctional P.tangent P.connection 13 12
      (show 4*(12+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 13) := by
  have hb := virtual13_quarter_bound S P hsource hAmann hsp heq38 hn
  have hq := quarterTop_positive S P 13 hsp heq38
    (by omega) (show 4*13 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 392) hq) hb

theorem virtual14_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 14) :
    448 * ManifoldQuaternionicCanonicalIntegration.integral P.tangent
      (ManifoldQuaternionicQuarterVolume.quarterTop P.tangent P.connection 14
        (show 4*14 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 14 13
        (show 4*(13+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega) (Characters.virtual 14) := by
  have hdim : 4*(13+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have hOrbital := orbital14_recovered_nonnegative S P hsource hsp heq38 hn hdim
  have hSquare := amann_witness14_square_nonnegative S P hAmann hsp heq38 hn hdim
  have hu := candidate_u_power S P 14 13 hn hdim 0
  have hlinear := density14_linear P.tangent P.connection hdim
  simp only [candidateFunctional_apply] at hlinear
  rw [virtual14_eq_recovered P.tangent P.connection hdim]
  rw [← hu]
  linarith

theorem virtual14_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 14) :
    0 < characteristicFunctional P.tangent P.connection 14 13
      (show 4*(13+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 14) := by
  have hb := virtual14_quarter_bound S P hsource hAmann hsp heq38 hn
  have hq := quarterTop_positive S P 14 hsp heq38
    (by omega) (show 4*14 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 448) hq) hb

end
end QuaternionicSymmetry.ManifoldE14VirtualBounds
