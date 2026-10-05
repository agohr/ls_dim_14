import QuaternionicSymmetry.KillingFieldsPaperPointwise
import QuaternionicSymmetry.KillingFieldsPaperDensityComparison
import QuaternionicSymmetry.ManifoldE14VirtualBounds
import QuaternionicSymmetry.ManifoldFiniteVirtualNumbers

/-! The main paper's alternative certificate route on actual PQK geometry.
All orbital terms are evaluated in fixed rank fourteen after zero padding;
the one degree-twelve class is treated by the existing Amann source contract.
No old dimension-specific positivity theorem is used to supply a sign. -/
namespace QuaternionicSymmetry.ManifoldKillingFieldsPaperVirtualBound
open Module MvPolynomial ManifoldEvenCharacteristicAlgebra
open ManifoldIntegratedRecoveredCertificates ManifoldTangentCharacterNumber
open ManifoldTangentCharacterThirteenFourteenNumbers ManifoldFiniteVirtualNumbers
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldE14VirtualBounds ManifoldAmannIntersectionInput
open QuaternionicQuarterPowerNumber QuaternionicRecoveredSourceComparison
open QuaternionicClosedSourceNumbers ManifoldHodgeSquareApplication
open QuaternionicE14ClosedEvaluation QuaternionicWeylMatrixCoefficients
open QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureOrbitalSign
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicTracePositivity ManifoldClosedPolynomialRepresentative
open QuaternionicClosedSourceGenerators ManifoldEvenClosedEvaluation
open QuaternionicSourceIntegralNonnegative ManifoldQuaternionicKSWScalarConstancyDerived
open KillingFieldsPaperCertificate
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

theorem virtual_eq_paper (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14)
    (hqdim : S.quaternionicDimension = n)
    (hdim : 4*(n-1+1) = Module.finrank ℝ E) :
    characteristicFunctional P.tangent P.connection n (n-1) hdim (Characters.virtual n) =
      candidateFunctional P.tangent P.connection n (n-1) hdim (density n) := by
  rw [candidateFunctional_apply]
  have hs := sourceNumber_eq_sevenCandidate S P.tangent P.connection 0 (n-1) hdim (density n)
  rw [hqdim] at hs
  rw [← hs]
  rcases hn with ⟨hlo, hhi⟩
  interval_cases n
  · rw [density2_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 2 (by omega) (by omega) hqdim hdim 0
  · rw [density3_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 3 (by omega) (by omega) hqdim hdim 0
  · rw [density4_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 4 (by omega) (by omega) hqdim hdim 0
  · rw [density5_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 5 (by omega) (by omega) hqdim hdim 0
  · rw [density6_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 6 (by omega) (by omega) hqdim hdim 0
  · rw [density7_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 7 (by omega) (by omega) hqdim hdim 0
  · rw [density8_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 8 (by omega) (by omega) hqdim hdim 0
  · rw [density9_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 9 (by omega) (by omega) hqdim hdim 0
  · rw [density10_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 10 (by omega) (by omega) hqdim hdim 0
  · rw [density11_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 11 (by omega) (by omega) hqdim hdim 0
  · rw [density12_eq_existing]
    exact virtual_eq_source S P.tangent P.connection 12 (by omega) (by omega) hqdim hdim 0
  · rw [density13_eq_existing]
    exact virtual13_eq_source P.tangent P.connection S hqdim hdim 0
  · rw [density14_eq_existing]
    exact virtual14_eq_source P.tangent P.connection S hqdim hdim 0

theorem remainder_recovered_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (hqdim : S.quaternionicDimension = n)
    (hdim : 4*(n-1+1) = Module.finrank ℝ E) :
    0 ≤ candidateFunctional P.tangent P.connection n (n-1) hdim (remainder n) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, _, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  have hn' : n-1+1 = n := by omega
  have hw : IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (remainder n) (n-1+1) := by
    simpa only [hn'] using remainder_weighted n hn
  have hp := sourcePolynomialNumber_nonnegative S P.tangent P.connection
    (Module.finBasis ℝ E) t (n-1) hdim (remainder n) hw (by
      intro p y hy F hF
      obtain ⟨W, hW, hv⟩ := seven_generator_values S P.tangent P.connection
        (formula_of_KSWLemma310OnModel S P.tangent hsp P.toPositiveScalarTangentGeometry hn2)
        hd (Module.finBasis ℝ E) t (fun p y hy => (ht p y hy).symm) p y hy
      rw [pointwise_representative_complex, hv]
      have hh := KillingFieldsPaperPointwise.remainder_nonnegative (β := Index S)
        hsource S.quaternionicDimension (by omega) S (Module.finBasis ℝ E)
        ((t^2 / Real.pi)^2) (sq_nonneg _) rfl
        (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) (Module.finBasis ℝ E))
        (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
          (Module.finBasis ℝ E) hW.1 hW.2.2.2.2.1) F hF
      simpa only [hqdim] using hh)
  rw [sourceNumber_eq_sevenCandidate, hqdim] at hp
  exact hp

theorem square_recovered_nonnegative
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (hqdim : S.quaternionicDimension = n)
    (hdim : 4*(n-1+1) = Module.finrank ℝ E) :
    0 ≤ candidateFunctional P.tangent P.connection n (n-1) hdim (squareTerm n) := by
  by_cases hlarge : 13 ≤ n
  · have hHodge := quarter_square_nonnegative S P hAmann hsp heq38 (by omega)
      (n-1) (by omega) hdim
    have hs := weighted_square_nonnegative P.tangent P.connection n (n-1) hdim
      hHodge 3 (by omega) eta eta_weighted
    have hn' : n-1+1-2*3 = n-6 := by omega
    rw [hn'] at hs
    unfold squareTerm
    rw [← smul_eq_C_mul, map_smul, Rat.smul_def]
    apply mul_nonneg _ hs
    unfold squareCoefficient
    split_ifs <;> norm_num
  · have h13 : n ≠ 13 := by omega
    have h14 : n ≠ 14 := by omega
    simp [squareTerm, squareCoefficient, h13, h14]

/-- The volume lower bound proved by the paper's twelve common spectra and
one global square, uniformly through quaternionic dimension fourteen. -/
theorem virtual_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (hqdim : S.quaternionicDimension = n) :
    (scalarCoefficient n : ℝ) * ManifoldQuaternionicCanonicalIntegration.integral P.tangent
      (ManifoldQuaternionicQuarterVolume.quarterTop P.tangent P.connection n
        (by have h := S.real_finrank; omega)) ≤
    characteristicFunctional P.tangent P.connection n (n-1)
      (by have h := S.real_finrank; omega) (Characters.virtual n) := by
  have hdim : 4*(n-1+1) = Module.finrank ℝ E := by have h := S.real_finrank; omega
  rw [virtual_eq_paper S P n hn hqdim hdim, full_certificate n hn]
  rw [map_add, map_add, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  have hu := sourcePolynomialNumber_u_power S P.tangent P.connection 0 (n-1) hdim
  rw [sourceNumber_eq_sevenCandidate, hqdim] at hu
  have hn' : n-1+1 = n := by omega
  simp only [hn'] at hu
  change candidateFunctional P.tangent P.connection n (n-1) hdim
    (DimensionThirteenFourteenDensity.u ^ n) = _ at hu
  rw [hu]
  have hr := remainder_recovered_nonnegative S P hsource hsp heq38 n hn hqdim hdim
  have hs := square_recovered_nonnegative S P hAmann hsp heq38 n hn hqdim hdim
  norm_cast
  linarith

end
end QuaternionicSymmetry.ManifoldKillingFieldsPaperVirtualBound
