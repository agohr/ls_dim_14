import QuaternionicSymmetry.QuaternionicE14OrbitalPointwise

/-! Nonnegativity of each complete E14 orbital remainder, including all
58 registered finite witness coefficients and admissible spectra. -/
namespace QuaternionicSymmetry.QuaternionicE14OrbitalSums
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  QuaternionicE14OrbitalPointwise
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {ι β V : Type*} [Fintype ι] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def evaluatedFunctional (v : Fin 7 → CE V) (F : CE V →ₗ[ℝ] ℝ) :
    DimensionThirteenFourteenDensity.P →ₗ[ℚ] ℝ :=
  (F.restrictScalars ℚ).comp (aeval v).toLinearMap

theorem weighted_orbital_sum_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (n k : ℕ) (hn : 11 ≤ n) (hk : k ≤ 6)
    {m : ℕ} (terms : Fin m → List ℕ × ℚ)
    (hc : ∀ i, 0 ≤ (terms i).2) (ha : ∀ i, (terms i).1.length ≤ n)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ) (hs : 0 ≤ s)
    (hqdim : Q.quaternionicDimension = n)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : ∀ i, QuaternionicMatrixModel.HermitianAntiSelfDual (A i))
    (η : β → E V) (hη : ∀ i, η i ∈ HyperholomorphicExterior.formSpace Q b)
    (F : CE V →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := V) (topForm Q b))) :
    0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ (n-k) *
        H2WitnessThirteen.embed
          (∑ i, C (terms i).2 * FiniteTypeCSchurSix.orbital n k (terms i).1))) := by
  let L := evaluatedFunctional (sevenValues Q b s A η) F
  change 0 ≤ L _
  have he : DimensionThirteenFourteenDensity.u ^ (n-k) *
      H2WitnessThirteen.embed
        (∑ i, C (terms i).2 * FiniteTypeCSchurSix.orbital n k (terms i).1) =
      ∑ i, C (terms i).2 * (DimensionThirteenFourteenDensity.u ^ (n-k) *
        H2WitnessThirteen.embed (FiniteTypeCSchurSix.orbital n k (terms i).1)) := by
    simp only [map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show H2WitnessThirteen.embed (C (terms i).2) = C (terms i).2 from
      H2WitnessThirteen.embed.commutes (terms i).2]
    ring
  rw [he]
  simp only [map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (by exact_mod_cast hc i)
  exact PositiveRay.functional_nonneg
    (orbital_term_in_positive_ray hsource n k hn hk (terms i).1 (ha i)
      Q b s hs hqdim A hA η hη) F hF

theorem orbitalSum13_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ) (hs : 0 ≤ s)
    (hn : Q.quaternionicDimension = 13)
    (A : β → Matrix (Fin 13 ⊕ Fin 13) (Fin 13 ⊕ Fin 13) ℂ)
    (hA : ∀ i, QuaternionicMatrixModel.HermitianAntiSelfDual (A i))
    (η : β → E V) (hη : ∀ i, η i ∈ HyperholomorphicExterior.formSpace Q b)
    (F : CE V →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := V) (topForm Q b))) :
    0 ≤ F (aeval (sevenValues Q b s A η) H2WitnessThirteen.orbitalSum) := by
  have h1 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 12 *
        H2WitnessThirteen.embed H2WitnessThirteen.w1)) := by
    rw [H2WitnessThirteenChecks.w1_entries]
    exact weighted_orbital_sum_nonnegative hsource 13 1 (by decide) (by decide)
      H2WitnessThirteenChecks.terms1
      (fun i => (H2WitnessThirteenChecks.terms1_positive i).le)
      (fun i => (H2WitnessThirteenChecks.terms1_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h2 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 11 *
        H2WitnessThirteen.embed H2WitnessThirteen.w2)) := by
    rw [H2WitnessThirteenChecks.w2_entries]
    exact weighted_orbital_sum_nonnegative hsource 13 2 (by decide) (by decide)
      H2WitnessThirteenChecks.terms2
      (fun i => (H2WitnessThirteenChecks.terms2_positive i).le)
      (fun i => (H2WitnessThirteenChecks.terms2_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h3 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 10 *
        H2WitnessThirteen.embed H2WitnessThirteen.w3)) := by
    rw [H2WitnessThirteenChecks.w3_entries]
    exact weighted_orbital_sum_nonnegative hsource 13 3 (by decide) (by decide)
      H2WitnessThirteenChecks.terms3
      (fun i => (H2WitnessThirteenChecks.terms3_positive i).le)
      (fun i => (H2WitnessThirteenChecks.terms3_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h4 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 9 *
        H2WitnessThirteen.embed H2WitnessThirteen.w4)) := by
    rw [H2WitnessThirteenChecks.w4_entries]
    exact weighted_orbital_sum_nonnegative hsource 13 4 (by decide) (by decide)
      H2WitnessThirteenChecks.terms4
      (fun i => (H2WitnessThirteenChecks.terms4_positive i).le)
      (fun i => (H2WitnessThirteenChecks.terms4_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h5 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 8 *
        H2WitnessThirteen.embed H2WitnessThirteen.w5)) := by
    rw [H2WitnessThirteenChecks.w5_entries]
    exact weighted_orbital_sum_nonnegative hsource 13 5 (by decide) (by decide)
      H2WitnessThirteenChecks.terms5
      (fun i => (H2WitnessThirteenChecks.terms5_positive i).le)
      (fun i => (H2WitnessThirteenChecks.terms5_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h6 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 7 *
        H2WitnessThirteen.embed H2WitnessThirteen.w6)) := by
    rw [H2WitnessThirteenChecks.w6_entries]
    exact weighted_orbital_sum_nonnegative hsource 13 6 (by decide) (by decide)
      H2WitnessThirteenChecks.terms6
      (fun i => (H2WitnessThirteenChecks.terms6_positive i).le)
      (fun i => (H2WitnessThirteenChecks.terms6_admissible i).1)
      Q b s hs hn A hA η hη F hF
  simpa only [H2WitnessThirteen.orbitalSum, map_add] using
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) h5) h6

theorem orbitalSum14_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ) (hs : 0 ≤ s)
    (hn : Q.quaternionicDimension = 14)
    (A : β → Matrix (Fin 14 ⊕ Fin 14) (Fin 14 ⊕ Fin 14) ℂ)
    (hA : ∀ i, QuaternionicMatrixModel.HermitianAntiSelfDual (A i))
    (η : β → E V) (hη : ∀ i, η i ∈ HyperholomorphicExterior.formSpace Q b)
    (F : CE V →ₗ[ℝ] ℝ) (hF : 0 ≤ F (embed (V := V) (topForm Q b))) :
    0 ≤ F (aeval (sevenValues Q b s A η) H2WitnessFourteen.orbitalSum) := by
  have h1 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 13 *
        H2WitnessFourteen.embed H2WitnessFourteen.w1)) := by
    rw [H2WitnessFourteenChecks.w1_entries]
    exact weighted_orbital_sum_nonnegative hsource 14 1 (by decide) (by decide)
      H2WitnessFourteenChecks.terms1
      (fun i => (H2WitnessFourteenChecks.terms1_positive i).le)
      (fun i => (H2WitnessFourteenChecks.terms1_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h2 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 12 *
        H2WitnessFourteen.embed H2WitnessFourteen.w2)) := by
    rw [H2WitnessFourteenChecks.w2_entries]
    exact weighted_orbital_sum_nonnegative hsource 14 2 (by decide) (by decide)
      H2WitnessFourteenChecks.terms2
      (fun i => (H2WitnessFourteenChecks.terms2_positive i).le)
      (fun i => (H2WitnessFourteenChecks.terms2_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h3 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 11 *
        H2WitnessFourteen.embed H2WitnessFourteen.w3)) := by
    rw [H2WitnessFourteenChecks.w3_entries]
    exact weighted_orbital_sum_nonnegative hsource 14 3 (by decide) (by decide)
      H2WitnessFourteenChecks.terms3
      (fun i => (H2WitnessFourteenChecks.terms3_positive i).le)
      (fun i => (H2WitnessFourteenChecks.terms3_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h4 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 10 *
        H2WitnessFourteen.embed H2WitnessFourteen.w4)) := by
    rw [H2WitnessFourteenChecks.w4_entries]
    exact weighted_orbital_sum_nonnegative hsource 14 4 (by decide) (by decide)
      H2WitnessFourteenChecks.terms4
      (fun i => (H2WitnessFourteenChecks.terms4_positive i).le)
      (fun i => (H2WitnessFourteenChecks.terms4_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h5 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 9 *
        H2WitnessFourteen.embed H2WitnessFourteen.w5)) := by
    rw [H2WitnessFourteenChecks.w5_entries]
    exact weighted_orbital_sum_nonnegative hsource 14 5 (by decide) (by decide)
      H2WitnessFourteenChecks.terms5
      (fun i => (H2WitnessFourteenChecks.terms5_positive i).le)
      (fun i => (H2WitnessFourteenChecks.terms5_admissible i).1)
      Q b s hs hn A hA η hη F hF
  have h6 : 0 ≤ F (aeval (sevenValues Q b s A η)
      (DimensionThirteenFourteenDensity.u ^ 8 *
        H2WitnessFourteen.embed H2WitnessFourteen.w6)) := by
    rw [H2WitnessFourteenChecks.w6_entries]
    exact weighted_orbital_sum_nonnegative hsource 14 6 (by decide) (by decide)
      H2WitnessFourteenChecks.terms6
      (fun i => (H2WitnessFourteenChecks.terms6_positive i).le)
      (fun i => (H2WitnessFourteenChecks.terms6_admissible i).1)
      Q b s hs hn A hA η hη F hF
  simpa only [H2WitnessFourteen.orbitalSum, map_add] using
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) h5) h6

end
end QuaternionicSymmetry.QuaternionicE14OrbitalSums
