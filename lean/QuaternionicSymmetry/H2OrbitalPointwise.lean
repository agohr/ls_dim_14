import QuaternionicSymmetry.OrbitalPointwisePolynomialSign
import QuaternionicSymmetry.H2WitnessThirteenChecks
import QuaternionicSymmetry.H2WitnessFourteenChecks
import QuaternionicSymmetry.PositiveRaySums

/-! Pointwise signs of all six positive orbital groups in each dimension
13/14 witness. The separate Hodge-square sign is not asserted here. -/
namespace QuaternionicSymmetry.H2OrbitalPointwise

open Module MvPolynomial QuaternionicFundamental MatrixTracePolynomial
  OrbitalPointwisePolynomialSign
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

private theorem eval_weighted_sum {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℚ R] [IsScalarTower ℚ ℝ R] {σ : Type*} [Fintype σ]
    (v : Fin 6 → R) (p : σ → FiniteTypeCSchurSix.P) (a : σ → ℚ) (x : R) :
    aeval v (∑ i, C (a i) * p i) * x =
      ∑ i, (a i : ℝ) • (aeval v (p i) * x) := by
  simp only [map_sum, map_mul, aeval_C, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [IsScalarTower.algebraMap_apply ℚ ℝ R, mul_assoc, ← Algebra.smul_def]
  simp

variable {ι β V : Type*} [Fintype ι] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem weighted_orbitals_mem_positiveRay
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (n k : ℕ) (hn : 11 ≤ n) (hk : k ≤ 6)
    {σ : Type*} [Fintype σ] (terms : σ → List ℕ × ℚ)
    (ha : ∀ i, (terms i).1.length ≤ n) (hc : ∀ i, 0 ≤ (terms i).2)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hkQ : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (aeval (fun i : Fin 6 => signedTracePower (complexifiedMatrix B η) (i.val+1))
        (∑ i, C (terms i).2 * FiniteTypeCSchurSix.orbital n k (terms i).1) *
        form Q c ^ (Q.quaternionicDimension-k)) := by
  rw [eval_weighted_sum]
  apply PositiveRay.sum
  intro i
  exact PositiveRay.smul
    (orbital_mem_positiveRay hsource n k hn hk (terms i).1 (ha i) B hB Q c η hη hkQ)
    (by exact_mod_cast hc i)

def groups13 : Fin 6 → FiniteTypeCSchurSix.P :=
  ![H2WitnessThirteen.w1, H2WitnessThirteen.w2, H2WitnessThirteen.w3,
    H2WitnessThirteen.w4, H2WitnessThirteen.w5, H2WitnessThirteen.w6]

theorem groups13_mem_positiveRay
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (B : β → Matrix (Fin 13 ⊕ Fin 13) (Fin 13 ⊕ Fin 13) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hQ : 6 ≤ Q.quaternionicDimension) (j : Fin 6) :
    PositiveRay.Contains (topForm Q c)
      (aeval (fun i : Fin 6 => signedTracePower (complexifiedMatrix B η) (i.val+1))
        (groups13 j) * form Q c ^ (Q.quaternionicDimension-(j.val+1))) := by
  fin_cases j
  · change PositiveRay.Contains _ (aeval _ H2WitnessThirteen.w1 * _)
    rw [H2WitnessThirteenChecks.w1_entries]
    exact weighted_orbitals_mem_positiveRay hsource 13 1 (by decide) (by decide)
      H2WitnessThirteenChecks.terms1
      (fun i => (H2WitnessThirteenChecks.terms1_admissible i).1)
      (fun i => (H2WitnessThirteenChecks.terms1_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessThirteen.w2 * _)
    rw [H2WitnessThirteenChecks.w2_entries]
    exact weighted_orbitals_mem_positiveRay hsource 13 2 (by decide) (by decide)
      H2WitnessThirteenChecks.terms2
      (fun i => (H2WitnessThirteenChecks.terms2_admissible i).1)
      (fun i => (H2WitnessThirteenChecks.terms2_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessThirteen.w3 * _)
    rw [H2WitnessThirteenChecks.w3_entries]
    exact weighted_orbitals_mem_positiveRay hsource 13 3 (by decide) (by decide)
      H2WitnessThirteenChecks.terms3
      (fun i => (H2WitnessThirteenChecks.terms3_admissible i).1)
      (fun i => (H2WitnessThirteenChecks.terms3_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessThirteen.w4 * _)
    rw [H2WitnessThirteenChecks.w4_entries]
    exact weighted_orbitals_mem_positiveRay hsource 13 4 (by decide) (by decide)
      H2WitnessThirteenChecks.terms4
      (fun i => (H2WitnessThirteenChecks.terms4_admissible i).1)
      (fun i => (H2WitnessThirteenChecks.terms4_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessThirteen.w5 * _)
    rw [H2WitnessThirteenChecks.w5_entries]
    exact weighted_orbitals_mem_positiveRay hsource 13 5 (by decide) (by decide)
      H2WitnessThirteenChecks.terms5
      (fun i => (H2WitnessThirteenChecks.terms5_admissible i).1)
      (fun i => (H2WitnessThirteenChecks.terms5_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessThirteen.w6 * _)
    rw [H2WitnessThirteenChecks.w6_entries]
    exact weighted_orbitals_mem_positiveRay hsource 13 6 (by decide) (by decide)
      H2WitnessThirteenChecks.terms6
      (fun i => (H2WitnessThirteenChecks.terms6_admissible i).1)
      (fun i => (H2WitnessThirteenChecks.terms6_positive i).le)
      B hB Q c η hη (by omega)

def groups14 : Fin 6 → FiniteTypeCSchurSix.P :=
  ![H2WitnessFourteen.w1, H2WitnessFourteen.w2, H2WitnessFourteen.w3,
    H2WitnessFourteen.w4, H2WitnessFourteen.w5, H2WitnessFourteen.w6]

theorem groups14_mem_positiveRay
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (B : β → Matrix (Fin 14 ⊕ Fin 14) (Fin 14 ⊕ Fin 14) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hQ : 6 ≤ Q.quaternionicDimension) (j : Fin 6) :
    PositiveRay.Contains (topForm Q c)
      (aeval (fun i : Fin 6 => signedTracePower (complexifiedMatrix B η) (i.val+1))
        (groups14 j) * form Q c ^ (Q.quaternionicDimension-(j.val+1))) := by
  fin_cases j
  · change PositiveRay.Contains _ (aeval _ H2WitnessFourteen.w1 * _)
    rw [H2WitnessFourteenChecks.w1_entries]
    exact weighted_orbitals_mem_positiveRay hsource 14 1 (by decide) (by decide)
      H2WitnessFourteenChecks.terms1
      (fun i => (H2WitnessFourteenChecks.terms1_admissible i).1)
      (fun i => (H2WitnessFourteenChecks.terms1_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessFourteen.w2 * _)
    rw [H2WitnessFourteenChecks.w2_entries]
    exact weighted_orbitals_mem_positiveRay hsource 14 2 (by decide) (by decide)
      H2WitnessFourteenChecks.terms2
      (fun i => (H2WitnessFourteenChecks.terms2_admissible i).1)
      (fun i => (H2WitnessFourteenChecks.terms2_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessFourteen.w3 * _)
    rw [H2WitnessFourteenChecks.w3_entries]
    exact weighted_orbitals_mem_positiveRay hsource 14 3 (by decide) (by decide)
      H2WitnessFourteenChecks.terms3
      (fun i => (H2WitnessFourteenChecks.terms3_admissible i).1)
      (fun i => (H2WitnessFourteenChecks.terms3_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessFourteen.w4 * _)
    rw [H2WitnessFourteenChecks.w4_entries]
    exact weighted_orbitals_mem_positiveRay hsource 14 4 (by decide) (by decide)
      H2WitnessFourteenChecks.terms4
      (fun i => (H2WitnessFourteenChecks.terms4_admissible i).1)
      (fun i => (H2WitnessFourteenChecks.terms4_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessFourteen.w5 * _)
    rw [H2WitnessFourteenChecks.w5_entries]
    exact weighted_orbitals_mem_positiveRay hsource 14 5 (by decide) (by decide)
      H2WitnessFourteenChecks.terms5
      (fun i => (H2WitnessFourteenChecks.terms5_admissible i).1)
      (fun i => (H2WitnessFourteenChecks.terms5_positive i).le)
      B hB Q c η hη (by omega)
  · change PositiveRay.Contains _ (aeval _ H2WitnessFourteen.w6 * _)
    rw [H2WitnessFourteenChecks.w6_entries]
    exact weighted_orbitals_mem_positiveRay hsource 14 6 (by decide) (by decide)
      H2WitnessFourteenChecks.terms6
      (fun i => (H2WitnessFourteenChecks.terms6_admissible i).1)
      (fun i => (H2WitnessFourteenChecks.terms6_positive i).le)
      B hB Q c η hη (by omega)

end
end QuaternionicSymmetry.H2OrbitalPointwise
