import QuaternionicSymmetry.OrbitalRealSquaredSpectrum
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Integral

/-! The closed real scalar-orbital cone in its finite Schur coordinate space. -/

namespace QuaternionicSymmetry.OrbitalRealCone

open Matrix OrbitalRealSquaredSpectrum OrbitalConjugateSchur
  OrbitalSymplecticSpectral QuaternionicMatrixModel MeasureTheory

noncomputable section

/-- The finite list of Schur shapes at weight `k`. -/
abbrev Shape (k : ℕ) :=
  {lam : List ℕ // lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset}

/-- Coordinate space of weight-`k` finite Schur expansions. -/
abbrev Coordinates (k : ℕ) := Shape k → ℝ

def generatorCoordinates (n k : ℕ) (a : Fin n → ℝ) : Coordinates k :=
  fun lam => (4 : ℝ) ^ k *
    (QuarticOrbitalEleven.factorialRho n lam.1 : ℝ) * squaredSchurValue a lam.1

def matrixCoordinates {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) : Coordinates k :=
  fun lam => (4 : ℝ) ^ k *
    (QuarticOrbitalEleven.factorialRho n lam.1 : ℝ) * matrixSchurValue B lam.1

/-- Reconstruction in the exact polynomial used by the Haar and Gaussian
arguments. The finite coordinate vector carries all spectrum dependence. -/
theorem finiteOrbitalPolynomial_eq_coordinates
    {β : Type*} [Fintype β] {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial B A k =
      ∑ lam : Shape k,
        MvPolynomial.C (matrixCoordinates B k lam) *
          MatrixTracePolynomial.schurPolynomial A lam.1 := by
  unfold OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial matrixCoordinates
  rw [Finset.mul_sum]
  simp only [← mul_assoc, ← map_mul]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro lam _
  simp [mul_assoc]

/-- The exact closed conical hull of all nonnegative real spectra. -/
def cone (n k : ℕ) : ConvexCone ℝ (Coordinates k) :=
  (ConvexCone.hull ℝ
    {v | ∃ a : Fin n → ℝ, (∀ i, 0 ≤ a i) ∧ v = generatorCoordinates n k a}).closure

theorem generator_mem_cone (n k : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) : generatorCoordinates n k a ∈ cone n k := by
  apply subset_closure
  apply ConvexCone.subset_hull
  exact ⟨a, ha, rfl⟩

theorem matrixCoordinates_eq_generator_of_diagonalization {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (x : Fin n → ℝ) (u : CompactSymplecticHaar.Group n)
    (hB : B = CompactSymplecticHaar.conjugate
      (CompactSymplecticHaar.standardJ n) u
      (OrbitalDiagonalSpectra.hermitianDiagonal x)) (k : ℕ) :
    matrixCoordinates B k = generatorCoordinates n k (fun i => x i ^ 2) := by
  funext lam
  simp [matrixCoordinates, generatorCoordinates, hB,
    matrixSchurValue_conjugate, matrixSchurValue_diagonal,
    squaredSchurValue_square]

theorem matrixCoordinates_mem_cone {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : HermitianAntiSelfDual B) (k : ℕ) :
    matrixCoordinates B k ∈ cone n k := by
  obtain ⟨x, u, hx⟩ := exists_symplectic_diagonalization hB
  rw [matrixCoordinates_eq_generator_of_diagonalization B x u hx k]
  exact generator_mem_cone n k _ (squaredSpectrum_nonneg x)

/-- Scalar coefficient integrability suffices for integrability of the
finite-dimensional intrinsic coordinate map. -/
theorem integrable_matrixCoordinates_of_schurValues
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n k : ℕ}
    (B : α → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (h : ∀ lam : Shape k,
      Integrable (fun t => matrixSchurValue (B t) lam.1) μ) :
    Integrable (fun t => matrixCoordinates (B t) k) μ := by
  apply Integrable.of_eval
  intro lam
  change Integrable (fun t =>
    (4 : ℝ) ^ k * (QuarticOrbitalEleven.factorialRho n lam.1 : ℝ) *
      matrixSchurValue (B t) lam.1) μ
  exact (h lam).const_mul _

theorem integral_matrixCoordinates_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n k : ℕ}
    (B : α → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hfi : Integrable (fun t => matrixCoordinates (B t) k) μ)
    (lam : Shape k) :
    (∫ t, matrixCoordinates (B t) k ∂μ) lam =
      ∫ t, (4 : ℝ) ^ k *
        (QuarticOrbitalEleven.factorialRho n lam.1 : ℝ) *
          matrixSchurValue (B t) lam.1 ∂μ := by
  rw [eval_integral (fun i => hfi.eval i)]
  rfl

/-- Every integrable probability mixture of intrinsic matrix coordinates
remains in the closed scalar-orbital cone. No eigenvalue selection occurs in
the integrand. -/
theorem integral_matrixCoordinates_mem_cone
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {n k : ℕ}
    (B : α → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : ∀ᵐ t ∂μ, HermitianAntiSelfDual (B t))
    (hfi : Integrable (fun t => matrixCoordinates (B t) k) μ) :
    (∫ t, matrixCoordinates (B t) k ∂μ) ∈ cone n k := by
  apply (ConvexCone.convex (cone n k)).integral_mem isClosed_closure
  · filter_upwards [hB] with t ht
    exact matrixCoordinates_mem_cone (B t) ht k
  · exact hfi

end
end QuaternionicSymmetry.OrbitalRealCone
