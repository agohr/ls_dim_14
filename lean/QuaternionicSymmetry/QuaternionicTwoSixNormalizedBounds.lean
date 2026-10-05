import QuaternionicSymmetry.QuaternionicTwoSixDensityBound
import QuaternionicSymmetry.QuaternionicTwoSixDensityScaling

/-! Scalar-curvature normalized pointwise bounds for the printed dimensions
two through six. -/
namespace QuaternionicSymmetry.QuaternionicTwoSixNormalizedBounds
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
open PrintedProjectionCubicPositivity QuaternionicNormalizedDensityValues
open QuaternionicTwoSixDensityScaling QuaternionicTwoSixDensityBound
open PrintedTwoSixLinearAssembly ReconstructionExamples
noncomputable section
set_option synthInstance.maxHeartbeats 200000

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
local instance : CommRing (CE V) := inferInstance
local instance : Algebra ℝ (CE V) := inferInstance
local instance : IsScalarTower ℝ (CE V) (CE V) := inferInstance

private theorem hermitian_real_smul {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : B.IsHermitian) (r : ℝ) : (r • B).IsHermitian := by
  change Matrix.conjTranspose (r • B) = r • B
  rw [Matrix.conjTranspose_smul, hB]
  simp

omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem density2_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (η : β → E V) (L : CE V →ₗ[ℝ] ℝ) :
    16 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 2) ≤
      L (aeval (normalizedValues Q b s B η) density2) := by
  have hp := density2_lower_bound Q b (fun a => s⁻¹ • B a) η L
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 4)
  rw [normalized_density2 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring


theorem density3_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 3) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    32 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 3) ≤
      L (aeval (normalizedValues Q b s B η) density3) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density3_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 6)
  rw [normalized_density3 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

theorem density4_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 4) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    48 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 4) ≤
      L (aeval (normalizedValues Q b s B η) density4) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density4_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 8)
  rw [normalized_density4 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

theorem density5_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 5) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    72 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 5) ≤
      L (aeval (normalizedValues Q b s B η) k5) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density5_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 10)
  rw [normalized_k5 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

theorem density6_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 6) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    96 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 6) ≤
      L (aeval (normalizedValues Q b s B η) k6) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density6_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 12)
  rw [normalized_k6 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

end
end QuaternionicSymmetry.QuaternionicTwoSixNormalizedBounds
