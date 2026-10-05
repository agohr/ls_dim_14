import QuaternionicSymmetry.QuaternionicSevenTenDensityBound
import QuaternionicSymmetry.QuaternionicSevenTenDensityScaling

/-! The dimension seven through ten pointwise density inequalities after the
scalar-curvature normalization used by the actual KSW source forms. -/
namespace QuaternionicSymmetry.QuaternionicSevenTenNormalizedBounds
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
open PrintedProjectionCubicPositivity QuaternionicNormalizedDensityValues
open QuaternionicSevenTenDensityScaling QuaternionicSevenTenDensityBound
open PrintedCertificatesSevenTen
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

theorem density7_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 7) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 7 ⊕ Fin 7) (Fin 7 ⊕ Fin 7) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    128 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 7) ≤
      L (aeval (normalizedValues Q b s B η) rhs7) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density7_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 14)
  rw [normalized_rhs7 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

theorem density8_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 8) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    160 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 8) ≤
      L (aeval (normalizedValues Q b s B η) rhs8) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density8_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 16)
  rw [normalized_rhs8 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

theorem density9_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 9) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 9 ⊕ Fin 9) (Fin 9 ⊕ Fin 9) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    200 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 9) ≤
      L (aeval (normalizedValues Q b s B η) rhs9) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density9_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 18)
  rw [normalized_rhs9 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

theorem density10_lower_bound_normalized
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 10) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 10 ⊕ Fin 10) (Fin 10 ⊕ Fin 10) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    240 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 10) ≤
      L (aeval (normalizedValues Q b s B η) rhs10) := by
  have hBs (a : β) : (s⁻¹ • B a).IsHermitian :=
    hermitian_real_smul (B a) (hB a) s⁻¹
  have hp := density10_lower_bound Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 20)
  rw [normalized_rhs10 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1; ring

end
end QuaternionicSymmetry.QuaternionicSevenTenNormalizedBounds
