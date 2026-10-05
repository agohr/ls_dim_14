import QuaternionicSymmetry.SmoothTaylorSeries
import QuaternionicSymmetry.OrbitalOddFormalKernel
import Mathlib.Analysis.Complex.Trigonometric

/-! Exact Taylor coefficients of the actual real `2 sinh` determinant.
Every rational formal coefficient is identified with the derivative of the
smooth determinant divided by its factorial. This is an analytic-to-formal
bridge; equality of the determinant quotient with Haar integration is separate.
-/

namespace QuaternionicSymmetry.OrbitalAnalyticOddKernel

open Matrix SmoothTaylorSeries OrbitalOddFormalKernel

noncomputable section

def evaluation (t : ℝ) : Smooth →+* ℝ where
  toFun f := (f : ℝ → ℝ) t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def sourceKernel {n : ℕ} (x y : Fin n → ℚ) : Matrix (Fin n) (Fin n) Smooth :=
  Matrix.of fun i j => exponential ((x i : ℝ) * (y j : ℝ)) -
    exponential (-((x i : ℝ) * (y j : ℝ)))

def sourceDeterminant {n : ℕ} (x y : Fin n → ℚ) : Smooth := (sourceKernel x y).det

theorem sourceDeterminant_apply {n : ℕ} (x y : Fin n → ℚ) (t : ℝ) :
    (sourceDeterminant x y : ℝ → ℝ) t =
      (Matrix.of fun i j => 2 * Real.sinh ((x i : ℝ) * (y j : ℝ) * t)).det := by
  change evaluation t (sourceKernel x y).det = _
  rw [(evaluation t).map_det]
  congr 1
  ext i j
  change Real.exp ((x i : ℝ) * (y j : ℝ) * t) -
    Real.exp (-((x i : ℝ) * (y j : ℝ)) * t) = _
  rw [Matrix.of_apply, Real.sinh_eq]
  simp only [neg_mul]
  ring

theorem taylor_sourceKernel {n : ℕ} (x y : Fin n → ℚ) :
    taylorHom.mapMatrix (sourceKernel x y) =
      (PowerSeries.map (Rat.castHom ℝ)).mapMatrix (sourceFullFormalOddKernel x y) := by
  ext i j m
  change PowerSeries.coeff m (taylorHom
    (exponential ((x i : ℝ) * (y j : ℝ)) -
      exponential (-((x i : ℝ) * (y j : ℝ))))) = _
  rw [map_sub, taylor_exponential, taylor_exponential, map_sub]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    RingHom.mapMatrix_apply, Matrix.map_apply, PowerSeries.coeff_map,
    sourceFullFormalOddKernel, Matrix.smul_apply, smul_eq_mul,
    PowerSeries.coeff_C_mul, coeff_fullFormalOddKernel]
  simp only [map_mul, map_div₀, map_sub, map_pow, map_neg, map_one, map_ofNat,
    map_natCast, Rat.coe_castHom]
  rw [neg_pow]
  ring

theorem taylor_sourceDeterminant {n : ℕ} (x y : Fin n → ℚ) :
    taylorHom (sourceDeterminant x y) =
      PowerSeries.map (Rat.castHom ℝ) (sourceFullFormalOddKernel x y).det := by
  unfold sourceDeterminant
  rw [taylorHom.map_det, taylor_sourceKernel, ← RingHom.map_det]

/-- Every derivative, including all higher orbital weights, is exactly the
corresponding formal coefficient with the Taylor factorial. -/
theorem sourceDeterminant_taylor_coefficient {n : ℕ} (x y : Fin n → ℚ) (m : ℕ) :
    iteratedDeriv m (sourceDeterminant x y : ℝ → ℝ) 0 / (m.factorial : ℝ) =
      ((PowerSeries.coeff m (sourceFullFormalOddKernel x y).det : ℚ) : ℝ) := by
  have h := congrArg (PowerSeries.coeff m) (taylor_sourceDeterminant x y)
  simpa only [taylorHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_series, PowerSeries.coeff_map, Rat.coe_castHom] using h

end
end QuaternionicSymmetry.OrbitalAnalyticOddKernel
