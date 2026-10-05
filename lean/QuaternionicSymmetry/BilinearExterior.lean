import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Real bilinear two-forms represented in the actual exterior algebra of the dual.

The finite-basis construction below is verified through the canonical exterior
pairing. Its skew case recovers the original bilinear form, with the factor of
one half fixed explicitly.
-/

namespace QuaternionicSymmetry.BilinearExterior

open Module
open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

def ofBilinear (b : Basis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  ∑ i, ∑ j, (B (b i) (b j) / 2) •
    exteriorPower.ιMulti ℝ 2 ![b.coord i, b.coord j]

/-- The exterior representative depends linearly on the bilinear form. -/
def ofBilinearLinear (b : Basis ι ℝ V) :
    (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ]
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) where
  toFun := ofBilinear b
  map_add' B C := by
    simp [ofBilinear, add_div, add_smul, Finset.sum_add_distrib]
  map_smul' r B := by
    simp [ofBilinear, Finset.smul_sum, smul_smul, mul_div_assoc]

@[simp] theorem ofBilinearLinear_apply (b : Basis ι ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ofBilinearLinear b B = ofBilinear b B := rfl

def evaluate (v w : V) :
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) →ₗ[ℝ] ℝ :=
  (LinearMap.applyₗ (exteriorPower.ιMulti ℝ 2 ![v, w])).comp
    (exteriorPower.pairingDual ℝ V 2)

@[simp] theorem evaluate_wedge (v w : V) (f g : Module.Dual ℝ V) :
    evaluate v w (exteriorPower.ιMulti ℝ 2 ![f, g]) = f v * g w - g v * f w := by
  simp [evaluate, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]

private theorem basis_expansion (b : Basis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : V) :
    B v w = ∑ i, ∑ j, B (b i) (b j) * (b.coord i v * b.coord j w) := by
  have hv : (∑ i, b.coord i v • b i) = v := b.sum_repr v
  have hw : (∑ i, b.coord i w • b i) = w := b.sum_repr w
  conv_lhs => rw [← hv, ← hw]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exterior evaluation extracts precisely the alternating part of a bilinear form. -/
theorem evaluate_ofBilinear (b : Basis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : V) :
    evaluate v w (ofBilinear b B) = (B v w - B w v) / 2 := by
  simp only [ofBilinear, map_sum, map_smul, smul_eq_mul, evaluate_wedge]
  rw [basis_expansion b B v w, basis_expansion b B w v]
  simp only [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A skew bilinear form is recovered exactly, rather than only up to normalization. -/
theorem evaluate_of_skew (b : Basis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h : ∀ v w, B v w = -B w v) (v w : V) :
    evaluate v w (ofBilinear b B) = B v w := by
  rw [evaluate_ofBilinear, h w v]
  ring

end
end QuaternionicSymmetry.BilinearExterior
