import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

/-!
Coordinate exterior-algebra identities for four generators.  These are purely
algebraic statements in `ExteriorAlgebra ℝ (Fin 4 → ℝ)`; no differential forms,
curvature, or geometric positivity is used.
-/

namespace QuaternionicSymmetry.FourDimensionalForms

open ExteriorAlgebra

abbrev V := Fin 4 → ℝ
abbrev E := ExteriorAlgebra ℝ V

def e (k : Fin 4) : V := fun j => if j = k then 1 else 0

def g (k : Fin 4) : E := ExteriorAlgebra.ι ℝ (e k)

def e₀ : V := e 0
def e₁ : V := e 1
def e₂ : V := e 2
def e₃ : V := e 3

def α : E := g 0 * g 1 - g 2 * g 3
def ωI : E := g 0 * g 1 + g 2 * g 3
def ωJ : E := g 0 * g 2 - g 1 * g 3
def ωK : E := g 0 * g 3 + g 1 * g 2
def vol : E := g 0 * g 1 * g 2 * g 3

private theorem gen_sq (k : Fin 4) : g k * g k = 0 := by
  exact ExteriorAlgebra.ι_sq_zero (e k)

private theorem gen_swap (i j : Fin 4) :
    g i * g j = -(g j * g i) := by
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e i) (e j))

private theorem move_left (i j : Fin 4) (x : E) :
    g i * (g j * x) = -(g j * (g i * x)) := by
  rw [← mul_assoc, gen_swap i j]
  simp only [neg_mul, mul_assoc]

private theorem g₂g₃g₀g₁ :
    g 2 * g 3 * g 0 * g 1 = g 0 * g 1 * g 2 * g 3 := by
  calc
    g 2 * g 3 * g 0 * g 1 = g 2 * (g 3 * (g 0 * g 1)) := by simp [mul_assoc]
    _ = -(g 2 * (g 0 * (g 3 * g 1))) := by rw [move_left 3 0]; exact mul_neg _ _
    _ = g 0 * (g 2 * (g 3 * g 1)) := by rw [move_left 2 0]; simp
    _ = -(g 0 * (g 2 * (g 1 * g 3))) := by rw [gen_swap 3 1]; simp only [mul_neg]
    _ = g 0 * (g 1 * (g 2 * g 3)) := by rw [move_left 2 1]; simp only [mul_neg, neg_neg]
    _ = g 0 * g 1 * g 2 * g 3 := by simp [mul_assoc]

private theorem pair_sq (i j : Fin 4) :
    (g i * g j) * (g i * g j) = 0 := by
  calc
    (g i * g j) * (g i * g j) = g i * (g j * (g i * g j)) := by simp [mul_assoc]
    _ = -(g i * (g i * (g j * g j))) := by rw [move_left j i]; simp only [mul_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem g₀g₂g₁g₃ :
    g 0 * g 2 * g 1 * g 3 = -(g 0 * g 1 * g 2 * g 3) := by
  calc
    g 0 * g 2 * g 1 * g 3 = g 0 * (g 2 * (g 1 * g 3)) := by simp [mul_assoc]
    _ = -(g 0 * (g 1 * (g 2 * g 3))) := by rw [move_left 2 1]; exact mul_neg _ _
    _ = -(g 0 * g 1 * g 2 * g 3) := by simp [mul_assoc]

private theorem g₁g₃g₀g₂ :
    g 1 * g 3 * g 0 * g 2 = -(g 0 * g 1 * g 2 * g 3) := by
  calc
    g 1 * g 3 * g 0 * g 2 = g 1 * (g 3 * (g 0 * g 2)) := by simp [mul_assoc]
    _ = -(g 1 * (g 0 * (g 3 * g 2))) := by rw [move_left 3 0]; exact mul_neg _ _
    _ = g 0 * (g 1 * (g 3 * g 2)) := by rw [move_left 1 0]; simp
    _ = -(g 0 * (g 1 * (g 2 * g 3))) := by rw [gen_swap 3 2]; simp only [mul_neg]
    _ = -(g 0 * g 1 * g 2 * g 3) := by simp [mul_assoc]

private theorem g₀g₃g₁g₂ :
    g 0 * g 3 * g 1 * g 2 = g 0 * g 1 * g 2 * g 3 := by
  calc
    g 0 * g 3 * g 1 * g 2 = g 0 * (g 3 * (g 1 * g 2)) := by simp [mul_assoc]
    _ = -(g 0 * (g 1 * (g 3 * g 2))) := by rw [move_left 3 1]; exact mul_neg _ _
    _ = g 0 * (g 1 * (g 2 * g 3)) := by rw [gen_swap 3 2]; simp only [mul_neg, neg_neg]
    _ = g 0 * g 1 * g 2 * g 3 := by simp [mul_assoc]

private theorem g₁g₂g₀g₃ :
    g 1 * g 2 * g 0 * g 3 = g 0 * g 1 * g 2 * g 3 := by
  calc
    g 1 * g 2 * g 0 * g 3 = g 1 * (g 2 * (g 0 * g 3)) := by simp [mul_assoc]
    _ = -(g 1 * (g 0 * (g 2 * g 3))) := by rw [move_left 2 0]; exact mul_neg _ _
    _ = g 0 * (g 1 * (g 2 * g 3)) := by rw [move_left 1 0]; simp
    _ = g 0 * g 1 * g 2 * g 3 := by simp [mul_assoc]

theorem alpha_sq : α ^ 2 = -(2 : ℝ) • vol := by
  simp only [α, pow_two]
  have h01 : (g 0 * g 1) * (g 0 * g 1) = 0 := by
    calc
      (g 0 * g 1) * (g 0 * g 1) = g 0 * (g 1 * (g 0 * g 1)) := by simp [mul_assoc]
      _ = -(g 0 * (g 0 * (g 1 * g 1))) := by rw [move_left 1 0]; simp only [mul_neg]
      _ = 0 := by rw [← mul_assoc, gen_sq 0]; simp
  have h23 : (g 2 * g 3) * (g 2 * g 3) = 0 := by
    calc
      (g 2 * g 3) * (g 2 * g 3) = g 2 * (g 3 * (g 2 * g 3)) := by simp [mul_assoc]
      _ = -(g 2 * (g 2 * (g 3 * g 3))) := by rw [move_left 3 2]; simp only [mul_neg]
      _ = 0 := by rw [← mul_assoc, gen_sq 2]; simp
  have hcross : g 2 * g 3 * (g 0 * g 1) = g 0 * g 1 * g 2 * g 3 := by
    simpa [mul_assoc] using g₂g₃g₀g₁
  calc
    (g 0 * g 1 - g 2 * g 3) * (g 0 * g 1 - g 2 * g 3) =
        (g 0 * g 1) * (g 0 * g 1) - (g 0 * g 1) * (g 2 * g 3)
          - (g 2 * g 3) * (g 0 * g 1) + (g 2 * g 3) * (g 2 * g 3) := by
      noncomm_ring
    _ = -(2 : ℝ) • vol := by
      rw [h01, h23, hcross]
      have hv : g 0 * g 1 * (g 2 * g 3) = vol := by simp [vol, mul_assoc]
      have hv2 : g 0 * g 1 * g 2 * g 3 = vol := by simp [vol, mul_assoc]
      rw [hv, hv2, Algebra.smul_def]
      rw [show (algebraMap ℝ E) (-2) = -2 by
        rw [map_neg, map_ofNat]]
      simp
      rw [two_mul]
      abel

theorem scaled_alpha_sq (c : ℝ) : (c • α) ^ 2 = -(2 * c ^ 2) • vol := by
  calc
    (c • α) ^ 2 = c • (α * (c • α)) := by rw [pow_two, smul_mul_assoc]
    _ = c • (c • (α * α)) := by rw [mul_smul_comm]
    _ = (c * c) • (α * α) := by rw [smul_smul]
    _ = (c * c) • (-(2 : ℝ) • vol) := by rw [← pow_two α, alpha_sq]
    _ = -(2 * c ^ 2) • vol := by
      rw [smul_smul]
      rw [show c * c * (-2 : ℝ) = -(2 * c ^ 2) by ring]

theorem omega_sum_sq : ωI ^ 2 + ωJ ^ 2 + ωK ^ 2 = (6 : ℝ) • vol := by
  simp only [ωI, ωJ, ωK, pow_two]
  calc
    (g 0 * g 1 + g 2 * g 3) * (g 0 * g 1 + g 2 * g 3) +
        (g 0 * g 2 - g 1 * g 3) * (g 0 * g 2 - g 1 * g 3) +
        (g 0 * g 3 + g 1 * g 2) * (g 0 * g 3 + g 1 * g 2) =
      ((g 0 * g 1) * (g 0 * g 1) + (g 0 * g 1) * (g 2 * g 3) +
          (g 2 * g 3) * (g 0 * g 1) + (g 2 * g 3) * (g 2 * g 3)) +
        ((g 0 * g 2) * (g 0 * g 2) - (g 0 * g 2) * (g 1 * g 3) -
          (g 1 * g 3) * (g 0 * g 2) + (g 1 * g 3) * (g 1 * g 3)) +
        ((g 0 * g 3) * (g 0 * g 3) + (g 0 * g 3) * (g 1 * g 2) +
          (g 1 * g 2) * (g 0 * g 3) + (g 1 * g 2) * (g 1 * g 2)) := by
      noncomm_ring
    _ = (6 : ℝ) • vol := by
      rw [pair_sq 0 1, pair_sq 2 3, pair_sq 0 2, pair_sq 1 3,
        pair_sq 0 3, pair_sq 1 2]
      have hcross : g 2 * g 3 * (g 0 * g 1) = vol := by
        simpa [mul_assoc, vol] using g₂g₃g₀g₁
      have h02 : g 0 * g 2 * (g 1 * g 3) = -vol := by
        simpa [mul_assoc, vol] using g₀g₂g₁g₃
      have h13 : g 1 * g 3 * (g 0 * g 2) = -vol := by
        simpa [mul_assoc, vol] using g₁g₃g₀g₂
      have h03 : g 0 * g 3 * (g 1 * g 2) = vol := by
        simpa [mul_assoc, vol] using g₀g₃g₁g₂
      have h12 : g 1 * g 2 * (g 0 * g 3) = vol := by
        simpa [mul_assoc, vol] using g₁g₂g₀g₃
      rw [hcross, h02, h13, h03, h12]
      have hv : g 0 * g 1 * (g 2 * g 3) = vol := by simp [vol, mul_assoc]
      rw [hv]
      rw [Algebra.smul_def]
      rw [show (algebraMap ℝ E) 6 = 6 by exact map_ofNat _ _]
      have h6 : (6 : E) = 1 + 1 + 1 + 1 + 1 + 1 := by norm_num
      rw [h6]
      simp only [one_mul, add_mul]
      abel

end QuaternionicSymmetry.FourDimensionalForms
