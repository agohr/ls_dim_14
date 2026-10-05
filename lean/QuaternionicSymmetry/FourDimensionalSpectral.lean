import QuaternionicSymmetry.FourDimensionalOrientation
import QuaternionicSymmetry.EvenForms
import Mathlib.Tactic.NoncommRing

/-!
Explicit three-parameter exterior-algebra calculation in oriented dimension four.
The forms below are concrete coordinate expressions in the actual exterior
algebra.  The resulting quadratic identity is algebraic; it does not invoke a
spectral theorem or identify a geometric Lie algebra.
-/

namespace QuaternionicSymmetry.FourDimensionalSpectral

open QuaternionicSymmetry.FourDimensionalForms
open ExteriorAlgebra

abbrev V := QuaternionicSymmetry.FourDimensionalForms.V
abbrev E := QuaternionicSymmetry.FourDimensionalForms.E

/-- The other two coordinate anti-self-dual two-forms. -/
def αJ : E := g 0 * g 2 + g 1 * g 3
def αK : E := g 0 * g 3 - g 1 * g 2

private theorem gen_sq (k : Fin 4) : g k * g k = 0 := by
  exact ExteriorAlgebra.ι_sq_zero (e k)

private theorem gen_swap (i j : Fin 4) :
    g i * g j = -(g j * g i) := by
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e i) (e j))

private theorem move_left (i j : Fin 4) (x : E) :
    g i * (g j * x) = -(g j * (g i * x)) := by
  rw [← mul_assoc, gen_swap i j]
  simp only [neg_mul, mul_assoc]

private theorem pair_sq (i j : Fin 4) :
    (g i * g j) * (g i * g j) = 0 := by
  calc
    (g i * g j) * (g i * g j) = g i * (g j * (g i * g j)) := by simp [mul_assoc]
    _ = -(g i * (g i * (g j * g j))) := by
      rw [move_left j i]
      simp only [mul_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem zero_ijik (i j k : Fin 4) :
    (g i * g j) * (g i * g k) = 0 := by
  calc
    (g i * g j) * (g i * g k) = g i * (g j * (g i * g k)) := by simp [mul_assoc]
    _ = -(g i * (g i * (g j * g k))) := by
      rw [move_left j i]
      simp only [mul_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem zero_ijjk (i j k : Fin 4) :
    (g i * g j) * (g j * g k) = 0 := by
  calc
    (g i * g j) * (g j * g k) = g i * (g j * (g j * g k)) := by simp [mul_assoc]
    _ = 0 := by
      rw [← mul_assoc (g j) (g j) (g k), gen_sq j]
      simp

private theorem zero_ijki (i j k : Fin 4) :
    (g i * g j) * (g k * g i) = 0 := by
  calc
    (g i * g j) * (g k * g i) = g i * (g j * (g k * g i)) := by simp [mul_assoc]
    _ = -(g i * (g j * (g i * g k))) := by
      rw [gen_swap k i]
      simp only [mul_neg]
    _ = g i * (g i * (g j * g k)) := by
      rw [move_left j i]
      simp only [mul_neg, neg_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem zero_ijkj (i j k : Fin 4) :
    (g i * g j) * (g k * g j) = 0 := by
  calc
    (g i * g j) * (g k * g j) = g i * (g j * (g k * g j)) := by simp [mul_assoc]
    _ = -(g i * (g j * (g j * g k))) := by
      rw [gen_swap k j]
      simp only [mul_neg]
    _ = 0 := by
      rw [← mul_assoc (g j) (g j) (g k), gen_sq j]
      simp

private theorem perm_2301 : (g 2 * g 3) * (g 0 * g 1) = vol := by
  calc
    (g 2 * g 3) * (g 0 * g 1) = g 2 * (g 3 * (g 0 * g 1)) := by simp [mul_assoc]
    _ = -(g 2 * (g 0 * (g 3 * g 1))) := by rw [move_left 3 0]; simp only [mul_neg]
    _ = g 0 * (g 2 * (g 3 * g 1)) := by rw [move_left 2 0]; simp
    _ = -(g 0 * (g 2 * (g 1 * g 3))) := by rw [gen_swap 3 1]; simp only [mul_neg]
    _ = g 0 * (g 1 * (g 2 * g 3)) := by rw [move_left 2 1]; simp only [mul_neg, neg_neg]
    _ = vol := by simp [vol, mul_assoc]

private theorem perm_0213 : (g 0 * g 2) * (g 1 * g 3) = -vol := by
  calc
    (g 0 * g 2) * (g 1 * g 3) = g 0 * (g 2 * (g 1 * g 3)) := by simp [mul_assoc]
    _ = -(g 0 * (g 1 * (g 2 * g 3))) := by rw [move_left 2 1]; simp only [mul_neg]
    _ = -vol := by simp [vol, mul_assoc]

private theorem perm_1302 : (g 1 * g 3) * (g 0 * g 2) = -vol := by
  calc
    (g 1 * g 3) * (g 0 * g 2) = g 1 * (g 3 * (g 0 * g 2)) := by simp [mul_assoc]
    _ = -(g 1 * (g 0 * (g 3 * g 2))) := by rw [move_left 3 0]; simp only [mul_neg]
    _ = g 0 * (g 1 * (g 3 * g 2)) := by rw [move_left 1 0]; simp
    _ = -(g 0 * (g 1 * (g 2 * g 3))) := by rw [gen_swap 3 2]; simp only [mul_neg]
    _ = -vol := by simp [vol, mul_assoc]

private theorem perm_0312 : (g 0 * g 3) * (g 1 * g 2) = vol := by
  calc
    (g 0 * g 3) * (g 1 * g 2) = g 0 * (g 3 * (g 1 * g 2)) := by simp [mul_assoc]
    _ = -(g 0 * (g 1 * (g 3 * g 2))) := by rw [move_left 3 1]; simp only [mul_neg]
    _ = g 0 * (g 1 * (g 2 * g 3)) := by rw [gen_swap 3 2]; simp only [mul_neg, neg_neg]
    _ = vol := by simp [vol, mul_assoc]

private theorem perm_1203 : (g 1 * g 2) * (g 0 * g 3) = vol := by
  calc
    (g 1 * g 2) * (g 0 * g 3) = g 1 * (g 2 * (g 0 * g 3)) := by simp [mul_assoc]
    _ = -(g 1 * (g 0 * (g 2 * g 3))) := by rw [move_left 2 0]; simp only [mul_neg]
    _ = g 0 * (g 1 * (g 2 * g 3)) := by rw [move_left 1 0]; simp
    _ = vol := by simp [vol, mul_assoc]

private theorem alphaJ_sq : αJ ^ 2 = -(2 : ℝ) • vol := by
  simp only [αJ, pow_two]
  calc
    (g 0 * g 2 + g 1 * g 3) * (g 0 * g 2 + g 1 * g 3) =
        (g 0 * g 2) * (g 0 * g 2) + (g 0 * g 2) * (g 1 * g 3) +
          (g 1 * g 3) * (g 0 * g 2) + (g 1 * g 3) * (g 1 * g 3) := by
      noncomm_ring
    _ = -(2 : ℝ) • vol := by
      rw [pair_sq 0 2, pair_sq 1 3, perm_0213, perm_1302]
      rw [Algebra.smul_def]
      rw [show (algebraMap ℝ E) (-2) = -2 by rw [map_neg, map_ofNat]]
      simp [two_mul]

private theorem alphaK_sq : αK ^ 2 = -(2 : ℝ) • vol := by
  simp only [αK, pow_two]
  calc
    (g 0 * g 3 - g 1 * g 2) * (g 0 * g 3 - g 1 * g 2) =
        (g 0 * g 3) * (g 0 * g 3) - (g 0 * g 3) * (g 1 * g 2) -
          (g 1 * g 2) * (g 0 * g 3) + (g 1 * g 2) * (g 1 * g 2) := by
      noncomm_ring
    _ = -(2 : ℝ) • vol := by
      rw [pair_sq 0 3, pair_sq 1 2, perm_0312, perm_1203]
      rw [Algebra.smul_def]
      rw [show (algebraMap ℝ E) (-2) = -2 by rw [map_neg, map_ofNat]]
      simp [two_mul]
      abel

private theorem alpha_alphaJ : α * αJ = 0 := by
  simp only [α, αJ]
  calc
    (g 0 * g 1 - g 2 * g 3) * (g 0 * g 2 + g 1 * g 3) =
        (g 0 * g 1) * (g 0 * g 2) + (g 0 * g 1) * (g 1 * g 3) -
          (g 2 * g 3) * (g 0 * g 2) - (g 2 * g 3) * (g 1 * g 3) := by
      noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 1 2, zero_ijjk 0 1 3,
        zero_ijki 2 3 0, zero_ijkj 2 3 1]
      simp

private theorem alphaJ_alpha : αJ * α = 0 := by
  simp only [α, αJ]
  calc
    (g 0 * g 2 + g 1 * g 3) * (g 0 * g 1 - g 2 * g 3) =
        (g 0 * g 2) * (g 0 * g 1) - (g 0 * g 2) * (g 2 * g 3) +
          (g 1 * g 3) * (g 0 * g 1) - (g 1 * g 3) * (g 2 * g 3) := by
      noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 2 1, zero_ijjk 0 2 3,
        zero_ijki 1 3 0, zero_ijkj 1 3 2]
      simp

private theorem alpha_alphaK : α * αK = 0 := by
  simp only [α, αK]
  calc
    (g 0 * g 1 - g 2 * g 3) * (g 0 * g 3 - g 1 * g 2) =
        (g 0 * g 1) * (g 0 * g 3) - (g 0 * g 1) * (g 1 * g 2) -
          (g 2 * g 3) * (g 0 * g 3) + (g 2 * g 3) * (g 1 * g 2) := by
      noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 1 3, zero_ijjk 0 1 2,
        zero_ijkj 2 3 0, zero_ijki 2 3 1]
      simp

private theorem alphaK_alpha : αK * α = 0 := by
  simp only [α, αK]
  calc
    (g 0 * g 3 - g 1 * g 2) * (g 0 * g 1 - g 2 * g 3) =
        (g 0 * g 3) * (g 0 * g 1) - (g 0 * g 3) * (g 2 * g 3) -
          (g 1 * g 2) * (g 0 * g 1) + (g 1 * g 2) * (g 2 * g 3) := by
      noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 3 1, zero_ijkj 0 3 2,
        zero_ijki 1 2 0, zero_ijjk 1 2 3]
      simp

private theorem alphaJ_alphaK : αJ * αK = 0 := by
  simp only [αJ, αK]
  calc
    (g 0 * g 2 + g 1 * g 3) * (g 0 * g 3 - g 1 * g 2) =
        (g 0 * g 2) * (g 0 * g 3) - (g 0 * g 2) * (g 1 * g 2) +
          (g 1 * g 3) * (g 0 * g 3) - (g 1 * g 3) * (g 1 * g 2) := by
      noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 2 3, zero_ijkj 0 2 1,
        zero_ijkj 1 3 0, zero_ijik 1 3 2]
      simp

private theorem alphaK_alphaJ : αK * αJ = 0 := by
  simp only [αJ, αK]
  calc
    (g 0 * g 3 - g 1 * g 2) * (g 0 * g 2 + g 1 * g 3) =
        (g 0 * g 3) * (g 0 * g 2) + (g 0 * g 3) * (g 1 * g 3) -
          (g 1 * g 2) * (g 0 * g 2) - (g 1 * g 2) * (g 1 * g 3) := by
      noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 3 2, zero_ijkj 0 3 1,
        zero_ijkj 1 2 0, zero_ijik 1 2 3]
      simp

private theorem square_add_three (x y z : E)
    (hxy : x * y = 0) (hyx : y * x = 0)
    (hxz : x * z = 0) (hzx : z * x = 0)
    (hyz : y * z = 0) (hzy : z * y = 0) :
    (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [pow_two]
  calc
    (x + y + z) * (x + y + z) =
        x * x + x * y + x * z + y * x + y * y + y * z + z * x + z * y + z * z := by
      noncomm_ring
    _ = x ^ 2 + y ^ 2 + z ^ 2 := by
      rw [hxy, hxz, hyx, hyz, hzx, hzy]
      simp [pow_two, add_assoc]

/-- The square of a scalar combination of the three coordinate forms. -/
theorem anti_self_dual_sq (a b c : ℝ) :
    (a • α + b • αJ + c • αK) ^ 2 =
      -(2 * (a ^ 2 + b ^ 2 + c ^ 2)) • vol := by
  have hA : (a • α) ^ 2 = -(2 * a ^ 2) • vol := by
    exact scaled_alpha_sq a
  have hB : (b • αJ) ^ 2 = -(2 * b ^ 2) • vol := by
    rw [pow_two, smul_mul_smul, ← pow_two αJ, alphaJ_sq]
    rw [smul_smul]
    congr 1
    ring
  have hC : (c • αK) ^ 2 = -(2 * c ^ 2) • vol := by
    rw [pow_two, smul_mul_smul, ← pow_two αK, alphaK_sq]
    rw [smul_smul]
    congr 1
    ring
  have hAB : (a • α) * (b • αJ) = 0 := by
    rw [smul_mul_smul, alpha_alphaJ, smul_zero]
  have hBA : (b • αJ) * (a • α) = 0 := by
    rw [smul_mul_smul, alphaJ_alpha, smul_zero]
  have hAC : (a • α) * (c • αK) = 0 := by
    rw [smul_mul_smul, alpha_alphaK, smul_zero]
  have hCA : (c • αK) * (a • α) = 0 := by
    rw [smul_mul_smul, alphaK_alpha, smul_zero]
  have hBC : (b • αJ) * (c • αK) = 0 := by
    rw [smul_mul_smul, alphaJ_alphaK, smul_zero]
  have hCB : (c • αK) * (b • αJ) = 0 := by
    rw [smul_mul_smul, alphaK_alphaJ, smul_zero]
  calc
    (a • α + b • αJ + c • αK) ^ 2 =
        (a • α) ^ 2 + (b • αJ) ^ 2 + (c • αK) ^ 2 :=
      square_add_three _ _ _ hAB hBA hAC hCA hBC hCB
    _ = -(2 * (a ^ 2 + b ^ 2 + c ^ 2)) • vol := by
      rw [hA, hB, hC]
      rw [← add_smul, ← add_smul]
      congr 1
      ring

/-- The signed top-degree coefficient of every such square is nonnegative. -/
theorem anti_self_dual_volume_nonneg (a b c : ℝ) :
    0 ≤ volumeCoefficient (-((a • α + b • αJ + c • αK) ^ 2)) := by
  rw [anti_self_dual_sq, map_neg, map_smul, volumeCoefficient_vol]
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have hs : 0 ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by nlinarith
  simpa [smul_eq_mul] using hs

end QuaternionicSymmetry.FourDimensionalSpectral
