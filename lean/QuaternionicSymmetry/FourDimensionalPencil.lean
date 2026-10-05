import QuaternionicSymmetry.FourDimensionalDegree
import QuaternionicSymmetry.EvenForms
import Mathlib.Tactic.NoncommRing

/-!
  The four-dimensional quaternionic pencil in the actual exterior algebra.

  The calculation is coordinate exterior algebra on four real generators.  No
  spectral theorem, positivity statement, or geometric realization is used.
-/

namespace QuaternionicSymmetry.FourDimensionalPencil

open QuaternionicSymmetry.FourDimensionalForms
open ExteriorAlgebra

abbrev V := QuaternionicSymmetry.FourDimensionalForms.V
abbrev E := QuaternionicSymmetry.FourDimensionalForms.E

private theorem gen_sq (k : Fin 4) : g k * g k = 0 :=
  ExteriorAlgebra.ι_sq_zero (e k)

private theorem gen_swap (i j : Fin 4) : g i * g j = -(g j * g i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e i) (e j))

private theorem move_left (i j : Fin 4) (x : E) :
    g i * (g j * x) = -(g j * (g i * x)) := by
  rw [← mul_assoc, gen_swap i j]
  simp only [neg_mul, mul_assoc]

private theorem pair_sq (i j : Fin 4) : (g i * g j) * (g i * g j) = 0 := by
  calc
    (g i * g j) * (g i * g j) = g i * (g j * (g i * g j)) := by simp [mul_assoc]
    _ = -(g i * (g i * (g j * g j))) := by rw [move_left j i]; simp only [mul_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem zero_ijik (i j k : Fin 4) : (g i * g j) * (g i * g k) = 0 := by
  calc
    (g i * g j) * (g i * g k) = g i * (g j * (g i * g k)) := by simp [mul_assoc]
    _ = -(g i * (g i * (g j * g k))) := by rw [move_left j i]; simp only [mul_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem zero_ijjk (i j k : Fin 4) : (g i * g j) * (g j * g k) = 0 := by
  calc
    (g i * g j) * (g j * g k) = g i * (g j * (g j * g k)) := by simp [mul_assoc]
    _ = 0 := by rw [← mul_assoc (g j) (g j) (g k), gen_sq j]; simp

private theorem zero_ijki (i j k : Fin 4) : (g i * g j) * (g k * g i) = 0 := by
  calc
    (g i * g j) * (g k * g i) = g i * (g j * (g k * g i)) := by simp [mul_assoc]
    _ = -(g i * (g j * (g i * g k))) := by rw [gen_swap k i]; simp only [mul_neg]
    _ = g i * (g i * (g j * g k)) := by rw [move_left j i]; simp only [mul_neg, neg_neg]
    _ = 0 := by rw [← mul_assoc, gen_sq i]; simp

private theorem zero_ijkj (i j k : Fin 4) : (g i * g j) * (g k * g j) = 0 := by
  calc
    (g i * g j) * (g k * g j) = g i * (g j * (g k * g j)) := by simp [mul_assoc]
    _ = -(g i * (g j * (g j * g k))) := by rw [gen_swap k j]; simp only [mul_neg]
    _ = 0 := by rw [← mul_assoc (g j) (g j) (g k), gen_sq j]; simp

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

theorem omegaI_sq : ωI ^ 2 = (2 : ℝ) • vol := by
  simp only [ωI, pow_two]
  calc
    (g 0 * g 1 + g 2 * g 3) * (g 0 * g 1 + g 2 * g 3) =
        (g 0 * g 1) * (g 0 * g 1) + (g 0 * g 1) * (g 2 * g 3) +
          (g 2 * g 3) * (g 0 * g 1) + (g 2 * g 3) * (g 2 * g 3) := by noncomm_ring
    _ = (2 : ℝ) • vol := by
      rw [pair_sq 0 1, pair_sq 2 3, perm_2301]
      have h : (g 0 * g 1) * (g 2 * g 3) = vol := by simp [vol, mul_assoc]
      rw [h, Algebra.smul_def, show (algebraMap ℝ E) 2 = 2 by exact map_ofNat _ _]
      simp [two_mul]

theorem omegaJ_sq : ωJ ^ 2 = (2 : ℝ) • vol := by
  simp only [ωJ, pow_two]
  calc
    (g 0 * g 2 - g 1 * g 3) * (g 0 * g 2 - g 1 * g 3) =
        (g 0 * g 2) * (g 0 * g 2) - (g 0 * g 2) * (g 1 * g 3) -
          (g 1 * g 3) * (g 0 * g 2) + (g 1 * g 3) * (g 1 * g 3) := by noncomm_ring
    _ = (2 : ℝ) • vol := by
      rw [pair_sq 0 2, pair_sq 1 3, perm_0213, perm_1302]
      rw [Algebra.smul_def, show (algebraMap ℝ E) 2 = 2 by exact map_ofNat _ _]
      simp [two_mul]

theorem omegaK_sq : ωK ^ 2 = (2 : ℝ) • vol := by
  simp only [ωK, pow_two]
  calc
    (g 0 * g 3 + g 1 * g 2) * (g 0 * g 3 + g 1 * g 2) =
        (g 0 * g 3) * (g 0 * g 3) + (g 0 * g 3) * (g 1 * g 2) +
          (g 1 * g 2) * (g 0 * g 3) + (g 1 * g 2) * (g 1 * g 2) := by noncomm_ring
    _ = (2 : ℝ) • vol := by
      rw [pair_sq 0 3, pair_sq 1 2, perm_0312, perm_1203]
      rw [Algebra.smul_def, show (algebraMap ℝ E) 2 = 2 by exact map_ofNat _ _]
      simp [two_mul]

private theorem two_forms_commute (x y : E)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℝ 2 V)
    (hy : y ∈ ExteriorAlgebra.exteriorPower ℝ 2 V) : x * y = y * x := by
  let x' := EvenForms.ofTwoForm ⟨x, hx⟩
  let y' := EvenForms.ofTwoForm ⟨y, hy⟩
  exact congrArg (fun z : EvenForms.evenSubalgebra ℝ V => (z : E)) (mul_comm x' y')

theorem alpha_omegaI : α * ωI = 0 := by
  simp only [α, ωI]
  calc
    (g 0 * g 1 - g 2 * g 3) * (g 0 * g 1 + g 2 * g 3) =
        (g 0 * g 1) * (g 0 * g 1) + (g 0 * g 1) * (g 2 * g 3) -
          (g 2 * g 3) * (g 0 * g 1) - (g 2 * g 3) * (g 2 * g 3) := by noncomm_ring
    _ = 0 := by
      rw [pair_sq 0 1, pair_sq 2 3, perm_2301]
      have h : (g 0 * g 1) * (g 2 * g 3) = vol := by simp [vol, mul_assoc]
      rw [h]
      abel

theorem alpha_omegaJ : α * ωJ = 0 := by
  simp only [α, ωJ]
  calc
    (g 0 * g 1 - g 2 * g 3) * (g 0 * g 2 - g 1 * g 3) =
        (g 0 * g 1) * (g 0 * g 2) - (g 0 * g 1) * (g 1 * g 3) -
          (g 2 * g 3) * (g 0 * g 2) + (g 2 * g 3) * (g 1 * g 3) := by noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 1 2, zero_ijjk 0 1 3, zero_ijki 2 3 0, zero_ijkj 2 3 1]
      simp

theorem alpha_omegaK : α * ωK = 0 := by
  simp only [α, ωK]
  calc
    (g 0 * g 1 - g 2 * g 3) * (g 0 * g 3 + g 1 * g 2) =
        (g 0 * g 1) * (g 0 * g 3) + (g 0 * g 1) * (g 1 * g 2) -
          (g 2 * g 3) * (g 0 * g 3) - (g 2 * g 3) * (g 1 * g 2) := by noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 1 3, zero_ijjk 0 1 2, zero_ijkj 2 3 0, zero_ijki 2 3 1]
      simp

theorem omegaI_omegaJ : ωI * ωJ = 0 := by
  simp only [ωI, ωJ]
  calc
    (g 0 * g 1 + g 2 * g 3) * (g 0 * g 2 - g 1 * g 3) =
        (g 0 * g 1) * (g 0 * g 2) - (g 0 * g 1) * (g 1 * g 3) +
          (g 2 * g 3) * (g 0 * g 2) - (g 2 * g 3) * (g 1 * g 3) := by noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 1 2, zero_ijjk 0 1 3, zero_ijki 2 3 0, zero_ijkj 2 3 1]
      simp

theorem omegaI_omegaK : ωI * ωK = 0 := by
  simp only [ωI, ωK]
  calc
    (g 0 * g 1 + g 2 * g 3) * (g 0 * g 3 + g 1 * g 2) =
        (g 0 * g 1) * (g 0 * g 3) + (g 0 * g 1) * (g 1 * g 2) +
          (g 2 * g 3) * (g 0 * g 3) + (g 2 * g 3) * (g 1 * g 2) := by noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 1 3, zero_ijjk 0 1 2, zero_ijkj 2 3 0, zero_ijki 2 3 1]
      simp

theorem omegaJ_omegaK : ωJ * ωK = 0 := by
  simp only [ωJ, ωK]
  calc
    (g 0 * g 2 - g 1 * g 3) * (g 0 * g 3 + g 1 * g 2) =
        (g 0 * g 2) * (g 0 * g 3) + (g 0 * g 2) * (g 1 * g 2) -
          (g 1 * g 3) * (g 0 * g 3) - (g 1 * g 3) * (g 1 * g 2) := by noncomm_ring
    _ = 0 := by
      rw [zero_ijik 0 2 3, zero_ijkj 0 2 1, zero_ijkj 1 3 0, zero_ijik 1 3 2]
      simp

theorem omegaI_alpha : ωI * α = 0 := by
  rw [two_forms_commute ωI α omegaI_degree alpha_degree, alpha_omegaI]

theorem omegaJ_alpha : ωJ * α = 0 := by
  rw [two_forms_commute ωJ α omegaJ_degree alpha_degree, alpha_omegaJ]

theorem omegaK_alpha : ωK * α = 0 := by
  rw [two_forms_commute ωK α omegaK_degree alpha_degree, alpha_omegaK]

theorem omegaJ_omegaI : ωJ * ωI = 0 := by
  rw [two_forms_commute ωJ ωI omegaJ_degree omegaI_degree, omegaI_omegaJ]

theorem omegaK_omegaI : ωK * ωI = 0 := by
  rw [two_forms_commute ωK ωI omegaK_degree omegaI_degree, omegaI_omegaK]

theorem omegaK_omegaJ : ωK * ωJ = 0 := by
  rw [two_forms_commute ωK ωJ omegaK_degree omegaJ_degree, omegaJ_omegaK]

private theorem square_add_four (w x y z : E)
    (hwx : w * x = 0) (hxw : x * w = 0)
    (hwy : w * y = 0) (hyw : y * w = 0)
    (hwz : w * z = 0) (hzw : z * w = 0)
    (hxy : x * y = 0) (hyx : y * x = 0)
    (hxz : x * z = 0) (hzx : z * x = 0)
    (hyz : y * z = 0) (hzy : z * y = 0) :
    (w + x + y + z) ^ 2 = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [pow_two]
  calc
    (w + x + y + z) * (w + x + y + z) =
        w*w + w*x + w*y + w*z + x*w + x*x + x*y + x*z +
          y*w + y*x + y*y + y*z + z*w + z*x + z*y + z*z := by noncomm_ring
    _ = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by
      rw [hwx, hwy, hwz, hxw, hxy, hxz, hyw, hyx, hyz, hzw, hzx, hzy]
      simp [pow_two, add_assoc]

private theorem scaled_omegaI_sq (a : ℝ) : (a • ωI) ^ 2 = (2 * a ^ 2) • vol := by
  rw [pow_two, smul_mul_smul, ← pow_two ωI, omegaI_sq, smul_smul]
  congr 1
  ring

private theorem scaled_omegaJ_sq (a : ℝ) : (a • ωJ) ^ 2 = (2 * a ^ 2) • vol := by
  rw [pow_two, smul_mul_smul, ← pow_two ωJ, omegaJ_sq, smul_smul]
  congr 1
  ring

private theorem scaled_omegaK_sq (a : ℝ) : (a • ωK) ^ 2 = (2 * a ^ 2) • vol := by
  rw [pow_two, smul_mul_smul, ← pow_two ωK, omegaK_sq, smul_smul]
  congr 1
  ring

private theorem scaled_zero {x y : E} (a b : ℝ) (h : x * y = 0) :
    (a • x) * (b • y) = 0 := by
  rw [smul_mul_smul, h, smul_zero]

/-- The square of the four-dimensional quaternionic pencil. -/
theorem pencil_sq (s a b c : ℝ) :
    (s • α + a • ωI + b • ωJ + c • ωK) ^ 2 =
      (2 * (a ^ 2 + b ^ 2 + c ^ 2 - s ^ 2)) • vol := by
  have hs : (s • α) ^ 2 = -(2 * s ^ 2) • vol := scaled_alpha_sq s
  have ha : (a • ωI) ^ 2 = (2 * a ^ 2) • vol := scaled_omegaI_sq a
  have hb : (b • ωJ) ^ 2 = (2 * b ^ 2) • vol := scaled_omegaJ_sq b
  have hc : (c • ωK) ^ 2 = (2 * c ^ 2) • vol := scaled_omegaK_sq c
  calc
    (s • α + a • ωI + b • ωJ + c • ωK) ^ 2 =
        (s • α) ^ 2 + (a • ωI) ^ 2 + (b • ωJ) ^ 2 + (c • ωK) ^ 2 := by
      apply square_add_four
      · exact scaled_zero s a alpha_omegaI
      · exact scaled_zero a s omegaI_alpha
      · exact scaled_zero s b alpha_omegaJ
      · exact scaled_zero b s omegaJ_alpha
      · exact scaled_zero s c alpha_omegaK
      · exact scaled_zero c s omegaK_alpha
      · exact scaled_zero a b omegaI_omegaJ
      · exact scaled_zero b a omegaJ_omegaI
      · exact scaled_zero a c omegaI_omegaK
      · exact scaled_zero c a omegaK_omegaI
      · exact scaled_zero b c omegaJ_omegaK
      · exact scaled_zero c b omegaK_omegaJ
    _ = (2 * (a ^ 2 + b ^ 2 + c ^ 2 - s ^ 2)) • vol := by
      rw [hs, ha, hb, hc]
      rw [← add_smul, ← add_smul, ← add_smul]
      congr 1
      ring

/-- Every member of the pencil is an actual exterior two-form. -/
theorem pencil_degree (s a b c : ℝ) :
    s • α + a • ωI + b • ωJ + c • ωK ∈ ExteriorAlgebra.exteriorPower ℝ 2 V := by
  exact (ExteriorAlgebra.exteriorPower ℝ 2 V).add_mem
    ((ExteriorAlgebra.exteriorPower ℝ 2 V).add_mem
      ((ExteriorAlgebra.exteriorPower ℝ 2 V).add_mem
        ((ExteriorAlgebra.exteriorPower ℝ 2 V).smul_mem s alpha_degree)
        ((ExteriorAlgebra.exteriorPower ℝ 2 V).smul_mem a omegaI_degree))
      ((ExteriorAlgebra.exteriorPower ℝ 2 V).smul_mem b omegaJ_degree))
    ((ExteriorAlgebra.exteriorPower ℝ 2 V).smul_mem c omegaK_degree)

end QuaternionicSymmetry.FourDimensionalPencil
