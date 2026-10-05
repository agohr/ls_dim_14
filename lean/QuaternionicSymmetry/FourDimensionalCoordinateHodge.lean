import QuaternionicSymmetry.FourDimensionalOrientation

/-! Hodge star on the six independent two-form coefficients in the ordered
orthonormal frame `(e₀,e₁,e₂,e₃)`. The order is `(01,02,03,12,13,23)`;
the orientation is the existing determinant-normalized `vol`. -/
namespace QuaternionicSymmetry.FourDimensionalCoordinateHodge

open FourDimensionalForms
noncomputable section

abbrev Two := Fin 6 → ℝ

def star : Two →ₗ[ℝ] Two where
  toFun x := ![x 5, -x 4, x 3, x 2, -x 1, x 0]
  map_add' x y := by funext i; fin_cases i <;> simp [Pi.add_apply] <;> abel
  map_smul' c x := by funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]

@[simp] theorem star_star (x : Two) : star (star x) = x := by
  funext i
  fin_cases i <;> simp [star]

def plusI : Two := fun i => if i = 0 ∨ i = 5 then 1 else 0
def plusJ : Two := fun i => if i = 1 then 1 else if i = 4 then -1 else 0
def plusK : Two := fun i => if i = 2 ∨ i = 3 then 1 else 0
def minusI : Two := fun i => if i = 0 then 1 else if i = 5 then -1 else 0
def minusJ : Two := fun i => if i = 1 ∨ i = 4 then 1 else 0
def minusK : Two := fun i => if i = 2 then 1 else if i = 3 then -1 else 0

@[simp] theorem star_plusI : star plusI = plusI := by funext i; fin_cases i <;> norm_num [star, plusI, Fin.ext_iff]
@[simp] theorem star_plusJ : star plusJ = plusJ := by funext i; fin_cases i <;> norm_num [star, plusJ, Fin.ext_iff]
@[simp] theorem star_plusK : star plusK = plusK := by funext i; fin_cases i <;> norm_num [star, plusK, Fin.ext_iff]
@[simp] theorem star_minusI : star minusI = -minusI := by funext i; fin_cases i <;> norm_num [star, minusI, Fin.ext_iff]
@[simp] theorem star_minusJ : star minusJ = -minusJ := by funext i; fin_cases i <;> norm_num [star, minusJ, Fin.ext_iff]
@[simp] theorem star_minusK : star minusK = -minusK := by funext i; fin_cases i <;> norm_num [star, minusK, Fin.ext_iff]

theorem plus_iff (x : Two) : star x = x ↔
    x = (x 0) • plusI + (x 1) • plusJ + (x 2) • plusK := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    funext i
    fin_cases i <;> simp_all [star, plusI, plusJ, plusK, Pi.add_apply,
      smul_eq_mul, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero] <;> linarith
  · intro h
    calc
      star x = star (x 0 • plusI + x 1 • plusJ + x 2 • plusK) := congrArg star h
      _ = x 0 • plusI + x 1 • plusJ + x 2 • plusK := by simp
      _ = x := h.symm

theorem minus_iff (x : Two) : star x = -x ↔
    x = (x 0) • minusI + (x 1) • minusJ + (x 2) • minusK := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    funext i
    fin_cases i <;> simp_all [star, minusI, minusJ, minusK, Pi.add_apply,
      smul_eq_mul, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero] <;> linarith
  · intro h
    calc
      star x = star (x 0 • minusI + x 1 • minusJ + x 2 • minusK) := congrArg star h
      _ = -(x 0 • minusI + x 1 • minusJ + x 2 • minusK) := by simp; module
      _ = -x := congrArg Neg.neg h.symm

/-- Interpret the ordered six coefficients in the existing exterior algebra.
The basis order and signs agree with `FourDimensionalForms.vol`. -/
def exterior (x : Two) : FourDimensionalForms.E :=
  x 0 • (g 0 * g 1) + x 1 • (g 0 * g 2) +
  x 2 • (g 0 * g 3) + x 3 • (g 1 * g 2) +
  x 4 • (g 1 * g 3) + x 5 • (g 2 * g 3)

theorem exterior_plusI : exterior plusI = ωI := by
  simp [exterior, plusI, ωI]

theorem exterior_plusJ : exterior plusJ = ωJ := by
  simp [exterior, plusJ, ωJ]; abel

theorem exterior_plusK : exterior plusK = ωK := by
  simp [exterior, plusK, ωK]

theorem exterior_minusI : exterior minusI = α := by
  simp [exterior, minusI, α]; abel

theorem volume_g4 (i j k l : Fin 4) :
    volumeCoefficient (g i * g j * g k * g l) =
      Matrix.det ![e i, e j, e k, e l] := by
  have h : g i * g j * g k * g l =
      ExteriorAlgebra.ιMulti ℝ 4 ![e i, e j, e k, e l] := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, g, mul_assoc]
  rw [h]
  rw [volumeCoefficient, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [volumeAlternating, dite_true]
  rfl

theorem volume_g0123 : volumeCoefficient (g 0 * g 1 * g 2 * g 3) = 1 := by
  exact volumeCoefficient_vol

theorem volume_g4_repeat (i j k l : Fin 4)
    (h : i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l) :
    volumeCoefficient (g i * g j * g k * g l) = 0 := by
  rw [volume_g4]
  rcases h with h | h | h | h | h | h
  · subst j
    exact Matrix.det_zero_of_row_eq (by decide : (0 : Fin 4) ≠ 1) (by funext t; rfl)
  · subst k
    exact Matrix.det_zero_of_row_eq (by decide : (0 : Fin 4) ≠ 2) (by funext t; rfl)
  · subst l
    exact Matrix.det_zero_of_row_eq (by decide : (0 : Fin 4) ≠ 3) (by funext t; rfl)
  · subst k
    exact Matrix.det_zero_of_row_eq (by decide : (1 : Fin 4) ≠ 2) (by funext t; rfl)
  · subst l
    exact Matrix.det_zero_of_row_eq (by decide : (1 : Fin 4) ≠ 3) (by funext t; rfl)
  · subst l
    exact Matrix.det_zero_of_row_eq (by decide : (2 : Fin 4) ≠ 3) (by funext t; rfl)

private theorem g_swap (i j : Fin 4) : g i * g j = -(g j * g i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e i) (e j))

private theorem volume_swap01 (i j k l : Fin 4) :
    volumeCoefficient (g i * g j * g k * g l) =
      -volumeCoefficient (g j * g i * g k * g l) := by
  rw [g_swap i j, neg_mul, neg_mul, map_neg]

private theorem volume_swap12 (i j k l : Fin 4) :
    volumeCoefficient (g i * g j * g k * g l) =
      -volumeCoefficient (g i * g k * g j * g l) := by
  have h : g i * g j * g k * g l = -(g i * g k * g j * g l) := by
    calc
      g i * g j * g k * g l = g i * (g j * g k) * g l := by simp [mul_assoc]
      _ = g i * (-(g k * g j)) * g l := by rw [g_swap]
      _ = -(g i * g k * g j * g l) := by simp [mul_assoc]
  rw [h, map_neg]

private theorem volume_swap23 (i j k l : Fin 4) :
    volumeCoefficient (g i * g j * g k * g l) =
      -volumeCoefficient (g i * g j * g l * g k) := by
  have h : g i * g j * g k * g l = -(g i * g j * g l * g k) := by
    calc
      g i * g j * g k * g l = (g i * g j) * (g k * g l) := by simp [mul_assoc]
      _ = (g i * g j) * (-(g l * g k)) := by rw [g_swap k l]
      _ = -(g i * g j * g l * g k) := by simp [mul_assoc]
  rw [h, map_neg]

private theorem volume_0123 :
    volumeCoefficient (g 0 * g 1 * g 2 * g 3) = 1 := volume_g0123

private theorem volume_2301 :
    volumeCoefficient (g 2 * g 3 * g 0 * g 1) = 1 := by
  rw [volume_swap12 2 3 0 1, volume_swap01 2 0 3 1,
    volume_swap23 0 2 3 1, volume_swap12 0 2 1 3, volume_g0123] <;> norm_num

private theorem volume_0213 :
    volumeCoefficient (g 0 * g 2 * g 1 * g 3) = -1 := by
  rw [volume_swap12 0 2 1 3, volume_g0123] <;> norm_num

private theorem volume_1302 :
    volumeCoefficient (g 1 * g 3 * g 0 * g 2) = -1 := by
  rw [volume_swap12 1 3 0 2, volume_swap01 1 0 3 2,
    volume_swap23 0 1 3 2, volume_g0123] <;> norm_num

private theorem volume_0312 :
    volumeCoefficient (g 0 * g 3 * g 1 * g 2) = 1 := by
  rw [volume_swap12 0 3 1 2, volume_swap23 0 1 3 2, volume_g0123] <;> norm_num

private theorem volume_1203 :
    volumeCoefficient (g 1 * g 2 * g 0 * g 3) = 1 := by
  rw [volume_swap12 1 2 0 3, volume_swap01 1 0 2 3, volume_g0123] <;> norm_num

/-- The exterior characterization of the coordinate star, with the
determinant-normalized orientation fixed by `volumeCoefficient vol = 1`. -/
theorem wedge_star_volume (x y : Two) :
    volumeCoefficient (exterior x * exterior (star y)) =
      ∑ i : Fin 6, x i * y i := by
  simp only [exterior, star, Fin.sum_univ_succ, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, map_add, map_smul]
  simp_rw [← mul_assoc]
  simp [volume_g4_repeat, volume_0123, volume_2301,
    volume_0213, volume_1302, volume_0312, volume_1203,
    Fin.ext_iff]
  ring

theorem exterior_sub (x y : Two) :
    exterior (x - y) = exterior x - exterior y := by
  simp [exterior, sub_smul]
  abel

theorem exterior_injective : Function.Injective exterior := by
  intro x y hxy
  have hzero : exterior (x - y) = 0 := by
    rw [exterior_sub, hxy, sub_self]
  have hpair := wedge_star_volume (x - y) (x - y)
  rw [hzero, zero_mul, map_zero] at hpair
  have hterm (i : Fin 6) : (x - y) i * (x - y) i = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg ((x - y) j))).mp hpair.symm i (Finset.mem_univ i)
  funext i
  have hi := hterm i
  simp only [Pi.sub_apply] at hi
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hi)


end
end QuaternionicSymmetry.FourDimensionalCoordinateHodge
