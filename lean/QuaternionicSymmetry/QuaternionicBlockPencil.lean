import QuaternionicSymmetry.QuaternionicBlocks
import QuaternionicSymmetry.FourDimensionalPencil
import QuaternionicSymmetry.CubicNilpotentCoefficient

/-!
  Quaternionic pencils on finitely many coordinate four-blocks.

  The block factorisation is an identity in the actual exterior algebra, with
  the multinomial step carried out in its commutative even subalgebra.
-/

namespace QuaternionicSymmetry
namespace QuaternionicBlockPencil

open scoped BigOperators
open QuaternionicBlocks

noncomputable section

variable {β : Type*} [DecidableEq β]

/-- The scalar coefficient contributed by one quaternionic block. -/
def coefficient (lam : β → ℝ) (j : β) (s a b c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 - s ^ 2 * (lam j) ^ 2

/-- The actual exterior two-form pencil on block `j`. -/
def pencil (lam : β → ℝ) (j : β) (s a b c : ℝ) : E β :=
  (s * lam j) • α j + a • ωI j + b • ωJ j + c • ωK j

theorem pencil_sq (lam : β → ℝ) (j : β) (s a b c : ℝ) :
    (pencil lam j s a b c) ^ 2 = (2 * coefficient lam j s a b c) • vol j := by
  have h := congrArg (ExteriorAlgebra.map (insert j))
    (FourDimensionalPencil.pencil_sq (s * lam j) a b c)
  calc
    (pencil lam j s a b c) ^ 2 =
        (2 * (a ^ 2 + b ^ 2 + c ^ 2 - (s * lam j) ^ 2)) • vol j := by
      simpa only [pencil, α, ωI, ωJ, ωK, vol, map_add, map_smul, map_pow] using h
    _ = (2 * coefficient lam j s a b c) • vol j := by
      congr 1
      simp only [coefficient]
      ring

theorem pencil_degree (lam : β → ℝ) (j : β) (s a b c : ℝ) :
    pencil lam j s a b c ∈ ExteriorAlgebra.exteriorPower ℝ 2 (V β) := by
  exact (ExteriorAlgebra.exteriorPower ℝ 2 (V β)).add_mem
    ((ExteriorAlgebra.exteriorPower ℝ 2 (V β)).add_mem
      ((ExteriorAlgebra.exteriorPower ℝ 2 (V β)).add_mem
        ((ExteriorAlgebra.exteriorPower ℝ 2 (V β)).smul_mem (s * lam j) (alpha_degree j))
        ((ExteriorAlgebra.exteriorPower ℝ 2 (V β)).smul_mem a (omegaI_degree j)))
      ((ExteriorAlgebra.exteriorPower ℝ 2 (V β)).smul_mem b (omegaJ_degree j)))
    ((ExteriorAlgebra.exteriorPower ℝ 2 (V β)).smul_mem c (omegaK_degree j))

private theorem source_pencil_cube (t a b c : ℝ) :
    (t • FourDimensionalForms.α + a • FourDimensionalForms.ωI +
      b • FourDimensionalForms.ωJ + c • FourDimensionalForms.ωK) ^ 3 = 0 := by
  apply ExteriorDimension.pow_eq_zero_of_degree
  · exact FourDimensionalPencil.pencil_degree t a b c
  · rw [Module.finrank_fintype_fun_eq_card]
    norm_num

theorem pencil_cube (lam : β → ℝ) (j : β) (s a b c : ℝ) :
    (pencil lam j s a b c) ^ 3 = 0 := by
  have h := congrArg (ExteriorAlgebra.map (insert j)) (source_pencil_cube (s * lam j) a b c)
  simpa only [pencil, α, ωI, ωJ, ωK, map_add, map_smul, map_pow, map_zero] using h

/-- The block pencil viewed in the commutative even exterior subalgebra. -/
def pencilEven (lam : β → ℝ) (j : β) (s a b c : ℝ) : EvenForms.evenSubalgebra ℝ (V β) :=
  ⟨pencil lam j s a b c,
    (EvenForms.evenSubalgebra ℝ (V β)).add_mem
      ((EvenForms.evenSubalgebra ℝ (V β)).add_mem
        ((EvenForms.evenSubalgebra ℝ (V β)).add_mem
          ((EvenForms.evenSubalgebra ℝ (V β)).smul_mem (alpha_even j) (s * lam j))
          ((EvenForms.evenSubalgebra ℝ (V β)).smul_mem (omegaI_even j) a))
        ((EvenForms.evenSubalgebra ℝ (V β)).smul_mem (omegaJ_even j) b))
      ((EvenForms.evenSubalgebra ℝ (V β)).smul_mem (omegaK_even j) c)⟩

def volEven (j : β) : EvenForms.evenSubalgebra ℝ (V β) := ⟨vol j, vol_even j⟩

@[simp] theorem coe_pencilEven (lam : β → ℝ) (j : β) (s a b c : ℝ) :
    (pencilEven lam j s a b c : E β) = pencil lam j s a b c := rfl

@[simp] theorem coe_volEven (j : β) : (volEven j : E β) = vol j := rfl

theorem pencilEven_sq (lam : β → ℝ) (j : β) (s a b c : ℝ) :
    (pencilEven lam j s a b c) ^ 2 = (2 * coefficient lam j s a b c) • volEven j := by
  apply Subtype.ext
  exact pencil_sq lam j s a b c

theorem pencilEven_cube (lam : β → ℝ) (j : β) (s a b c : ℝ) :
    (pencilEven lam j s a b c) ^ 3 = 0 := by
  apply Subtype.ext
  exact pencil_cube lam j s a b c

private theorem prod_pencilEven_sq (lam : β → ℝ) (s a b c : ℝ) (t : Finset β) :
    (∏ j ∈ t, (pencilEven lam j s a b c) ^ 2) =
      (2 ^ t.card * ∏ j ∈ t, coefficient lam j s a b c) •
        ∏ j ∈ t, volEven j := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        Finset.card_insert_of_notMem hj, ih, pencilEven_sq]
      rw [smul_mul_smul]
      congr 1
      · simp only [pow_succ]
        ring
      · simp only [Finset.prod_insert hj]

/-- The top exterior power of the sum of block pencils, calculated in the
commutative even exterior subalgebra. -/
theorem sum_pencilEven_top_power [Fintype β] (lam : β → ℝ) (s a b c : ℝ) :
    (∑ j, pencilEven lam j s a b c) ^ (2 * Fintype.card β) =
      ((2 * Fintype.card β).factorial : ℝ) •
        ((∏ j, coefficient lam j s a b c) • ∏ j, volEven j) := by
  classical
  let S := EvenForms.evenSubalgebra ℝ (V β)
  have htop := CubicNilpotentSum.top_power (R := S) Finset.univ
    (fun j => pencilEven lam j s a b c)
    (fun j _ => pencilEven_cube lam j s a b c)
  rw [prod_pencilEven_sq] at htop
  rw [show Finset.univ.card = Fintype.card β by simp] at htop
  calc
    (∑ j, pencilEven lam j s a b c) ^ (2 * Fintype.card β) =
        (CubicNilpotentSum.topCoefficient (Fintype.card β) : S) *
          (2 ^ Fintype.card β * ∏ j, coefficient lam j s a b c) •
            ∏ j, volEven j := htop
    _ = ((2 * Fintype.card β).factorial : ℝ) •
        ((∏ j, coefficient lam j s a b c) • ∏ j, volEven j) := by
      rw [smul_smul]
      rw [Algebra.smul_def, Algebra.smul_def]
      rw [← mul_assoc]
      apply congrArg (fun x : S => x * ∏ j, volEven j)
      change (algebraMap ℝ S) (CubicNilpotentSum.topCoefficient (Fintype.card β) : ℝ) *
          (algebraMap ℝ S) (2 ^ Fintype.card β * ∏ j, coefficient lam j s a b c) =
        (algebraMap ℝ S) (((2 * Fintype.card β).factorial : ℝ) *
          ∏ j, coefficient lam j s a b c)
      rw [← map_mul]
      congr 1
      rw [show (CubicNilpotentSum.topCoefficient (Fintype.card β) : ℝ) *
          (2 ^ Fintype.card β * ∏ j, coefficient lam j s a b c) =
          ((2 : ℝ) ^ Fintype.card β *
            (CubicNilpotentSum.topCoefficient (Fintype.card β) : ℝ)) *
            ∏ j, coefficient lam j s a b c by ring]
      rw [CubicNilpotentSum.cast_two_pow_mul_topCoefficient]

end
end QuaternionicBlockPencil
end QuaternionicSymmetry
