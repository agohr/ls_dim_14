import QuaternionicSymmetry.ExteriorContinuousPairing
import QuaternionicSymmetry.ContinuousWedgeBlockAlternation
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-! The canonical exterior pairing preserves the normalized continuous wedge,
with no factorial discrepancy. -/
namespace QuaternionicSymmetry.ExteriorContinuousWedge

open Module ExteriorContinuousPairing ContinuousWedge ContinuousAlternation
  ContinuousMultilinearProduct ContinuousWedgeBlockAlternation

noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {p q : ℕ}

/-- Multiplication in the actual exterior algebra, restricted to its degrees. -/
def mulPower (α : Power V p) (β : Power V q) : Power V (p+q) :=
  ⟨α.val * β.val, SetLike.mul_mem_graded α.property β.property⟩

omit [FiniteDimensional ℝ V] in
@[simp] theorem mulPower_zero_left (β : Power V q) : mulPower (0 : Power V p) β = 0 := by
  apply Subtype.ext
  exact zero_mul _

omit [FiniteDimensional ℝ V] in
@[simp] theorem mulPower_zero_right (α : Power V p) : mulPower α (0 : Power V q) = 0 := by
  apply Subtype.ext
  exact mul_zero _

omit [FiniteDimensional ℝ V] in
@[simp] theorem mulPower_add_left (α α' : Power V p) (β : Power V q) :
    mulPower (α + α') β = mulPower α β + mulPower α' β := by
  apply Subtype.ext
  exact add_mul _ _ _

omit [FiniteDimensional ℝ V] in
@[simp] theorem mulPower_add_right (α : Power V p) (β β' : Power V q) :
    mulPower α (β + β') = mulPower α β + mulPower α β' := by
  apply Subtype.ext
  exact mul_add _ _ _

omit [FiniteDimensional ℝ V] in
@[simp] theorem mulPower_smul_left (r : ℝ) (α : Power V p) (β : Power V q) :
    mulPower (r • α) β = r • mulPower α β := by
  apply Subtype.ext
  exact smul_mul_assoc _ _ _

omit [FiniteDimensional ℝ V] in
@[simp] theorem mulPower_smul_right (r : ℝ) (α : Power V p) (β : Power V q) :
    mulPower α (r • β) = r • mulPower α β := by
  apply Subtype.ext
  exact mul_smul_comm _ _ _

def covectorProduct (f : Fin p → Module.Dual ℝ V) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p => V) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin p) ℝ).compContinuousLinearMap
    (fun i => LinearMap.toContinuousLinearMap (f i))

@[simp] theorem covectorProduct_apply (f : Fin p → Module.Dual ℝ V) (v : Fin p → V) :
    covectorProduct f v = ∏ i, f i (v i) := rfl

theorem toContinuous_decomposable (f : Fin p → Module.Dual ℝ V) :
    toContinuous p (exteriorPower.ιMulti ℝ p f) = alternationCLM (covectorProduct f) := by
  ext v
  simp only [toContinuous_apply, exteriorPower.pairingDual_ιMulti_ιMulti,
    Matrix.det_apply, alternationCLM_apply, covectorProduct_apply]
  rfl

omit [FiniteDimensional ℝ V] in
theorem wedge_alternation (f : ContinuousMultilinearMap ℝ (fun _ : Fin p => V) ℝ)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℝ) :
    wedge (ContinuousLinearMap.mul ℝ ℝ) (alternationCLM f) (alternationCLM g) =
      alternationCLM ((concatenate (ContinuousLinearMap.mul ℝ ℝ) f g).domDomCongr
        (finSumFinEquiv (m := p) (n := q))) := by
  rw [wedge, alternation_concatenate_left_fin, alternation_concatenate_right_fin]
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  simp only [smul_smul, Nat.cast_mul]
  rw [inv_mul_cancel₀ (mul_ne_zero hp hq), one_smul]

theorem covectorProduct_append (f : Fin p → Module.Dual ℝ V)
    (g : Fin q → Module.Dual ℝ V) :
    covectorProduct (Fin.append f g) =
      (concatenate (ContinuousLinearMap.mul ℝ ℝ) (covectorProduct f)
        (covectorProduct g)).domDomCongr (finSumFinEquiv (m := p) (n := q)) := by
  ext v
  simp [covectorProduct_apply, concatenate_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Fin.prod_univ_add, Function.comp_def]

omit [FiniteDimensional ℝ V] in
theorem mulPower_decomposable (f : Fin p → Module.Dual ℝ V)
    (g : Fin q → Module.Dual ℝ V) :
    mulPower (exteriorPower.ιMulti ℝ p f) (exteriorPower.ιMulti ℝ q g) =
      exteriorPower.ιMulti ℝ (p+q) (Fin.append f g) := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti ℝ p f * ExteriorAlgebra.ιMulti ℝ q g =
    ExteriorAlgebra.ιMulti ℝ (p+q) (Fin.append f g)
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [List.ofFn_add, List.prod_append]
  congr 1
  · congr 1
    apply congrArg List.ofFn
    funext i
    exact congrArg (ExteriorAlgebra.ι ℝ) (Fin.append_left f g i).symm
  · simp

theorem toContinuous_mulPower_decomposable (f : Fin p → Module.Dual ℝ V)
    (g : Fin q → Module.Dual ℝ V) :
    toContinuous (p+q) (mulPower (exteriorPower.ιMulti ℝ p f) (exteriorPower.ιMulti ℝ q g)) =
      wedge (ContinuousLinearMap.mul ℝ ℝ)
        (toContinuous p (exteriorPower.ιMulti ℝ p f))
        (toContinuous q (exteriorPower.ιMulti ℝ q g)) := by
  rw [mulPower_decomposable, toContinuous_decomposable, toContinuous_decomposable,
    toContinuous_decomposable, wedge_alternation, covectorProduct_append]

/-- The exterior pairing respects multiplication in every pair of degrees. -/
theorem toContinuous_mulPower (α : Power V p) (β : Power V q) :
    toContinuous (p+q) (mulPower α β) =
      wedge (ContinuousLinearMap.mul ℝ ℝ) (toContinuous p α) (toContinuous q β) := by
  have hα : α ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ p)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  have hβ : β ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ q)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    induction hβ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact toContinuous_mulPower_decomposable f g
    | zero =>
      simp only [mulPower_zero_right, toContinuous_zero]
      ext v
      simp [wedge_apply]
    | add x y hx hy ihx ihy => simp only [mulPower_add_right, toContinuous_add,
        wedge_add_right, ihx, ihy]
    | smul r x hx ih => simp only [mulPower_smul_right, toContinuous_smul,
        wedge_smul_right, ih]
  | zero =>
    simp only [mulPower_zero_left, toContinuous_zero]
    ext v
    simp [wedge_apply]
  | add x y hx hy ihx ihy => simp only [mulPower_add_left, toContinuous_add,
      wedge_add_left, ihx, ihy]
  | smul r x hx ih => simp only [mulPower_smul_left, toContinuous_smul,
      wedge_smul_left, ih]

end
end QuaternionicSymmetry.ExteriorContinuousWedge
