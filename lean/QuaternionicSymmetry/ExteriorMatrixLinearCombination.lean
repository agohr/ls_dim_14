import QuaternionicSymmetry.RealifiedTracePolynomial
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! Finite real matrix combinations of homogeneous two-forms agree with
their canonically paired continuous matrix-valued forms. -/
namespace QuaternionicSymmetry.ExteriorMatrixLinearCombination
open RealifiedTracePolynomial ExteriorContinuousPairing ExteriorMatrixWedgeBridge
open QuaternionicExteriorEvenTrace EvenForms
noncomputable section
variable {V β κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype β] [Fintype κ] [DecidableEq κ]
local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra
variable (B : β → Matrix κ κ ℝ) (η : β → Power V 2)

def exteriorMatrix : Matrix κ κ (EvenAlgebra V) :=
  combination B (fun b => ofTwoForm (η b))

omit [FiniteDimensional ℝ V] [Fintype κ] [DecidableEq κ] in
theorem entries_two (i j : κ) :
    ((exteriorMatrix B η i j : EvenAlgebra V) : ExteriorAlgebra ℝ (Module.Dual ℝ V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) := by
  change (Subalgebra.val (evenSubalgebra ℝ (Module.Dual ℝ V))
    (∑ b, algebraMap ℝ (EvenAlgebra V) (B b i j) * ofTwoForm (η b))) ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro b _
  change (B b i j) • (η b).val ∈ ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)
  exact Submodule.smul_mem _ _ (η b).property

omit [FiniteDimensional ℝ V] in
theorem powerEntry_one (i j : κ) :
    powerEntry (exteriorMatrix B η) (entries_two B η) 1 i j =
      ∑ b, (B b i j) • η b := by
  apply Subtype.ext
  simp only [powerEntry, pow_one, Submodule.coe_sum, Submodule.coe_smul]
  change (Subalgebra.val (evenSubalgebra ℝ (Module.Dual ℝ V))
    (∑ b, algebraMap ℝ (EvenAlgebra V) (B b i j) * ofTwoForm (η b))) = _
  rw [map_sum]
  rfl

theorem matrixTwoForm_apply (v : Fin 2 → V) :
    matrixTwoForm (exteriorMatrix B η) (entries_two B η) v =
      ∑ b, toContinuous 2 (η b) v • B b := by
  ext i j
  change toContinuous 2 (powerEntry (exteriorMatrix B η) (entries_two B η) 1 i j) v = _
  rw [powerEntry_one]
  change (toContinuousLinear 2 (∑ b, (B b i j) • η b)) v = _
  rw [map_sum]
  simp only [map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

end
end QuaternionicSymmetry.ExteriorMatrixLinearCombination
