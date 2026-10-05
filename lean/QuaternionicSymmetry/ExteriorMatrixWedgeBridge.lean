import QuaternionicSymmetry.ContinuousMatrixWedgeEntries
import QuaternionicSymmetry.QuaternionicExteriorTraceForms
import QuaternionicSymmetry.ExteriorContinuousWedge
import QuaternionicSymmetry.LocalChernWeilTracePowers

/-! Homogeneous exterior matrix powers and normalized matrix-valued wedges. -/
namespace QuaternionicSymmetry.ExteriorMatrixWedgeBridge
open ExteriorContinuousPairing ExteriorContinuousWedge ContinuousWedge
  ContinuousMatrixWedgeEntries EvenForms QuaternionicExteriorEvenTrace
noncomputable section
set_option maxHeartbeats 1000000

variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype κ] [DecidableEq κ]

private abbrev X := ExteriorAlgebra ℝ (Module.Dual ℝ V)

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

omit [FiniteDimensional ℝ V] in
private theorem matrix_pow_mem (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (m : ℕ) (i j : κ) :
    (((A ^ m) i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ (2 * m) (Module.Dual ℝ V) := by
  induction m generalizing i j with
  | zero =>
      change (((1 : Matrix κ κ (EvenAlgebra V)) i j : EvenAlgebra V) : X (V := V)) ∈ _
      classical
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      change ((∑ k : κ, (A ^ m) i k * A k j : EvenAlgebra V) : X (V := V)) ∈ _
      rw [Nat.mul_succ]
      change (Subalgebra.val (evenSubalgebra ℝ (Module.Dual ℝ V))
        (∑ k : κ, (A ^ m) i k * A k j)) ∈ _
      rw [map_sum]
      apply Submodule.sum_mem
      intro k hk
      rw [map_mul]
      exact SetLike.mul_mem_graded (ih i k) (hA k j)

/-- The `(i,j)` entry of a matrix power, retained in its exact exterior degree. -/
def powerEntry (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (m : ℕ) (i j : κ) : Power V (2 * m) :=
  ⟨((A ^ m) i j : EvenAlgebra V), matrix_pow_mem A hA m i j⟩

/-- The coefficient matrix regarded as a genuine continuous alternating two-form. -/
def matrixTwoForm (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)) :
    V [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ :=
  ContinuousAlternatingMap.pi (fun i : κ =>
    ContinuousAlternatingMap.pi (fun j : κ =>
      toContinuous 2 (powerEntry A hA 1 i j)))

@[simp] theorem matrixTwoForm_entry (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (i j : κ) :
    entry i j (matrixTwoForm A hA) = toContinuous 2 (powerEntry A hA 1 i j) := by
  rfl

/-- Degree of the ordered matrix wedge power, definitionally the degree
used by the project's local Chern--Weil curvature powers. -/
abbrev wedgeDegree := LocalChernWeilTracePowers.powerDegree

theorem wedgeDegree_eq (k : ℕ) : wedgeDegree k = 2 * (k + 1) := by
  exact LocalChernWeilTracePowers.powerDegree_eq k

/-- A power entry with the recursive wedge degree as its index. -/
def wedgeEntry (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (k : ℕ) (i j : κ) : Power V (wedgeDegree k) :=
  ⟨((A ^ (k + 1)) i j : EvenAlgebra V), by
    rw [wedgeDegree_eq]
    exact matrix_pow_mem A hA (k + 1) i j⟩

/-- The ordered matrix wedge power, with exponent `k+1`. -/
def matrixWedgePower (γ : V [⋀^Fin 2]→L[ℝ] Matrix κ κ ℝ) :
    (k : ℕ) → V [⋀^Fin (wedgeDegree k)]→L[ℝ] Matrix κ κ ℝ
  | 0 => γ
  | k + 1 => wedge (ContinuousLinearMap.mul ℝ (Matrix κ κ ℝ)) γ
      (matrixWedgePower γ k)

/-- Every entry of the ordered matrix wedge power is the canonical pairing
of the corresponding homogeneous exterior matrix power. -/
theorem matrixWedgePower_entry (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (k : ℕ) (i j : κ) :
    entry i j (matrixWedgePower (matrixTwoForm A hA) k) =
      toContinuous (wedgeDegree k) (wedgeEntry A hA k i j) := by
  induction k generalizing i j with
  | zero =>
      simpa only [matrixWedgePower, wedgeDegree, wedgeEntry, powerEntry,
        Nat.zero_add, Nat.add_zero, mul_one] using
        matrixTwoForm_entry A hA i j
  | succ k ih =>
      rw [matrixWedgePower]
      rw [entry_wedge_mul]
      simp_rw [matrixTwoForm_entry, ih]
      simp_rw [← toContinuous_mulPower]
      change (∑ l : κ, (toContinuousLinear (V := V) (2 + wedgeDegree k))
        (mulPower (powerEntry A hA 1 i l) (wedgeEntry A hA k l j))) = _
      rw [← map_sum (toContinuousLinear (V := V) (2 + wedgeDegree k))]
      change toContinuous (wedgeDegree (k + 1))
        (∑ l : κ, mulPower (powerEntry A hA 1 i l) (wedgeEntry A hA k l j)) = _
      congr 1
      apply Subtype.ext
      simp only [Submodule.coe_sum, mulPower, powerEntry, wedgeEntry, pow_one]
      calc
        (∑ l : κ, ((A i l : EvenAlgebra V) : X (V := V)) *
            (((A ^ (k + 1)) l j : EvenAlgebra V) : X (V := V))) =
          (((∑ l : κ, A i l * (A ^ (k + 1)) l j : EvenAlgebra V)) : X (V := V)) := by
            simp
        _ = (((A ^ (k + 1 + 1)) i j : EvenAlgebra V) : X (V := V)) := by
          congr 1
          conv_rhs => rw [pow_succ' A (k + 1)]
          simp only [Matrix.mul_apply]

end
end QuaternionicSymmetry.ExteriorMatrixWedgeBridge
