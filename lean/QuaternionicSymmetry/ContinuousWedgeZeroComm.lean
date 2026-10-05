import QuaternionicSymmetry.ContinuousWedgeUnit
import QuaternionicSymmetry.ManifoldDeRhamRing

namespace QuaternionicSymmetry.ContinuousWedgeZeroComm

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeUnit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zeroAlt_eq_smul_one
    (β : E [⋀^Fin 0]→L[ℝ] ℝ) :
    β = (β Fin.elim0) • oneZero := by
  ext v
  have hv : v = Fin.elim0 := funext (fun i => Fin.elim0 i)
  subst v
  simp [oneZero, ContinuousAlternatingMap.smul_apply]

theorem wedge_zero_swap {n : ℕ}
    (α : E [⋀^Fin n]→L[ℝ] ℝ)
    (β : E [⋀^Fin 0]→L[ℝ] ℝ) :
    castAlt (Nat.zero_add n)
      (wedge (ContinuousLinearMap.mul ℝ ℝ) β α) =
        wedge (ContinuousLinearMap.mul ℝ ℝ) α β := by
  rw [zeroAlt_eq_smul_one β]
  rw [wedge_smul_left, wedge_smul_right]
  rw [wedge_one_left, wedge_one_right]
  ext v
  simp only [castAlt_apply, ContinuousAlternatingMap.smul_apply]
  congr 1

end QuaternionicSymmetry.ContinuousWedgeZeroComm
