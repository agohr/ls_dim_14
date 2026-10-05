import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Analysis.Complex.Basic

/-! A source-free centre test. A self-centralizing subalgebra contains the
centre; nonzero adjoint eigenvectors whose characters separate that
subalgebra then force the centre to vanish. Root multiplicity is not used.
The geometric proof must still supply those characters and separation. -/

namespace QuaternionicSymmetry.LieCenterFromSeparatingWeights

variable {L ι : Type*} [LieRing L] [LieAlgebra ℂ L]

theorem center_eq_bot_of_separating_weights
    (H : LieSubalgebra ℂ L)
    (hSelf : ∀ x : L, (∀ y ∈ H, ⁅x,y⁆ = 0) → x ∈ H)
    (χ : ι → H → ℂ)
    (hWeights : ∀ i, ∃ v : L, v ≠ 0 ∧
      ∀ h : H, ⁅(h : L),v⁆ = χ i h • v)
    (hSeparate : ∀ h : H, (∀ i, χ i h = 0) → h = 0) :
    LieAlgebra.center ℂ L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hCentral : ∀ y : L, ⁅x,y⁆ = 0 := by
    intro y
    have hy := (LieModule.mem_maxTrivSubmodule ℂ L L x).mp hx y
    simpa only [← lie_skew x y, neg_eq_zero] using hy
  let xH : H := ⟨x, hSelf x (fun y _ => hCentral y)⟩
  have hxH : xH = 0 := hSeparate xH (by
    intro i
    obtain ⟨v, hv, hEigen⟩ := hWeights i
    have hScalar : χ i xH • v = 0 := (hEigen xH).symm.trans (hCentral v)
    exact (smul_eq_zero.mp hScalar).resolve_right hv)
  change x = 0
  exact congrArg (fun h : H => (h : L)) hxH

end QuaternionicSymmetry.LieCenterFromSeparatingWeights
