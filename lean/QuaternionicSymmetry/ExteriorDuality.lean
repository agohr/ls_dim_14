import QuaternionicSymmetry.BilinearExterior
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! Nondegeneracy of the actual exterior dual pairing in finite dimension. -/

namespace QuaternionicSymmetry.ExteriorDuality

open Module

noncomputable section

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

theorem pairingDual_bijective (b : Basis ι ℝ V) (n : ℕ) :
    Function.Bijective (exteriorPower.pairingDual ℝ V n) := by
  classical
  letI : LinearOrder ι := IsWellFounded.wellOrderExtension emptyWf.rel
  let e := (b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)
  have he : exteriorPower.pairingDual ℝ V n = e.toLinearMap := by
    apply (b.dualBasis.exteriorPower n).ext
    intro s
    change exteriorPower.pairingDual ℝ V n (b.dualBasis.exteriorPower n s) =
      e (b.dualBasis.exteriorPower n s)
    rw [show e (b.dualBasis.exteriorPower n s) = (b.exteriorPower n).dualBasis s by
      exact Basis.equiv_apply _ _ _ _]
    rw [exteriorPower.basis_apply]
    simp only [Basis.coe_dualBasis]
    exact (exteriorPower.basis_coord ℝ n b s).symm
  rw [he]
  exact e.bijective

theorem twoform_ext (b : Basis ι ℝ V)
    {α γ : ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)}
    (h : ∀ v w, BilinearExterior.evaluate v w α = BilinearExterior.evaluate v w γ) :
    α = γ := by
  apply (pairingDual_bijective b 2).injective
  apply exteriorPower.linearMap_ext
  ext x
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  change exteriorPower.pairingDual ℝ V 2 α (exteriorPower.ιMulti ℝ 2 x) =
    exteriorPower.pairingDual ℝ V 2 γ (exteriorPower.ιMulti ℝ 2 x)
  rw [hx]
  exact h (x 0) (x 1)

/-- The exterior representative is independent of the basis used to construct it. -/
theorem ofBilinear_basis_independent {κ : Type*} [Fintype κ]
    (b : Basis ι ℝ V) (c : Basis κ ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    BilinearExterior.ofBilinear b B = BilinearExterior.ofBilinear c B := by
  apply twoform_ext b
  intro v w
  rw [BilinearExterior.evaluate_ofBilinear, BilinearExterior.evaluate_ofBilinear]

end
end QuaternionicSymmetry.ExteriorDuality
