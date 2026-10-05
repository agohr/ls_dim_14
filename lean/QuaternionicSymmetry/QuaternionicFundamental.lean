import QuaternionicSymmetry.HyperholomorphicExterior

/-! The quaternionic fundamental four-form in the actual exterior algebra of
the real dual space. Its construction is independent of the auxiliary basis. -/

namespace QuaternionicSymmetry.QuaternionicFundamental

open Module
open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev E (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  EvenForms.evenSubalgebra ℝ (Module.Dual ℝ V)

def omega (Q : QuaternionicStructure V) (b : Basis ι ℝ V) : Fin 3 → E V := ![
  HyperholomorphicExterior.evenForm b Q.I.toLinearEquiv.toLinearMap,
  HyperholomorphicExterior.evenForm b Q.J.toLinearEquiv.toLinearMap,
  HyperholomorphicExterior.evenForm b Q.K.toLinearEquiv.toLinearMap]

def form (Q : QuaternionicStructure V) (b : Basis ι ℝ V) : E V :=
  ∑ i : Fin 3, omega Q b i ^ 2

theorem omega_basis_independent {κ : Type*} [Fintype κ]
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (c : Basis κ ℝ V) :
    omega Q b = omega Q c := by
  unfold omega
  rw [HyperholomorphicExterior.evenForm_basis_independent b c]

theorem form_basis_independent {κ : Type*} [Fintype κ]
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (c : Basis κ ℝ V) :
    form Q b = form Q c := by
  unfold form
  rw [omega_basis_independent Q b c]

theorem form_eq (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    form Q b = omega Q b 0 ^ 2 + omega Q b 1 ^ 2 + omega Q b 2 ^ 2 := by
  exact Fin.sum_univ_three _

end
end QuaternionicSymmetry.QuaternionicFundamental
