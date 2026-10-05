import QuaternionicSymmetry.QuaternionicFundamental
import QuaternionicSymmetry.ExteriorDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Degree bookkeeping for the actual quaternionic fundamental form.

The statements here concern membership in the homogeneous pieces of the actual
exterior algebra.  They do not assert any geometric nonvanishing or spectral
classification result.
-/

namespace QuaternionicSymmetry.QuaternionicFundamental

open Module
open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private abbrev A (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  ExteriorAlgebra ℝ (Module.Dual ℝ V)

theorem omega_mem_degree (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (j : Fin 3) :
    ((omega Q b j : E V) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) := by
  fin_cases j
  · change (↑(EvenForms.ofTwoForm (HyperholomorphicExterior.form b
      Q.I.toLinearEquiv.toLinearMap)) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)
    simpa only [EvenForms.ofTwoForm_coe] using
      (HyperholomorphicExterior.form b Q.I.toLinearEquiv.toLinearMap).property
  · change (↑(EvenForms.ofTwoForm (HyperholomorphicExterior.form b
      Q.J.toLinearEquiv.toLinearMap)) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)
    simpa only [EvenForms.ofTwoForm_coe] using
      (HyperholomorphicExterior.form b Q.J.toLinearEquiv.toLinearMap).property
  · change (↑(EvenForms.ofTwoForm (HyperholomorphicExterior.form b
      Q.K.toLinearEquiv.toLinearMap)) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)
    simpa only [EvenForms.ofTwoForm_coe] using
      (HyperholomorphicExterior.form b Q.K.toLinearEquiv.toLinearMap).property

theorem omega_sq_mem_degree (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (j : Fin 3) :
    (((omega Q b j : E V) ^ 2 : E V) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ 4 (Module.Dual ℝ V) := by
  have hj := omega_mem_degree Q b j
  have hsq := SetLike.mul_mem_graded hj hj
  simpa only [pow_two] using hsq

theorem form_mem_degree (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    ((form Q b : E V) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ 4 (Module.Dual ℝ V) := by
  rw [form_eq Q b]
  change (((((omega Q b 0 : E V) ^ 2 : E V) : A V) +
    (((omega Q b 1 : E V) ^ 2 : E V) : A V) +
    (((omega Q b 2 : E V) ^ 2 : E V) : A V))) ∈
      ExteriorAlgebra.exteriorPower ℝ 4 (Module.Dual ℝ V)
  exact (ExteriorAlgebra.exteriorPower ℝ 4 (Module.Dual ℝ V)).add_mem
    ((ExteriorAlgebra.exteriorPower ℝ 4 (Module.Dual ℝ V)).add_mem
      (omega_sq_mem_degree Q b 0) (omega_sq_mem_degree Q b 1))
    (omega_sq_mem_degree Q b 2)

theorem form_pow_mem_degree (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (n : ℕ) :
    (((form Q b : E V) ^ n : E V) : A V) ∈
      ExteriorAlgebra.exteriorPower ℝ (4 * n) (Module.Dual ℝ V) := by
  have h := SetLike.pow_mem_graded n (form_mem_degree Q b)
  simpa [Nat.mul_comm] using h

theorem form_pow_eq_zero_of_finrank_lt [FiniteDimensional ℝ V]
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (n : ℕ)
    (h : Module.finrank ℝ V < 4 * n) :
    (((form Q b : E V) ^ n : E V) : A V) = 0 := by
  apply ExteriorDimension.pow_eq_zero_of_degree (form_mem_degree Q b)
  rw [Subspace.dual_finrank_eq]
  simpa [Nat.mul_comm] using h

end
end QuaternionicSymmetry.QuaternionicFundamental
