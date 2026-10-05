import QuaternionicSymmetry.QuaternionicStructure
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.Dimension.Free

/-! The genuine quaternion scalar action induced by a quaternionic structure. -/

namespace QuaternionicSymmetry.QuaternionicStructure

open scoped Quaternion

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def endomorphismBasis (Q : QuaternionicStructure V) :
    QuaternionAlgebra.Basis (Module.End ℝ V) (-1 : ℝ) 0 (-1) where
  i := Q.I.toLinearEquiv.toLinearMap
  j := Q.J.toLinearEquiv.toLinearMap
  k := Q.K.toLinearEquiv.toLinearMap
  i_mul_i := by ext v; simp [Q.I_sq]
  j_mul_j := by ext v; simp [Q.J_sq]
  i_mul_j := by ext v; rfl
  j_mul_i := by ext v; simp [Q.J_I_anti]

/-- A real algebra homomorphism from the actual quaternion division algebra. -/
def action (Q : QuaternionicStructure V) : ℍ →ₐ[ℝ] Module.End ℝ V :=
  Q.endomorphismBasis.liftHom

theorem action_apply (Q : QuaternionicStructure V) (q : ℍ) (v : V) :
    Q.action q v = q.re • v + q.imI • Q.I v + q.imJ • Q.J v + q.imK • Q.K v := by
  rfl

/-- Restrict the tautological endomorphism action along the quaternion homomorphism. -/
def quaternionModule (Q : QuaternionicStructure V) : Module ℍ V :=
  Module.compHom V Q.action.toRingHom

def quaternionTower (Q : QuaternionicStructure V) :
    letI := Q.quaternionModule
    IsScalarTower ℝ ℍ V := by
  letI := Q.quaternionModule
  refine ⟨?_⟩
  intro r q v
  change Q.action (r • q) v = r • Q.action q v
  rw [map_smul]
  rfl

/-- Dimension over the actual quaternion division ring, with the action just constructed. -/
def quaternionicDimension (Q : QuaternionicStructure V) : ℕ :=
  letI := Q.quaternionModule
  Module.finrank ℍ V

theorem real_finrank (Q : QuaternionicStructure V) :
    Module.finrank ℝ V = 4 * Q.quaternionicDimension := by
  letI := Q.quaternionModule
  letI := Q.quaternionTower
  have h := Module.finrank_mul_finrank ℝ ℍ V
  rw [Quaternion.finrank_eq_four] at h
  exact h.symm

theorem four_dvd_real_finrank (Q : QuaternionicStructure V) : 4 ∣ Module.finrank ℝ V :=
  ⟨Q.quaternionicDimension, Q.real_finrank⟩

theorem action_commutes (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hI : ∀ v, A (Q.I v) = Q.I (A v)) (hJ : ∀ v, A (Q.J v) = Q.J (A v))
    (q : ℍ) (v : V) : A (Q.action q v) = Q.action q (A v) := by
  simp only [action_apply, map_add, map_smul, hI, hJ, Q.commute_K A hI hJ]

/-- Commuting with the two complex structures makes the map genuinely quaternion-linear. -/
def quaternionLinear (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hI : ∀ v, A (Q.I v) = Q.I (A v)) (hJ : ∀ v, A (Q.J v) = Q.J (A v)) :
    letI := Q.quaternionModule
    V →ₗ[ℍ] V := by
  letI := Q.quaternionModule
  exact {
    toFun := A
    map_add' := A.map_add
    map_smul' := Q.action_commutes A hI hJ }

end
end QuaternionicSymmetry.QuaternionicStructure
