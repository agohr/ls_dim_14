import QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! A real quaternionic structure supplies a natural complex scalar action
after fixing its first imaginary unit. -/
namespace QuaternionicSymmetry.QuaternionicComplexModule

open Module
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : QuaternionicStructure V)

private def iEnd : Module.End ℝ V := Q.I.toLinearEquiv.toLinearMap

private theorem iEnd_sq : iEnd Q * iEnd Q = -1 := by
  ext v
  change Q.I (Q.I v) = -v
  exact Q.I_sq v

/-- Complex scalars act through the real endomorphism `I`. -/
def complexActionHom : ℂ →+* Module.End ℝ V :=
  (Complex.liftAux (iEnd Q) (iEnd_sq Q)).toRingHom

def complexModule : Module ℂ V := Module.compHom V (complexActionHom Q)

theorem complex_smul_apply (z : ℂ) (v : V) :
    (letI : Module ℂ V := complexModule Q; z • v) =
      z.re • v + z.im • Q.I v := by
  change (complexActionHom Q z) v = _
  simp [complexActionHom, Complex.liftAux_apply, iEnd]

theorem complex_I_smul (v : V) :
    (letI : Module ℂ V := complexModule Q; Complex.I • v) = Q.I v := by
  simp [complex_smul_apply]

theorem complex_ofReal_smul (r : ℝ) (v : V) :
    (letI : Module ℂ V := complexModule Q; (r : ℂ) • v) = r • v := by
  simp [complex_smul_apply]

theorem complex_scalar_tower :
    letI : Module ℂ V := complexModule Q
    IsScalarTower ℝ ℂ V := by
  letI : Module ℂ V := complexModule Q
  refine ⟨fun r z v => ?_⟩
  change (complexActionHom Q (r • z)) v =
    r • (complexActionHom Q z v)
  change ((Complex.liftAux (iEnd Q) (iEnd_sq Q)) (r • z)) v = _
  rw [map_smul]
  rfl

/-- A real endomorphism commuting with `I` is complex-linear for the induced
complex vector structure. -/
def complexLinearEnd (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) :
    letI : Module ℂ V := complexModule Q
    V →ₗ[ℂ] V := by
  letI : Module ℂ V := complexModule Q
  refine { toFun := A, map_add' := A.map_add, map_smul' := ?_ }
  intro z v
  rw [complex_smul_apply, complex_smul_apply]
  simp only [map_add, map_smul, hA, RingHom.id_apply]

theorem complexLinearEnd_apply (A : V →ₗ[ℝ] V)
    (hA : ∀ v, A (Q.I v) = Q.I (A v)) (v : V) :
    complexLinearEnd Q A hA v = A v := rfl

theorem complex_finrank_double :
    letI : Module ℂ V := complexModule Q
    Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
  letI : Module ℂ V := complexModule Q
  letI : IsScalarTower ℝ ℂ V := complex_scalar_tower Q
  have hmodule : (Module.complexToReal V) = (inferInstance : Module ℝ V) := by
    apply Module.ext
    funext r v
    exact complex_ofReal_smul Q r v
  simpa only [hmodule] using (finrank_real_of_complex V)

theorem complex_finite [FiniteDimensional ℝ V] [Nontrivial V] :
    letI : Module ℂ V := complexModule Q
    FiniteDimensional ℂ V := by
  letI : Module ℂ V := complexModule Q
  have hr : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hc : 0 < Module.finrank ℂ V := by
    have h := complex_finrank_double Q
    omega
  exact FiniteDimensional.of_finrank_pos hc

end
end QuaternionicSymmetry.QuaternionicComplexModule
