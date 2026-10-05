import QuaternionicSymmetry.GeneralComplexAdjointFromReal
import QuaternionicSymmetry.RealAdjointDifferentialFromMathlib
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The genuine adjoint representation of a complex Lie group, with
continuity obtained from its internally calculated differential at one. -/
namespace QuaternionicSymmetry.ComplexAdjointRepresentation
open GeneralComplexAdjointDifferentialSource ComplexLieRealCompanion
open scoped Manifold ContDiff Topology
noncomputable section
variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G] [LieGroup 𝓘(ℂ,V) ∞ G]

lemma conjugation_smooth (g : G) :
    ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (fun h : G => g*h*g⁻¹) :=
  (contMDiff_const.mul contMDiff_id).mul contMDiff_const

def adjoint : G →* Module.End ℂ V where
  toFun g := (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (fun h : G => g*h*g⁻¹) 1).toLinearMap
  map_one' := by
    change (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (fun h : G => 1*h*1⁻¹) 1).toLinearMap = _
    rw [show (fun h : G => 1*h*1⁻¹) = id by funext h; simp]
    exact congrArg ContinuousLinearMap.toLinearMap (mfderiv_id (I := 𝓘(ℂ,V)) (x := (1 : G)))
  map_mul' g h := by
    have heq : (fun t : G => (g*h)*t*(g*h)⁻¹) =
        (fun t : G => g*t*g⁻¹) ∘ (fun t : G => h*t*h⁻¹) := by
      funext t
      simp [mul_assoc]
    have hd := mfderiv_comp (I := 𝓘(ℂ,V)) (I' := 𝓘(ℂ,V)) (I'' := 𝓘(ℂ,V))
      (x := (1 : G)) ((conjugation_smooth g).mdifferentiableAt (by simp))
      ((conjugation_smooth h).mdifferentiableAt (by simp))
    change (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) _ 1).toLinearMap = _
    rw [heq, hd, show h*1*h⁻¹ = 1 by simp]
    rfl

@[simp] lemma adjoint_apply (g : G) (v : V) : adjoint (V := V) g v = adjointOrbit v g := rfl

lemma continuousAt_adjointOrbit_one (v : V) : ContinuousAt (adjointOrbit (G := G) v) 1 := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  exact ((GeneralComplexAdjointFromReal.complexAdjointDifferential_of_real
    RealAdjointDifferentialFromMathlib.realAdjointDifferential) v).1.continuousAt

lemma continuous_adjointOrbit (v : V) : Continuous (adjointOrbit (G := G) v) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ,V) ∞
  apply continuous_iff_continuousAt.mpr
  intro g
  let A : V →L[ℂ] V := LinearMap.toContinuousLinearMap (adjoint (V := V) g)
  have hi : ContinuousAt (fun t : G => g⁻¹*t) g := by fun_prop
  have hc : ContinuousAt (fun t : G => adjointOrbit v (g⁻¹*t)) g := by
    exact ContinuousAt.comp_of_eq (continuousAt_adjointOrbit_one v) hi (inv_mul_cancel g)
  have ht := A.continuous.continuousAt.comp hc
  apply ht.congr
  apply Filter.Eventually.of_forall
  intro t
  change adjoint (V := V) g (adjoint (V := V) (g⁻¹*t) v) = adjointOrbit v t
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rfl

end
end QuaternionicSymmetry.ComplexAdjointRepresentation
