import QuaternionicSymmetry.ContactHamiltonianAlgebra
import QuaternionicSymmetry.ContactExteriorDerivativeCalculus
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! The bordered Levi solution is holomorphic wherever the contact
determinant is nonzero, using inversion of an actual finite-dimensional
continuous linear map. -/
namespace QuaternionicSymmetry.ContactHamiltonianLocalSmooth
open ContactDeterminantAlgebra ContactExteriorDerivativeCalculus ContactHamiltonianAlgebra
open scoped ContDiff
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
local notation "J" => Fin (Module.finrank ℂ (V × ℂ))
local notation "e" => Module.finBasis ℂ (V × ℂ)

def borderMap (a : V → V →L[ℂ] ℂ) (x : V) : (V × ℂ) →L[ℂ] (J → ℂ) :=
  ContinuousLinearMap.pi (fun j => ((border (a x).toLinearMap (exteriorDerivative a x)).flip (e j)).toContinuousLinearMap)

theorem borderMap_apply (a : V → V →L[ℂ] ℂ) (x : V) (u : V × ℂ) (j : J) :
    borderMap a x u j = exteriorDerivative a x u.1 (e j).1 + u.2 * a x (e j).1 - (e j).2 * a x u.1 := rfl

theorem borderMap_invertible (a : V → V →L[ℂ] ℂ) (x : V)
    (h : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate) :
    (borderMap a x).IsInvertible := by
  have hi : Function.Injective (borderMap a x) := by
    intro u v huv
    apply ((border (a x).toLinearMap (exteriorDerivative a x)).toDual h).injective
    apply (Module.finBasis ℂ (V × ℂ)).ext
    intro j
    exact congrFun huv j
  let q := (borderMap a x).toLinearMap.linearEquivOfInjective hi (by simp)
  exact ⟨q.toContinuousLinearEquiv,rfl⟩

def datumCoordinates (f : V → ℂ) (x : V) : J → ℂ :=
  fun j => -fderiv ℂ f x (e j).1 - f x * (e j).2

def localSolution (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (x : V) : V × ℂ :=
  (borderMap a x).inverse (datumCoordinates f x)

theorem localSolution_eq (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (x : V)
    (h : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate) :
    localSolution a f x = solution (a x).toLinearMap (exteriorDerivative a x) h (f x) (fderiv ℂ f x).toLinearMap := by
  have he : borderMap a x (solution (a x).toLinearMap (exteriorDerivative a x) h (f x) (fderiv ℂ f x).toLinearMap) =
      datumCoordinates f x := by
    funext j
    exact solution_equation _ _ h _ _ (e j)
  rw [localSolution,← he]
  exact (borderMap_invertible a x h).inverse_apply_self _

theorem borderMap_contDiffOn (a : V → V →L[ℂ] ℂ) (U : Set V)
    (hU : IsOpen U) (ha : ContDiffOn ℂ ∞ a U) : ContDiffOn ℂ ∞ (borderMap a) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_pi.mpr
  intro j
  have hd : ContDiffOn ℂ ∞ (fderiv ℂ a) U := ha.fderiv_of_isOpen hU (by simp)
  simp only [borderMap_apply,exteriorDerivative_apply]
  exact (((hd.clm_apply contDiffOn_const).clm_apply contDiffOn_const).sub
    ((hd.clm_apply contDiffOn_const).clm_apply contDiffOn_const)).add
    (contDiffOn_const.mul (ha.clm_apply contDiffOn_const)) |>.sub
    (contDiffOn_const.mul (ha.clm_apply contDiffOn_const))

theorem localSolution_contDiffOn (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (U : Set V)
    (hU : IsOpen U) (ha : ContDiffOn ℂ ∞ a U) (hf : ContDiffOn ℂ ∞ f U)
    (h : ∀ x ∈ U, (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate) :
    ContDiffOn ℂ ∞ (localSolution a f) U := by
  have hb := borderMap_contDiffOn a U hU ha
  have hd : ContDiffOn ℂ ∞ (datumCoordinates f) U := by
    apply contDiffOn_pi.mpr
    intro j
    exact (((hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).neg).sub
      (hf.mul contDiffOn_const)
  intro x hx
  exact (((borderMap_invertible a x (h x hx)).contDiffAt_map_inverse.comp x
    (hb.contDiffAt (hU.mem_nhds hx))).clm_apply (hd.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

theorem localSolution_value (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (x : V)
    (h : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate) :
    a x (localSolution a f x).1 = f x := by
  rw [localSolution_eq a f x h]
  exact solution_value _ _ _ _ _

theorem localSolution_levi (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (x v : V)
    (h : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate) :
    exteriorDerivative a x (localSolution a f x).1 v + (localSolution a f x).2 * a x v = -fderiv ℂ f x v := by
  rw [localSolution_eq a f x h]
  exact solution_levi _ _ _ _ _ _

end
end QuaternionicSymmetry.ContactHamiltonianLocalSmooth
