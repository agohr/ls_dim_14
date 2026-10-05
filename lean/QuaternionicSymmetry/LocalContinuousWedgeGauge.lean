import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.LocalChernWeilQuadratic

/-! Pointwise gauge conjugation commutes with every normalized continuous
wedge of ring-valued forms, and cyclic traces remove the conjugation. -/

namespace QuaternionicSymmetry.LocalContinuousWedgeGauge

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.LocalChernWeilQuadratic

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {p q : ℕ}

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

def conjugationCLM (g h : R) : R →L[ℝ] R :=
  ((ContinuousLinearMap.mul ℝ R) h).comp ((ContinuousLinearMap.mul ℝ R).flip g)

@[simp] theorem conjugationCLM_apply (g h a : R) :
    conjugationCLM g h a = h * (a * g) := rfl

def conjugateForm (g h : R) (α : E [⋀^Fin p]→L[ℝ] R) :
    E [⋀^Fin p]→L[ℝ] R :=
  (conjugationCLM g h).compContinuousAlternatingMap α

@[simp] theorem conjugateForm_apply (g h : R)
    (α : E [⋀^Fin p]→L[ℝ] R) (v : Fin p → E) :
    conjugateForm g h α v = h * (α v * g) := rfl

theorem conjugationCLM_mul (g h : R) (hright : g * h = 1) (a b : R) :
    conjugationCLM g h (a * b) =
      conjugationCLM g h a * conjugationCLM g h b := by
  simp only [conjugationCLM_apply]
  calc
    h * (a * b * g) = h * (a * (g * h) * b * g) := by
      rw [hright]
      simp only [mul_one]
    _ = h * (a * g) * (h * (b * g)) := by noncomm_ring

theorem conjugateForm_wedge_mul (g h : R) (hright : g * h = 1)
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    conjugateForm g h (wedge (ContinuousLinearMap.mul ℝ R) α β) =
      wedge (ContinuousLinearMap.mul ℝ R)
        (conjugateForm g h α) (conjugateForm g h β) := by
  ext v
  rw [show conjugateForm g h (wedge (ContinuousLinearMap.mul ℝ R) α β) v =
      conjugationCLM g h (wedge (ContinuousLinearMap.mul ℝ R) α β v) from rfl]
  rw [wedge_apply, map_smul, map_sum]
  rw [wedge_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [ContinuousLinearMap.map_smul_of_tower]
  congr 1
  exact conjugationCLM_mul g h hright _ _

theorem cyclic_conjugateForm (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (g h : R) (hright : g * h = 1)
    (α : E [⋀^Fin p]→L[ℝ] R) :
    T.compContinuousAlternatingMap (conjugateForm g h α) =
      T.compContinuousAlternatingMap α := by
  ext v
  change T (h * (α v * g)) = T (α v)
  rw [hT, mul_assoc, hright, mul_one]

theorem trace_wedge_mul_conjugate (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (g h : R) (hright : g * h = 1)
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    T.compContinuousAlternatingMap
      (wedge (ContinuousLinearMap.mul ℝ R)
        (conjugateForm g h α) (conjugateForm g h β)) =
    T.compContinuousAlternatingMap
      (wedge (ContinuousLinearMap.mul ℝ R) α β) := by
  rw [← conjugateForm_wedge_mul g h hright α β]
  exact cyclic_conjugateForm T hT g h hright _

end
end QuaternionicSymmetry.LocalContinuousWedgeGauge
