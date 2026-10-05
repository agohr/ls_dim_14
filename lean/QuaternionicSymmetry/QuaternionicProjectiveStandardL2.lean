import QuaternionicSymmetry.QuaternionicProjectiveStandardRepresentation
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The standard block action transported from the product coordinates to
the genuine Hilbert direct sum `WithLp 2 (E × ℍ)`. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardL2

open QuaternionicProjectiveStandardRepresentation
open QuaternionicIsometryNormalizer
open scoped Quaternion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)

abbrev StandardSpace := WithLp 2 (E × ℍ)

private def coordinateEquiv : StandardSpace (E := E) ≃L[ℝ] E × ℍ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ

def standardActionL2 (p : symplecticKernel S × unitary ℍ) :
    StandardSpace (E := E) ≃L[ℝ] StandardSpace (E := E) :=
  ((coordinateEquiv (E := E)).trans (standardAction S p)).trans
    (coordinateEquiv (E := E)).symm

@[simp] theorem standardActionL2_fst
    (p : symplecticKernel S × unitary ℍ)
    (z : StandardSpace (E := E)) :
    (standardActionL2 S p z).fst = p.1.1.1 z.fst := rfl

@[simp] theorem standardActionL2_snd
    (p : symplecticKernel S × unitary ℍ)
    (z : StandardSpace (E := E)) :
    (standardActionL2 S p z).snd = z.snd * star (p.2 : ℍ) := rfl

theorem standardActionL2_norm
    (p : symplecticKernel S × unitary ℍ)
    (z : StandardSpace (E := E)) :
    ‖standardActionL2 S p z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2,
    standardActionL2_fst, standardActionL2_snd,
    p.1.1.1.norm_map]
  have hw := rightStarEquiv_norm p.2 z.snd
  rw [rightStarEquiv_apply] at hw
  rw [hw]

def standardIsometryL2 :
    (symplecticKernel S × unitary ℍ) →*
      ((StandardSpace (E := E)) ≃ₗᵢ[ℝ] (StandardSpace (E := E))) where
  toFun p := LinearIsometryEquiv.mk
    (standardActionL2 S p).toLinearEquiv (standardActionL2_norm S p)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro z
    change standardActionL2 S 1 z = z
    simp only [standardActionL2, map_one]
    exact (coordinateEquiv (E := E)).symm_apply_apply z
  map_mul' p r := by
    apply LinearIsometryEquiv.ext
    intro z
    change standardActionL2 S (p * r) z =
      standardActionL2 S p (standardActionL2 S r z)
    simp only [standardActionL2, map_mul]
    rfl

@[simp] theorem standardIsometryL2_apply
    (p : symplecticKernel S × unitary ℍ)
    (z : StandardSpace (E := E)) :
    standardIsometryL2 S p z = standardActionL2 S p z := rfl

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardL2
