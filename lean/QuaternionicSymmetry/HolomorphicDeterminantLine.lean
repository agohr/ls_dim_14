import QuaternionicSymmetry.HolomorphicLinePowers
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Determinant line of a genuine finite-rank complex vector-bundle core.
The transition is the determinant of the original complex-linear
transition, so the cocycle is derived rather than supplied. -/

namespace QuaternionicSymmetry.HolomorphicDeterminantLine

open scoped Manifold ContDiff
noncomputable section

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {ι : Type*} (Z : VectorBundleCore ℂ B F ι)

/-- Determinant is a holomorphic polynomial on the finite-dimensional
space of complex-linear endomorphisms. -/
theorem contDiff_det : ContDiff ℂ ∞
    (fun T : F →L[ℂ] F => T.det) := by
  let b := Module.finBasis ℂ F
  let mat : (F →L[ℂ] F) → Matrix (Fin (Module.finrank ℂ F))
      (Fin (Module.finrank ℂ F)) ℂ :=
    fun T => LinearMap.toMatrix b b (T : F →ₗ[ℂ] F)
  have hentry (i j : Fin (Module.finrank ℂ F)) :
      ContDiff ℂ ∞ (fun T : F →L[ℂ] F => mat T i j) := by
    have hcoord : ContDiff ℂ ∞
        (fun v : F => (b.coord i) v) :=
      ((b.coord i).toContinuousLinearMap).contDiff
    have happly : ContDiff ℂ ∞
        (fun T : F →L[ℂ] F => T (b j)) :=
      contDiff_id.clm_apply contDiff_const
    simpa only [mat, LinearMap.toMatrix_apply, Module.Basis.coord_apply] using
      hcoord.comp happly
  have hprod (σ : Equiv.Perm (Fin (Module.finrank ℂ F)))
      (s : Finset (Fin (Module.finrank ℂ F))) :
      ContDiff ℂ ∞
        (fun T : F →L[ℂ] F => ∏ i ∈ s, mat T (σ i) i) := by
    induction s using Finset.induction with
    | empty => simpa using (contDiff_const : ContDiff ℂ ∞
        (fun _ : F →L[ℂ] F => (1 : ℂ)))
    | @insert i s hi ih =>
        simpa only [Finset.prod_insert hi] using (hentry (σ i) i).mul ih
  have hmatrix : ContDiff ℂ ∞ (fun T : F →L[ℂ] F => (mat T).det) := by
    simp_rw [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    exact contDiff_const.mul (hprod σ Finset.univ)
  simpa only [mat, LinearMap.det_toMatrix] using hmatrix

/-- Determinant scalar of the transition of a complex vector bundle. -/
def transitionDet (i j : ι) (x : B) : ℂ := (Z.coordChange i j x).det

/-- The top exterior power, represented as a one-dimensional complex
vector-bundle core. -/
def determinantCore : VectorBundleCore ℂ B ℂ ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := transitionDet Z i j x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    have h : Z.coordChange i i x = ContinuousLinearMap.id ℂ F := by
      ext w
      exact Z.coordChange_self i x hx w
    change (transitionDet Z i i x • ContinuousLinearMap.id ℂ ℂ) v = v
    rw [show transitionDet Z i i x = 1 by
      change (Z.coordChange i i x).det = 1
      rw [h]
      exact LinearMap.det_id]
    simp only [one_smul, ContinuousLinearMap.id_apply]
  continuousOn_coordChange i j := by
    have h : ContinuousOn (transitionDet Z i j) (Z.baseSet i ∩ Z.baseSet j) :=
      ContinuousLinearMap.continuous_det.comp_continuousOn
        (Z.continuousOn_coordChange i j)
    exact h.smul continuousOn_const
  coordChange_comp i j k x hx v := by
    have hcomp : (Z.coordChange j k x).comp (Z.coordChange i j x) =
        Z.coordChange i k x := by
      ext w
      exact Z.coordChange_comp i j k x hx w
    have hs : transitionDet Z j k x * transitionDet Z i j x =
        transitionDet Z i k x := by
      change LinearMap.det (Z.coordChange j k x : F →ₗ[ℂ] F) *
        LinearMap.det (Z.coordChange i j x : F →ₗ[ℂ] F) =
        LinearMap.det (Z.coordChange i k x : F →ₗ[ℂ] F)
      rw [← LinearMap.det_comp]
      apply congrArg LinearMap.det
      ext w
      exact Z.coordChange_comp i j k x hx w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    calc
      transitionDet Z j k x * (transitionDet Z i j x * v) =
          (transitionDet Z j k x * transitionDet Z i j x) * v := by ring
      _ = transitionDet Z i k x * v := by rw [hs]

variable {H G : Type*} [TopologicalSpace H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ G H}

instance determinantCore_isContMDiff [Z.IsContMDiff IB ∞] :
    (determinantCore Z).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j := by
    have h : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
        (transitionDet Z i j) (Z.baseSet i ∩ Z.baseSet j) := by
      exact (contDiff_det (F := F)).contMDiff.comp_contMDiffOn
        (Z.contMDiffOn_coordChange IB i j)
    exact h.smul contMDiffOn_const

end
end QuaternionicSymmetry.HolomorphicDeterminantLine
