import QuaternionicSymmetry.ProjectiveLineHyperplaneCore
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Literal derivatives of CP¹ affine coordinate changes. The off-diagonal
tangent determinant transition is minus the square of the O(1) transition. -/

namespace QuaternionicSymmetry.ProjectiveLineTangentTransitions

open scoped Manifold ContDiff Topology
open ComplexProjectiveTopology FourDimensionalHalfSpinProjective
open ProjectiveLineTangentDeterminant ProjectiveLineHyperplaneCore
open HolomorphicDeterminantLine HolomorphicRankOneDeterminant
noncomputable section

def chartIndex (i : Fin 2) : atlas Model ProjectiveSpinor :=
  ⟨projectiveChart 1 i, ⟨i,rfl⟩⟩

theorem transition_distinct (i j : Fin 2) (hij : i ≠ j) (w : Model) :
    euclideanTransition 1 i j w = fun _ => (w 0)⁻¹ := by
  funext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [euclideanTransition, Fin.insertNth, Fin.succAbove]
  rfl

theorem overlap_distinct (i j : Fin 2) (hij : i ≠ j) (w : Model) :
    w ∈ euclideanOverlap 1 i j ↔ w 0 ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [euclideanOverlap, Fin.insertNth]
  rfl

def inverseDerivative (w : Model) : Model →L[ℂ] Model :=
  ContinuousLinearMap.pi (fun _ : Fin 1 =>
    (ContinuousLinearMap.toSpanSingleton ℂ (-(w 0 ^ 2)⁻¹)).comp
      (ContinuousLinearMap.proj 0))

theorem inverse_hasFDerivAt (w : Model) (hw : w 0 ≠ 0) :
    HasFDerivAt (fun z : Model => fun _ : Fin 1 => (z 0)⁻¹)
      (inverseDerivative w) w := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hasFDerivAt_inv hw).comp w (hasFDerivAt_apply 0 w)

theorem chart_overlap (i j : Fin 2) (p : ProjectiveSpinor)
    (hi : p ∈ affineDomain 1 i) (hj : p ∈ affineDomain 1 j) :
    projectiveChart 1 i p ∈ euclideanOverlap 1 i j := by
  rw [← projectiveChart_transition_source]
  refine ⟨?_,?_⟩
  · exact (projectiveChart 1 i).map_source (by simpa [projectiveChart_source] using hi)
  · change (projectiveChart 1 i).symm (projectiveChart 1 i p) ∈
      (projectiveChart 1 j).source
    rw [(projectiveChart 1 i).left_inv (by simpa [projectiveChart_source] using hi)]
    simpa [projectiveChart_source] using hj

theorem tangent_transition_derivative_distinct (i j : Fin 2) (hij : i ≠ j)
    (p : ProjectiveSpinor) (hi : p ∈ affineDomain 1 i)
    (hj : p ∈ affineDomain 1 j) :
    tangentCore.coordChange (chartIndex i) (chartIndex j) p =
      inverseDerivative (projectiveChart 1 i p) := by
  let w := projectiveChart 1 i p
  have hw := chart_overlap i j p hi hj
  have hn : w 0 ≠ 0 := (overlap_distinct i j hij w).mp hw
  have hg : ((projectiveChart 1 j) ∘ (projectiveChart 1 i).symm) =ᶠ[𝓝 w]
      (fun z : Model => fun _ : Fin 1 => (z 0)⁻¹) := by
    filter_upwards [(isOpen_euclideanOverlap 1 i j).mem_nhds hw] with z hz
    exact (projectiveChart_transition_apply 1 i j z hz).trans
      (transition_distinct i j hij z)
  change fderivWithin ℂ
    ((projectiveChart 1 j).extend 𝓘(ℂ,Model) ∘
      ((projectiveChart 1 i).extend 𝓘(ℂ,Model)).symm)
    (Set.range (𝓘(ℂ,Model))) ((projectiveChart 1 i).extend 𝓘(ℂ,Model) p) = _
  simp only [mfld_simps]
  rw [fderivWithin_univ, hg.fderiv_eq]
  exact (inverse_hasFDerivAt w hn).fderiv

theorem tangent_determinant_transition_distinct (i j : Fin 2) (hij : i ≠ j)
    (p : ProjectiveSpinor) (hi : p ∈ affineDomain 1 i)
    (hj : p ∈ affineDomain 1 j) :
    transitionDet tangentCore (chartIndex i) (chartIndex j) p =
      -(hyperplaneTransition i j p)^2 := by
  change (tangentCore.coordChange (chartIndex i) (chartIndex j) p).det = _
  rw [tangent_transition_derivative_distinct i j hij p hi hj, det_eq_scalar]
  simp only [inverseDerivative, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, one_mul]
  rw [projectiveChart_coordinate i p hi]
  have he : i.succAbove 0 = j := by fin_cases i <;> fin_cases j <;> simp_all
  rw [he]
  change -((p.rep j / p.rep i)^2)⁻¹ = -(p.rep i / p.rep j)^2
  have hpi : p.rep i ≠ 0 := hi
  have hpj : p.rep j ≠ 0 := hj
  field_simp [hpi,hpj]

end
end QuaternionicSymmetry.ProjectiveLineTangentTransitions
