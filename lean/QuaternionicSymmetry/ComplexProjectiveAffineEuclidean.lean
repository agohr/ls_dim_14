import QuaternionicSymmetry.ComplexProjectiveAffineTopology
import Mathlib.Data.Fin.Tuple.Basic

/-! Each affine hyperplane is canonically homeomorphic to `Fin d → ℂ`. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

private theorem insertNth_one_mem (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) : Fin.insertNth i 1 w ∈ affineHyperplane d i := by
  simp [affineHyperplane]

noncomputable def affineHyperplaneEquiv (d : ℕ) (i : Fin (d + 1)) :
    affineHyperplane d i ≃ (Fin d → ℂ) where
  toFun v := Fin.removeNth i v.1
  invFun w := ⟨Fin.insertNth i 1 w, insertNth_one_mem d i w⟩
  left_inv v := by
    apply Subtype.ext
    exact ((Fin.eq_insertNth_iff).2 ⟨v.2, rfl⟩).symm
  right_inv w := by simp

theorem continuous_affineHyperplaneEquiv (d : ℕ) (i : Fin (d + 1)) :
    Continuous (affineHyperplaneEquiv d i) := by
  apply continuous_pi
  intro j
  exact (continuous_apply (i.succAbove j)).comp continuous_subtype_val

theorem continuous_affineHyperplaneEquiv_symm (d : ℕ) (i : Fin (d + 1)) :
    Continuous (affineHyperplaneEquiv d i).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases hij : j = i
  · subst j
    simpa [affineHyperplaneEquiv] using (continuous_const : Continuous (fun _ : Fin d → ℂ => (1 : ℂ)))
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    rw [← hk]
    simpa [affineHyperplaneEquiv, Fin.insertNth_apply_succAbove] using (continuous_apply k :
      Continuous (fun w : Fin d → ℂ => w k))

noncomputable def affineEuclideanHomeomorph (d : ℕ) (i : Fin (d + 1)) :
    {p : Space d // p ∈ affineDomain d i} ≃ₜ (Fin d → ℂ) :=
  (affineChartHomeomorph d i).trans
    { toEquiv := affineHyperplaneEquiv d i
      continuous_toFun := continuous_affineHyperplaneEquiv d i
      continuous_invFun := continuous_affineHyperplaneEquiv_symm d i }

end QuaternionicSymmetry.ComplexProjectiveTopology
