import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize

/-! Every unit vector is a column of a unitary matrix, by extending its
singleton orthonormal family to an orthonormal basis. -/

namespace QuaternionicSymmetry.UnitaryTransitivity

open Matrix
open scoped InnerProductSpace

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem exists_unitary_column (v : EuclideanSpace ℂ κ) (hv : ‖v‖ = 1) (i₀ : κ) :
    ∃ U : Matrix.unitaryGroup κ ℂ, ∀ i, (U : Matrix κ κ ℂ) i i₀ = v i := by
  have ho : Orthonormal ℂ (({i₀} : Set κ).restrict (fun _ => v)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.property).trans
        (Set.mem_singleton_iff.mp j.property).symm
    subst j
    simp only [Set.restrict_apply, if_true]
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card κ)
  let e := EuclideanSpace.basisFun κ ℂ
  refine ⟨⟨e.toBasis.toMatrix b, e.toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  intro i
  change e.repr (b i₀) i = v i
  rw [hb i₀ (by simp)]
  rfl

theorem exists_unitary_mulVec_single (v : EuclideanSpace ℂ κ) (hv : ‖v‖ = 1) (i₀ : κ) :
    ∃ U : Matrix.unitaryGroup κ ℂ,
      (U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1 = fun i => v i := by
  obtain ⟨U, hU⟩ := exists_unitary_column v hv i₀
  refine ⟨U, ?_⟩
  funext i
  simpa using hU i

theorem exists_unitary_scaled_column (v : EuclideanSpace ℂ κ) (i₀ : κ) :
    ∃ U : Matrix.unitaryGroup κ ℂ,
      (fun i => v i) = ‖v‖ • ((U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1) := by
  by_cases hv : v = 0
  · refine ⟨1, ?_⟩
    simp [hv]
    rfl
  · obtain ⟨U, hU⟩ := exists_unitary_mulVec_single
      (NormedSpace.normalize v) (NormedSpace.norm_normalize hv) i₀
    refine ⟨U, ?_⟩
    rw [hU]
    funext i
    have h := congrArg (fun x : EuclideanSpace ℂ κ => x i)
      (NormedSpace.norm_smul_normalize v)
    exact h.symm

end
end QuaternionicSymmetry.UnitaryTransitivity
