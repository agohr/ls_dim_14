import QuaternionicSymmetry.CompactSymplecticFirstBlockCoordinates

/-! The finite coordinate permutation identifies the first stabilizer block
with the actual `CompactSymplecticHaar.Group 1`. -/

namespace QuaternionicSymmetry.CompactSymplecticFirstBlockGroup

open Matrix CompactSymplecticHaar
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerFormBlocks
open CompactSymplecticFirstBlockCoordinates
noncomputable section

private theorem unitary_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    A.reindex e e ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) hA
  rw [Matrix.reindexAlgEquiv_mul] at h
  simpa only [Matrix.reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_reindex, map_one] using h

private theorem form_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (A J : Matrix ι ι ℂ) (h : Aᵀ * J * A = J) :
    (A.reindex e e)ᵀ * J.reindex e e * A.reindex e e =
      J.reindex e e := by
  have h' := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) h
  rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul] at h'
  simpa only [Matrix.reindexAlgEquiv_apply, Matrix.transpose_reindex] using h'

private def toFirstBlock (u : CompactSymplecticHaar.Group 1) : FirstBlockGroup := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    (u.1.1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ).reindex
      pairIndexEquiv pairIndexEquiv
  have hunit : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    unitary_reindex pairIndexEquiv _ u.1.property
  have hform : Aᵀ * firstBlockJ * A = firstBlockJ := by
    rw [firstBlockJ_eq_reindex_standardJ_one]
    exact form_reindex pairIndexEquiv _ _ u.2
  exact ⟨⟨A, hunit⟩, hform⟩

private def fromFirstBlock (u : FirstBlockGroup) :
    CompactSymplecticHaar.Group 1 := by
  let A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    (u.1.1 : Matrix (Fin 2) (Fin 2) ℂ).reindex
      pairIndexEquiv.symm pairIndexEquiv.symm
  have hunit : A ∈ Matrix.unitaryGroup (Fin 1 ⊕ Fin 1) ℂ :=
    unitary_reindex pairIndexEquiv.symm _ u.1.property
  have hJ : firstBlockJ.reindex pairIndexEquiv.symm
      pairIndexEquiv.symm = standardJ 1 := by
    rw [firstBlockJ_eq_reindex_standardJ_one]
    ext i j
    simp [Matrix.reindex_apply]
  have hform : Aᵀ * standardJ 1 * A = standardJ 1 := by
    rw [← hJ]
    exact form_reindex pairIndexEquiv.symm _ _ u.2
  exact ⟨⟨A, hunit⟩, hform⟩

/-- Explicit matrix-coordinate group equivalence, not a name assigned to
an unrelated abstract group. -/
def firstBlockGroupEquiv : CompactSymplecticHaar.Group 1 ≃* FirstBlockGroup where
  toFun := toFirstBlock
  invFun := fromFirstBlock
  left_inv := by
    intro u
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    simp [toFirstBlock, fromFirstBlock, Matrix.reindex_apply]
  right_inv := by
    intro u
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    simp [toFirstBlock, fromFirstBlock, Matrix.reindex_apply]
  map_mul' := by
    intro u v
    apply Subtype.ext
    apply Subtype.ext
    change ((u.1.1 * v.1.1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ).reindex
      pairIndexEquiv pairIndexEquiv) =
      (u.1.1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ).reindex
        pairIndexEquiv pairIndexEquiv *
      (v.1.1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ).reindex
        pairIndexEquiv pairIndexEquiv
    exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ pairIndexEquiv) _ _

end
end QuaternionicSymmetry.CompactSymplecticFirstBlockGroup
