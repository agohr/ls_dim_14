import QuaternionicSymmetry.QuaternionicPencilPolynomial
import QuaternionicSymmetry.ExteriorNonvanishing

/-!
  The global block volume as a concrete exterior product.

  This file records the ordered generator representative of the unordered
  product of even block volumes.  It is the bridge needed to apply the
  exterior-power basis to the global volume.
-/

namespace QuaternionicSymmetry
namespace QuaternionicBlockVolume

open scoped BigOperators
open QuaternionicBlocks QuaternionicBlockPencil QuaternionicPencilPolynomial

noncomputable section

/-- The coordinate vectors in the block-by-block order. -/
def blockVectorList (n : ℕ) : List (V (Fin n)) :=
  (List.finRange n).flatMap fun j =>
    [insert j (FourDimensionalForms.e 0), insert j (FourDimensionalForms.e 1),
      insert j (FourDimensionalForms.e 2), insert j (FourDimensionalForms.e 3)]

/-- The finite family enumerating `blockVectorList`. -/
def blockFamily (n : ℕ) : Fin (blockVectorList n).length → V (Fin n) :=
  (blockVectorList n).get

/-- The index list corresponding to the block-by-block coordinate order. -/
def blockIndexList (n : ℕ) : List (Fin n × Fin 4) :=
  (List.finRange n).product (List.finRange 4)

/-- The same family, directly as a reindexing of the standard coordinate basis. -/
def basisBlockFamily (n : ℕ) : Fin (blockIndexList n).length → V (Fin n) :=
  (Pi.basisFun ℝ (Fin n × Fin 4)) ∘ (blockIndexList n).get

private theorem blockVector_eq_basis {n : ℕ} (j : Fin n) (k : Fin 4) :
    QuaternionicBlocks.insert j (FourDimensionalForms.e k) =
      Pi.basisFun ℝ (Fin n × Fin 4) (j, k) := by
  ext p
  rcases p with ⟨p, q⟩
  by_cases h : p = j
  · subst p
    by_cases hk : q = k
    · subst q
      simp [QuaternionicBlocks.insert, FourDimensionalForms.e, Pi.basisFun_apply]
    · simp [QuaternionicBlocks.insert, FourDimensionalForms.e, Pi.basisFun_apply, hk]
  · have hp : (p, q) ≠ (j, k) := fun h' => h (congrArg Prod.fst h')
    simp [QuaternionicBlocks.insert, Pi.basisFun_apply, h, hp]

theorem blockVectorList_eq_basis_map (n : ℕ) :
    blockVectorList n = (blockIndexList n).map (Pi.basisFun ℝ (Fin n × Fin 4)) := by
  simp only [blockVectorList, blockIndexList, List.product, List.map_flatMap, List.map_map]
  simp_rw [blockVector_eq_basis]
  apply List.flatMap_congr
  intro a _
  rfl

theorem basisBlockFamily_linearIndependent (n : ℕ) :
    LinearIndependent ℝ (basisBlockFamily n) := by
  apply (Pi.basisFun ℝ (Fin n × Fin 4)).linearIndependent.comp
  exact List.nodup_iff_injective_get.mp
    ((List.nodup_finRange n).product (List.nodup_finRange 4))

private theorem list_prod_flatMap {α γ : Type*} [Monoid γ] (l : List α) (f : α → List γ) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

private theorem blockVectorList_prod (n : ℕ) :
    (List.map (ExteriorAlgebra.ι ℝ) (blockVectorList n)).prod =
      (List.map (fun j : Fin n => vol j) (List.finRange n)).prod := by
  rw [blockVectorList, List.map_flatMap, list_prod_flatMap]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vol_eq, g, mul_assoc,
    mul_one]

/-- For finitely many coordinate blocks, the product of their actual volume
forms is an `ιMulti` product of the ordered coordinate generators. -/
theorem volume_fin_eq_iMulti (n : ℕ) :
    (volume (β := Fin n) : E (Fin n)) =
      ExteriorAlgebra.ιMulti ℝ (blockVectorList n).length (blockFamily n) := by
  calc
    (volume (β := Fin n) : E (Fin n)) =
        (List.map (fun j : Fin n => vol j) (List.finRange n)).prod := by
      rw [volume]
      rw [Fin.prod_univ_def]
      change (EvenForms.evenSubalgebra ℝ (V (Fin n))).val
          ((List.map volEven (List.finRange n)).prod) = _
      rw [map_list_prod]
      rw [List.map_map]
      rfl
    _ = (List.map (ExteriorAlgebra.ι ℝ) (blockVectorList n)).prod :=
      (blockVectorList_prod n).symm
    _ = ExteriorAlgebra.ιMulti ℝ (blockVectorList n).length (blockFamily n) := by
      rw [ExteriorAlgebra.ιMulti_apply]
      apply congrArg List.prod
      simpa only [blockFamily, List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map (blockVectorList n) (ExteriorAlgebra.ι ℝ)).symm

/-- The preceding `ιMulti` representative written directly as a reindexing of
the coordinate basis. -/
theorem volume_fin_eq_iMulti_basis (n : ℕ) :
    (volume (β := Fin n) : E (Fin n)) =
      ExteriorAlgebra.ιMulti ℝ (blockIndexList n).length (basisBlockFamily n) := by
  calc
    (volume (β := Fin n) : E (Fin n)) =
        ExteriorAlgebra.ιMulti ℝ (blockVectorList n).length (blockFamily n) :=
      volume_fin_eq_iMulti n
    _ = (List.map (ExteriorAlgebra.ι ℝ) (blockVectorList n)).prod := by
      rw [ExteriorAlgebra.ιMulti_apply]
      apply congrArg List.prod
      simpa only [blockFamily, List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map (blockVectorList n) (ExteriorAlgebra.ι ℝ))
    _ = (List.map (ExteriorAlgebra.ι ℝ)
        ((blockIndexList n).map (Pi.basisFun ℝ (Fin n × Fin 4)))).prod := by
      rw [← blockVectorList_eq_basis_map]
    _ = ExteriorAlgebra.ιMulti ℝ (blockIndexList n).length (basisBlockFamily n) := by
      rw [ExteriorAlgebra.ιMulti_apply]
      apply congrArg List.prod
      simpa only [basisBlockFamily, List.get_eq_getElem, List.map_map] using
        (List.ofFn_getElem_eq_map (blockIndexList n)
          (fun v => ExteriorAlgebra.ι ℝ ((Pi.basisFun ℝ (Fin n × Fin 4)) v))).symm

/-- The actual global block volume is nonzero in every finite coordinate model. -/
theorem volume_fin_ne_zero (n : ℕ) :
    (volume (β := Fin n) : E (Fin n)) ≠ 0 := by
  rw [volume_fin_eq_iMulti_basis]
  exact ExteriorNonvanishing.iMulti_ne_zero _ (basisBlockFamily_linearIndependent n)

end
end QuaternionicBlockVolume
end QuaternionicSymmetry
