import QuaternionicSymmetry.ComplexProjectiveTopology

/-! Standard affine coordinates on the quotient model of complex projective space. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped LinearAlgebra.Projectivization

/-- The affine coordinate hyperplane in which the `i`-th coordinate is one. -/
def affineHyperplane (d : ℕ) (i : Fin (d + 1)) : Set (Coord d) :=
  {v | v i = 1}

/-- Divide every homogeneous coordinate by the chosen nonzero coordinate. -/
noncomputable def affineRatio (d : ℕ) (i : Fin (d + 1))
    (p : {p : Space d // p ∈ affineDomain d i}) : Coord d :=
  fun j => p.1.rep j / p.1.rep i

theorem affineRatio_mem (d : ℕ) (i : Fin (d + 1))
    (p : {p : Space d // p ∈ affineDomain d i}) :
    affineRatio d i p ∈ affineHyperplane d i := by
  change p.1.rep i / p.1.rep i = 1
  exact div_self p.2

/-- The inverse homogeneous-coordinate construction is genuinely projective. -/
noncomputable def affinePoint (d : ℕ) (i : Fin (d + 1))
    (v : affineHyperplane d i) : Space d :=
  Projectivization.mk ℂ v.1 (by
    intro hv
    have hi : v.1 i = 1 := v.2
    simp [hv] at hi)

theorem affinePoint_mem (d : ℕ) (i : Fin (d + 1))
    (v : affineHyperplane d i) :
    affinePoint d i v ∈ affineDomain d i := by
  rw [affinePoint]
  rw [mem_affineDomain_mk]
  exact v.2 ▸ one_ne_zero

/-- The ratio vector regarded as a point of the affine coordinate hyperplane. -/
noncomputable def affineChart (d : ℕ) (i : Fin (d + 1))
    (p : {p : Space d // p ∈ affineDomain d i}) : affineHyperplane d i :=
  ⟨affineRatio d i p, affineRatio_mem d i p⟩

/-- The projective point associated to an affine vector lies in its chart. -/
noncomputable def affineChartInv (d : ℕ) (i : Fin (d + 1))
    (v : affineHyperplane d i) : {p : Space d // p ∈ affineDomain d i} :=
  ⟨affinePoint d i v, affinePoint_mem d i v⟩

theorem affineChart_left_inv (d : ℕ) (i : Fin (d + 1))
    (v : affineHyperplane d i) :
    affineChart d i (affineChartInv d i v) = v := by
  apply Subtype.ext
  funext j
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1 (by
    intro hv
    have hi : v.1 i = 1 := v.2
    simp [hv] at hi)
  have hj := congrFun ha j
  have hi := congrFun ha i
  change (Projectivization.mk ℂ v.1 _).rep j /
    (Projectivization.mk ℂ v.1 _).rep i = v.1 j
  rw [← hj, ← hi]
  change ((a : ℂ) * v.1 j) / ((a : ℂ) * v.1 i) = v.1 j
  rw [v.2, mul_one]
  field_simp [a.ne_zero]

theorem affineChart_right_inv (d : ℕ) (i : Fin (d + 1))
    (p : {p : Space d // p ∈ affineDomain d i}) :
    affineChartInv d i (affineChart d i p) = p := by
  apply Subtype.ext
  change Projectivization.mk ℂ (affineRatio d i p) _ = p.1
  rw [← Projectivization.mk_rep p.1]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(p.1.rep i)⁻¹, ?_⟩
  funext j
  simp [affineRatio, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The standard affine coordinate bijection, before proving topological regularity. -/
noncomputable def affineChartEquiv (d : ℕ) (i : Fin (d + 1)) :
    {p : Space d // p ∈ affineDomain d i} ≃ affineHyperplane d i where
  toFun := affineChart d i
  invFun := affineChartInv d i
  left_inv := affineChart_right_inv d i
  right_inv := affineChart_left_inv d i

end QuaternionicSymmetry.ComplexProjectiveTopology
