import QuaternionicSymmetry.ComplexProjectiveDiagonalAction
import QuaternionicSymmetry.ComplexProjectiveAffineTopology

/-! A diagonal complex-torus projective map preserves every standard affine
chart, with explicit holomorphic coordinate ratios. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartFormula

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open TorusLaurentRepresentation
open scoped LinearAlgebra.Projectivization
noncomputable section

theorem projectiveAction_mem_affineDomain_iff {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (i : Fin (d + 1)) (p : Space d) :
    projectiveAction μ z p ∈ affineDomain d i ↔ p ∈ affineDomain d i := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveAction_mk, mem_affineDomain_mk, mem_affineDomain_mk]
    simp [diagonalEquiv_apply, (complexWeightCharacter (μ i) z).ne_zero]

theorem affineRatio_projectiveAction {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (i j : Fin (d + 1)) (p : Space d) (hp : p ∈ affineDomain d i) :
    affineRatio d i
      ⟨projectiveAction μ z p,
        (projectiveAction_mem_affineDomain_iff μ z i p).2 hp⟩ j =
      ((complexWeightCharacter (μ j) z : ℂ) /
        (complexWeightCharacter (μ i) z : ℂ)) *
        affineRatio d i ⟨p,hp⟩ j := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hvi : v i ≠ 0 :=
      (mem_affineDomain_mk d i v hv).1 hp
    have hwi : diagonalEquiv μ z v i ≠ 0 := by
      simpa [diagonalEquiv_apply] using
        mul_ne_zero (complexWeightCharacter (μ i) z).ne_zero hvi
    have hsub :
        (⟨projectiveAction μ z (Projectivization.mk ℂ v hv),
          (projectiveAction_mem_affineDomain_iff μ z i _).2 hp⟩ :
          affineDomain d i) =
        ⟨Projectivization.mk ℂ (diagonalEquiv μ z v)
          ((diagonalEquiv μ z).map_ne_zero_iff.mpr hv),
          (mem_affineDomain_mk d i (diagonalEquiv μ z v)
            ((diagonalEquiv μ z).map_ne_zero_iff.mpr hv)).2 hwi⟩ := by
      apply Subtype.ext
      exact projectiveAction_mk μ z v hv
    rw [hsub,
      affineRatio_mk d i j (diagonalEquiv μ z v)
        ((diagonalEquiv μ z).map_ne_zero_iff.mpr hv) hwi,
      affineRatio_mk d i j v hv hvi]
    simp only [diagonalEquiv_apply]
    field_simp [(complexWeightCharacter (μ i) z).ne_zero, hvi]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartFormula
