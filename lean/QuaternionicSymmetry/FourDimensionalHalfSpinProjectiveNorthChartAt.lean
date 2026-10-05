import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartDerivative

/-! At the true north projective spinor, the independent CP¹ charted-space
instance must select the `[1:z]` chart: its other affine chart is undefined
there. This removes any hidden choice of an unrelated local coordinate in
the subsequent manifold derivative comparison. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartAt

open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveNorthDerivative
  ComplexProjectiveTopology

noncomputable section

theorem north_not_second_affine :
    affineSpinorPoint 0 ∉ affineDomain 1 1 := by
  unfold affineSpinorPoint
  rw [mem_affineDomain_mk]
  simp

theorem north_chartAt :
    chartAt (Fin 1 → ℂ) (affineSpinorPoint 0) =
      projectiveChart 1 0 := by
  let i : Fin 2 := Classical.choose (exists_mem_affineDomain 1 (affineSpinorPoint 0))
  have hi : affineSpinorPoint 0 ∈ affineDomain 1 i :=
    Classical.choose_spec (exists_mem_affineDomain 1 (affineSpinorPoint 0))
  have hiz : i = 0 := by
    apply Fin.ext
    by_contra hne
    have hval : i.val = 1 := by omega
    have hii : i = 1 := Fin.ext hval
    exact north_not_second_affine (by simpa [hii] using hi)
  change projectiveChart 1 i = projectiveChart 1 0
  rw [hiz]

theorem north_chart_coordinate :
    (chartAt (Fin 1 → ℂ) (affineSpinorPoint 0))
      (affineSpinorPoint 0) = 0 := by
  rw [north_chartAt, affineSpinorPoint_eq_projectiveChart]
  have hzero : (![0] : Fin 1 → ℂ) = 0 := by
    funext i
    fin_cases i
    simp
  rw [hzero]
  have htarget : (0 : Fin 1 → ℂ) ∈ (projectiveChart 1 0).target := by
    simp [projectiveChart_target]
  exact (projectiveChart 1 0).right_inv htarget

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartAt
