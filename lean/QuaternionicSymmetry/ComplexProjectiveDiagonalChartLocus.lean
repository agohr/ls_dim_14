import QuaternionicSymmetry.ComplexProjectiveDiagonalAffineChartComorphism
import QuaternionicSymmetry.ComplexProjectiveTorusPreservation

/-! The exact affine-chart loci of an invariant homogeneous projective
cutout are preserved by the literal regular diagonal chart formulas. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartLocus

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalChartFormula
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def chartLocus (A : Set (Space d)) (i : Fin (d + 1)) : Set (Fin d → ℂ) :=
  {w | (projectiveChart d i).symm w ∈ A}

theorem chartDiagonal_maps_chartLocus
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (A : Set (Space d))
    (hA : Set.MapsTo (projectiveAction μ z) A A)
    (i : Fin (d + 1)) :
    Set.MapsTo (chartDiagonal μ z i) (chartLocus A i) (chartLocus A i) := by
  intro w hw
  change (projectiveChart d i).symm (chartDiagonal μ z i w) ∈ A
  have hp : (projectiveChart d i).symm w ∈ affineDomain d i := by
    rw [← projectiveChart_source]
    exact (projectiveChart d i).map_target (by simp [projectiveChart_target])
  have htarget : projectiveAction μ z ((projectiveChart d i).symm w) ∈
      affineDomain d i :=
    (projectiveAction_mem_affineDomain_iff μ z i _).2 hp
  have hchart := chart_projectiveAction μ z i _ hp
  rw [(projectiveChart d i).right_inv (by simp [projectiveChart_target])] at hchart
  have hback := (projectiveChart d i).left_inv (by
    simpa [projectiveChart_source] using htarget)
  rw [hchart] at hback
  change (projectiveChart d i).symm (chartDiagonal μ z i w) =
    projectiveAction μ z ((projectiveChart d i).symm w) at hback
  rw [hback]
  exact hA hw

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartLocus
