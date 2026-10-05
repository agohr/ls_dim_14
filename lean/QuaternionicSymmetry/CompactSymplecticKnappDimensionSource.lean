import QuaternionicSymmetry.CompactSymplecticStabilizerDimensionTransfer

/-! Precise primary-source boundary for the dimension of the *actual*
unitary-symplectic matrix group. Knapp, *Lie Groups Beyond an
Introduction*, 2nd ed., I§17 pp.113–114 after Proposition 1.136 and
Proposition 1.139, identifies compact `Sp(k)` with
`Sp(k,ℂ) ∩ U(2k)` in the same standard matrix form; VI§1 Theorem 6.11,
Remark 1 p.353 identifies its Lie algebra as the compact real form of
`sp(k,ℂ)`; Appendix C§1 p.685 gives complex dimension `k(2k+1)`.
Together these give an actual real smooth manifold atlas of that
dimension on our checked matrix subgroup, for `k ≥ 1`.

The theorem is an explicit literature argument. It asserts no
dimension of the projector stabilizer, quotient, or Wolf model. -/

namespace QuaternionicSymmetry.CompactSymplecticKnappDimensionSource

open Manifold
open scoped Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- Actual compact symplectic matrix group endowed with a standard
real manifold atlas of the Knapp dimension. -/
structure KnappMatrixAtlas (k : ℕ) where
  charts : ChartedSpace (RModel (k * (2 * k + 1)))
    (CompactSymplecticHaar.Group k)
  manifold : letI := charts
    IsManifold 𝓘(ℝ, RModel (k * (2 * k + 1))) ∞
      (CompactSymplecticHaar.Group k)
  lieGroup : letI := charts
    LieGroup 𝓘(ℝ, RModel (k * (2 * k + 1))) ∞
      (CompactSymplecticHaar.Group k)

/-- Knapp's dimension computation attached to the concrete matrix
group, with `k ≥ 1` visible. -/
def KnappCompactSymplecticMatrixDimension : Prop :=
  ∀ k : ℕ, 0 < k → Nonempty (KnappMatrixAtlas k)

end
end QuaternionicSymmetry.CompactSymplecticKnappDimensionSource
