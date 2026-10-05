import QuaternionicSymmetry.QuaternionicStandardSolderEquivariance
import QuaternionicSymmetry.QuaternionicProjectiveStandardSkew
import QuaternionicSymmetry.QuaternionicProjectiveStandardLie

/-! Infinitesimal equivariance of the off-diagonal standard solder. -/
namespace QuaternionicSymmetry.QuaternionicStandardSolderInfinitesimal
open QuaternionicStandardSolderOperator QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardSkew QuaternionicLieAlgebraProjection
open QuaternionicUnitScalarIsometries VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardL2.StandardSpace (E := E)) := inferInstance

private theorem column_infinitesimal (A : E →L[ℝ] E) (v : E) (w : ℍ)
    (hI : ∀ z, (symplecticProjection S A) (S.I z) = S.I ((symplecticProjection S A) z))
    (hJ : ∀ z, (symplecticProjection S A) (S.J z) = S.J ((symplecticProjection S A) z)) :
    (symplecticProjection S A) (column S v w) -
      column S v (scalarLineLie S A w) = column S (A v) w := by
  let H := symplecticProjection S A
  let a := axialProjection (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)
  let ell := imaginary a
  have hc : H (S.action w v) = S.action w (H v) :=
    S.action_commutes H.toLinearMap hI hJ w v
  have hscalar : (scalarProjection S A) v = S.action ell v := by
    change (synth S a) v = S.action (pureScalar a) v
    exact (action_pureScalar S a v).symm
  have hsum := congrArg (fun T : E →L[ℝ] E => T v) (projection_sum S A)
  have hsum' : H v + (scalarProjection S A) v = A v := by
    simpa only [ContinuousLinearMap.add_apply] using hsum
  change H (S.action w v) - S.action (w * -ell) v = S.action w (A v)
  rw [hc, mul_neg]
  simp only [map_neg, LinearMap.neg_apply, sub_neg_eq_add]
  change S.action w (H v) + S.action (w * ell) v = S.action w (A v)
  rw [map_mul, Module.End.mul_apply, ← hscalar]
  rw [← hsum', map_add]

set_option maxHeartbeats 800000 in
theorem standardLie_commutator_solder (A : E →L[ℝ] E) (v : E)
    (hI : ∀ z, (symplecticProjection S A) (S.I z) = S.I ((symplecticProjection S A) z))
    (hJ : ∀ z, (symplecticProjection S A) (S.J z) = S.J ((symplecticProjection S A) z))
    (hHskew : ∀ z w, inner ℝ ((symplecticProjection S A) z) w +
      inner ℝ z ((symplecticProjection S A) w) = 0) :
    standardLie S A * solderOperator S v - solderOperator S v * standardLie S A =
      solderOperator S (A v) := by
  let H := symplecticProjection S A
  let R := scalarLineLie S A
  let C := column S v
  let C' := column S (A v)
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change H (C z.snd) - C (R z.snd) = C' z.snd
    exact column_infinitesimal S A v z.snd hI hJ
  · apply ext_inner_right ℝ
    intro w
    have ht := column_infinitesimal S A v w hI hJ
    have hsR := scalarLineLie_skew S A (C.adjoint z.fst) w
    have hsH := hHskew z.fst (C w)
    change inner ℝ (R (-(C.adjoint z.fst)) -
      (-(C.adjoint (H z.fst)))) w =
      inner ℝ (-(C'.adjoint z.fst)) w
    simp only [map_neg, sub_neg_eq_add]
    rw [inner_add_left, inner_neg_left, inner_neg_left,
      ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    have htop := congrArg (fun t : E => inner ℝ z.fst t) ht
    change inner ℝ z.fst (H (C w) - C (R w)) = inner ℝ z.fst (C' w) at htop
    rw [inner_sub_right] at htop
    rw [ContinuousLinearMap.adjoint_inner_left] at hsR
    linarith

end
end QuaternionicSymmetry.QuaternionicStandardSolderInfinitesimal
