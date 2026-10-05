import QuaternionicSymmetry.QuaternionicBianchiWedgeScalar
import QuaternionicSymmetry.CurvatureBianchiWedge

/-! Algebraic first Bianchi determines the scalar part of curvature in the
quaternionic normalizer. No curvature-decomposition premise is used. -/
namespace QuaternionicSymmetry.QuaternionicCurvatureScalarFromBianchi
open QuaternionicBianchiWedgeScalar QuaternionicBianchiWedgeEight
open CurvatureBianchiAlternation CurvatureBianchiWedge VectorBundleFrameTransitions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
theorem exists_scalar (S : QuaternionicStructure E)
    (hn : 2 ≤ S.quaternionicDimension)
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (a : Fin 3 → E →L[ℝ] E →L[ℝ] ℝ)
    (hsk : ∀ t u v, a t u v = -a t v u)
    (hfirst : ∀ u v, R u v = -R v u)
    (hlast : ∀ u v w z, inner ℝ (R u v w) z = -inner ℝ (R u v z) w)
    (hB : ∀ u v w, R u v w + R v w u + R w u v = 0)
    (hI : ∀ u v w, R u v (S.I w) - S.I (R u v w) =
      (2 : ℝ) • (a 2 u v • S.J w - a 1 u v • S.K w))
    (hJ : ∀ u v w, R u v (S.J w) - S.J (R u v w) =
      (2 : ℝ) • (a 0 u v • S.K w - a 2 u v • S.I w))
    (hK : ∀ u v w, R u v (S.K w) - S.K (R u v w) =
      (2 : ℝ) • (a 1 u v • S.I w - a 0 u v • S.J w)) :
    ∃ c : ℝ, ∀ t u v, a t u v = c * inner ℝ (quaternionicGenerator S t u) v := by
  let T : E → E → E → E → ℝ := fun u v w z => inner ℝ (R u v w) z
  have hTf : ∀ u v w z, T u v w z = -T v u w z := by
    intro u v w z
    dsimp only [T]
    rw [hfirst, ContinuousLinearMap.neg_apply, inner_neg_left]
  have hTB : ∀ u v w z, T u v w z + T v w u z + T w u v z = 0 := by
    intro u v w z
    have he := congrArg (fun t : E => inner ℝ t z) (hB u v w)
    simpa only [inner_add_left, inner_zero_left, T] using he
  have hAI : ∀ u v w z, action T S.I u v w z =
      2 * (a 2 u v * metricForm S 1 w z - a 1 u v * metricForm S 2 w z) := by
    intro u v w z
    have he := congrArg (fun t : E => inner ℝ t z) (hI u v w)
    simp only [inner_sub_left, real_inner_smul_left] at he
    have hs := S.I_skew (R u v w) z
    change inner ℝ (R u v (S.I w)) z + inner ℝ (R u v w) (S.I z) =
      2 * (a 2 u v * inner ℝ (S.J w) z - a 1 u v * inner ℝ (S.K w) z)
    linarith
  have hAJ : ∀ u v w z, action T S.J u v w z =
      2 * (a 0 u v * metricForm S 2 w z - a 2 u v * metricForm S 0 w z) := by
    intro u v w z
    have he := congrArg (fun t : E => inner ℝ t z) (hJ u v w)
    simp only [inner_sub_left, real_inner_smul_left] at he
    have hs := S.J_skew (R u v w) z
    change inner ℝ (R u v (S.J w)) z + inner ℝ (R u v w) (S.J z) =
      2 * (a 0 u v * inner ℝ (S.K w) z - a 2 u v * inner ℝ (S.I w) z)
    linarith
  have hAK : ∀ u v w z, action T S.K u v w z =
      2 * (a 1 u v * metricForm S 0 w z - a 0 u v * metricForm S 1 w z) := by
    intro u v w z
    have he := congrArg (fun t : E => inner ℝ t z) (hK u v w)
    simp only [inner_sub_left, real_inner_smul_left] at he
    have hs := S.K_skew (R u v w) z
    change inner ℝ (R u v (S.K w)) z + inner ℝ (R u v w) (S.K z) =
      2 * (a 1 u v * inner ℝ (S.I w) z - a 0 u v * inner ℝ (S.J w) z)
    linarith
  apply QuaternionicBianchiWedgeScalar.exists_scalar S hn a hsk
  intro s t u v w z
  have h12 := wedge_eq_of_action T hTf hlast hTB S.I _ _ _ _ hAI u v w z
  have h20 := wedge_eq_of_action T hTf hlast hTB S.J _ _ _ _ hAJ u v w z
  have h01 := wedge_eq_of_action T hTf hlast hTB S.K _ _ _ _ hAK u v w z
  fin_cases s <;> fin_cases t <;>
    first
    | rfl
    | exact h12
    | exact h12.symm
    | exact h20
    | exact h20.symm
    | exact h01
    | exact h01.symm

end
end QuaternionicSymmetry.QuaternionicCurvatureScalarFromBianchi
