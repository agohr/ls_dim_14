import QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions

/-! Descent of the quaternionic four-form across genuine tangent charts. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing

open Matrix QuaternionicSymmetry.ManifoldQuaternionicMetric
  QuaternionicSymmetry.ManifoldQuaternionicFourForm
  QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.QuaternionicFourFormRotation
  QuaternionicSymmetry.ManifoldChartFormGluing
  QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold Topology ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem toFrame_coordChange (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (v : E) :
    Q.frames.toFrame j x
      ((tangentBundleCore 𝓘(ℝ, E) M).coordChange i j x v) =
    Q.frames.coordChange i j x (Q.frames.toFrame i x v) := by
  rw [Q.frames.coordChange_apply, Q.frames.from_to i x hi]

theorem chartKahler_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (s : Fin 3) :
    chartKahler Q i x s =
      ∑ t : Fin 3, rotationMatrix Q i j x t s •
        (chartKahler Q j x t).compContinuousLinearMap
          ((tangentBundleCore 𝓘(ℝ, E) M).coordChange i j x) := by
  ext v
  have h := congrArg (fun η : E [⋀^Fin 2]→L[ℝ] ℝ =>
      η (fun k => Q.frames.toFrame i x (v k)))
    (frameKahler_transition Q i j x hi hj s)
  change (frameKahler Q i s) (fun k => Q.frames.toFrame i x (v k)) =
    (∑ t : Fin 3, rotationMatrix Q i j x t s •
      (frameKahler Q j t).compContinuousLinearMap
        (Q.frames.coordChange i j x))
      (fun k => Q.frames.toFrame i x (v k)) at h
  rw [ContinuousAlternatingMap.sum_apply] at h
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  rw [chartKahler_eq_frameKahler Q i x hi s]
  rw [ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  simp_rw [chartKahler_eq_frameKahler Q j x hj]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change (frameKahler Q i s) (fun k => Q.frames.toFrame i x (v k)) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  congr 1
  funext k
  exact (toFrame_coordChange Q i j x hi (v k)).symm

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem wedge_comp (L : E →L[ℝ] E)
    (a b : E [⋀^Fin 2]→L[ℝ] ℝ) :
    (wedge (ContinuousLinearMap.mul ℝ ℝ) a b).compContinuousLinearMap L =
      wedge (ContinuousLinearMap.mul ℝ ℝ)
        (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [wedge_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1

theorem chartFour_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    chartFour Q i x =
      (chartFour Q j x).compContinuousLinearMap
        ((tangentBundleCore 𝓘(ℝ, E) M).coordChange i j x) := by
  let L := (tangentBundleCore 𝓘(ℝ, E) M).coordChange i j x
  let R := rotationMatrix Q i j x
  have hR : (Rᵀ)ᵀ * Rᵀ = 1 := by
    simpa only [transpose_transpose] using
      rotationMatrix_rows_orthogonal Q i j x hi hj
  have hrot := sum_wedge_square_rotate (Rᵀ) hR
    (fun t => (chartKahler Q j x t).compContinuousLinearMap L)
  calc
    chartFour Q i x =
      ∑ s : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
        (∑ t : Fin 3, Rᵀ s t •
          (chartKahler Q j x t).compContinuousLinearMap L)
        (∑ t : Fin 3, Rᵀ s t •
          (chartKahler Q j x t).compContinuousLinearMap L) := by
        simp_rw [chartFour, chartKahler_transition Q i j x hi hj]
        rfl
    _ = ∑ t : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
        ((chartKahler Q j x t).compContinuousLinearMap L)
        ((chartKahler Q j x t).compContinuousLinearMap L) := hrot
    _ = (chartFour Q j x).compContinuousLinearMap L := by
      ext v
      simp only [chartFour, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      simp_rw [← wedge_comp L]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- The quaternionic fundamental four-form as compatible smooth local
expressions in the manifold's preferred charts. -/
def fourFormData : ChartFormData (E := E) (M := M) 4 where
  localForm p y := chartFour Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm y)
  regular p := by
    have hs := chartFour_smooth Q (achart E p)
    have hsymm := contMDiffOn_extChartAt_symm (n := ∞) (I := 𝓘(ℝ, E)) p
    have hmaps : Set.MapsTo (extChartAt 𝓘(ℝ, E) p).symm
        (extChartAt 𝓘(ℝ, E) p).target
        ((tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E p)) := by
      intro y hy
      simpa only [tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, E)] using
        (extChartAt 𝓘(ℝ, E) p).map_target hy
    exact (hs.comp hsymm hmaps).contDiffOn
  coordinateLaw p q y hy hq := by
    let x := (extChartAt 𝓘(ℝ, E) p).symm y
    have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
      change x ∈ (tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E p)
      simpa only [tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, E)] using
        (extChartAt 𝓘(ℝ, E) p).map_target hy
    have hq' : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
      change x ∈ (tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E q)
      simpa only [tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, E)] using hq
    have h := chartFour_transition Q (achart E p) (achart E q) x hp hq'
    have hderiv := chartTransition_derivative_eq_core
      (I := 𝓘(ℝ, E)) p q y ⟨hy, hq⟩
    change chartFour Q (achart E p) x =
      (chartFour Q (achart E q)
        ((extChartAt 𝓘(ℝ, E) q).symm ((extChartAt 𝓘(ℝ, E) q) x))).compContinuousLinearMap
          (fderiv ℝ ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y)
    rw [(extChartAt 𝓘(ℝ, E) q).left_inv hq]
    exact h.trans (congrArg (fun L : E →L[ℝ] E =>
      (chartFour Q (achart E q) x).compContinuousLinearMap L) hderiv.symm)

/-- The globally glued smooth quaternionic four-form. -/
def fundamentalFourForm : QuaternionicSymmetry.ManifoldDifferentialForms.Form
    𝓘(ℝ, E) M 4 := (fourFormData Q).toForm

theorem fundamentalFourForm_smooth :
    QuaternionicSymmetry.ManifoldDifferentialForms.ChartSmooth
      (fundamentalFourForm Q) :=
  (fourFormData Q).toForm_smooth

end
end QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing
