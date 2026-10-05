import QuaternionicSymmetry.ManifoldQuaternionicIsometrySolderDerivative

/-! Naturality of the actual torsion-free metric tangent connection under
actual smooth metric-quaternionic isometries. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryConnectionNaturality

open Filter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicIsometryAdaptedOrthogonal
open ManifoldQuaternionicIsometryConnectionPullback
open ManifoldQuaternionicIsometrySolderDerivative
open QuaternionicSymmetry.ManifoldQuaternionicConnectionPointwiseUniqueness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Torsion-freeness of the explicitly transformed actual connection form.
It follows by differentiating the genuine solder covariance and cancelling
the symmetric second derivative of the chart isometry. -/
theorem pulledConnectionForm_torsion_center
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) (u v : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    fderiv ℝ (solder Q p) y₀ u v -
      fderiv ℝ (solder Q p) y₀ v u +
      pulledConnectionForm Q D f p y₀ u (solder Q p y₀ v) -
      pulledConnectionForm Q D f p y₀ v (solder Q p y₀ u) = 0 := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let A := forwardFrameField Q f p y₀
  let B := reverseFrameField Q f p y₀
  let S := solder Q p y₀
  let T := solder Q (f • p) (F y₀)
  let R := fderiv ℝ F y₀
  let dA := fderiv ℝ (forwardFrameField Q f p) y₀
  let dS := fderiv ℝ (solder Q p) y₀
  let dT := fderiv ℝ (solder Q (f • p)) (F y₀)
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hF : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have hmem : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hF]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hAB (z : E) : A (B z) = z := by
    simpa only [A, B, forwardFrameField, reverseFrameField, hsrc] using
      localAdaptedDerivative_inverse_center Q f p z
  have hcov : A.comp S = T.comp R := by
    have hc := (solder_covariance_eventually Q f p).eq_of_nhds
    exact hc
  have hcov_apply (z : E) : A (S z) = T (R z) :=
    congrArg (fun L : E →L[ℝ] E => L z) hcov
  have hanti :
      dA u (S v) - dA v (S u) + A (dS u v - dS v u) =
        dT (R u) (R v) - dT (R v) (R u) :=
    solder_covariance_antisym_center Q f p u v
  have htarget := D.torsion (f • p) (F y₀) (R u) (R v) hmem
  have hpull (a b : E) :
      A (pulledConnectionForm Q D f p y₀ a (S b)) =
        D.form (f • p) (F y₀) (R a) (T (R b)) + dA a (S b) := by
    rw [pulledConnectionForm_apply]
    change A (B (D.form (f • p) (F y₀) (R a) (A (S b)) + dA a (S b))) = _
    rw [hAB, hcov_apply]
  have hz :
      A (dS u v - dS v u +
        pulledConnectionForm Q D f p y₀ u (S v) -
        pulledConnectionForm Q D f p y₀ v (S u)) = 0 := by
    rw [map_sub, map_add, map_sub, hpull u v, hpull v u]
    calc
      _ = (dA u (S v) - dA v (S u) + A (dS u v - dS v u)) +
            (D.form (f • p) (F y₀) (R u) (T (R v)) -
              D.form (f • p) (F y₀) (R v) (T (R u))) := by
            simp only [map_sub]
            abel_nf
      _ = (dT (R u) (R v) - dT (R v) (R u)) +
            (D.form (f • p) (F y₀) (R u) (T (R v)) -
              D.form (f • p) (F y₀) (R v) (T (R u))) := by rw [hanti]
      _ = 0 := by
        calc
          _ = dT (R u) (R v) - dT (R v) (R u) +
                D.form (f • p) (F y₀) (R u) (T (R v)) -
                  D.form (f • p) (F y₀) (R v) (T (R u)) := by abel
          _ = 0 := htarget
  have horth (z : E) : inner ℝ (A z) (A z) = inner ℝ z z := by
    simpa only [A, forwardFrameField, hsrc] using
      localAdaptedDerivative_center_inner Q f p z z
  have hzero : dS u v - dS v u +
      pulledConnectionForm Q D f p y₀ u (S v) -
      pulledConnectionForm Q D f p y₀ v (S u) = 0 := by
    let z := dS u v - dS v u +
      pulledConnectionForm Q D f p y₀ u (S v) -
      pulledConnectionForm Q D f p y₀ v (S u)
    have hh := horth z
    rw [hz, inner_zero_left] at hh
    by_contra hne
    have hp := real_inner_self_pos.mpr hne
    linarith
  exact hzero

/-- Levi-Civita naturality under an actual smooth metric-quaternionic
isometry, at the center of every adapted source chart. This is deduced
internally from metricity, torsion, and pointwise uniqueness. -/
theorem pulledConnectionForm_eq_center
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) :
    pulledConnectionForm Q D f p (extChartAt 𝓘(ℝ,E) p p) =
      D.form p (extChartAt 𝓘(ℝ,E) p p) := by
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  apply candidate_eq_on_chart Q D p y₀ hy
  · intro u v w
    exact pulledConnectionForm_metric_center Q D f p u v w
  · intro u v
    exact pulledConnectionForm_torsion_center Q D f p u v

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryConnectionNaturality
