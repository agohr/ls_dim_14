import QuaternionicSymmetry.ManifoldQuaternionicIsometryConnectionPullback
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection

/-! The actual soldering one-form is carried by an isometry to the
coordinate pullback of the target soldering form. Its differentiation is
the torsion part of Levi-Civita naturality. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometrySolderDerivative

open Filter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicIsometryConnectionPullback
open ManifoldQuaternionicCoordinateConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The pointwise solder covariance is a neighborhood equality of genuine
one-forms in fixed coordinates, so it may legitimately be differentiated. -/
theorem solder_covariance_eventually
    (f : QuaternionicIsometries Q) (p : M) :
    (fun y : E => (forwardFrameField Q f p y).comp (solder Q p y))
      =ᶠ[nhds (extChartAt 𝓘(ℝ,E) p p)]
    (fun y : E =>
      (solder Q (f • p) (localIsometryChartMap Q f p y)).comp
        (fderiv ℝ (localIsometryChartMap Q f p) y)) := by
  filter_upwards [localIsometryChart_overlap_eventually Q f p]
    with y ⟨hy, hx, hfx⟩
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hxy : extChartAt 𝓘(ℝ,E) p x = y :=
    (extChartAt 𝓘(ℝ,E) p).right_inv hy
  ext u
  have hc := localAdaptedDerivative_solder_covariant Q f p x hx hfx u
  have hR := localIsometryChartMap_fderiv Q f p x hx hfx
  change localAdaptedDerivative Q f p x (solder Q p y u) =
    solder Q (f • p) (localIsometryChartMap Q f p y)
      (fderiv ℝ (localIsometryChartMap Q f p) y u)
  rw [← hxy]
  change localAdaptedDerivative Q f p x
      (solder Q p (extChartAt 𝓘(ℝ,E) p x) u) =
    solder Q (f • p)
      (extChartAt 𝓘(ℝ,E) (f • p)
        (f • ((extChartAt 𝓘(ℝ,E) p).symm
          (extChartAt 𝓘(ℝ,E) p x))))
      (fderiv ℝ (localIsometryChartMap Q f p)
        (extChartAt 𝓘(ℝ,E) p x) u)
  rw [(extChartAt 𝓘(ℝ,E) p).left_inv
    (by simpa only [extChartAt_source] using hx)]
  rw [hR]
  exact hc

/-- Differentiated solder covariance at the center. The four terms are
respectively the frame variation, source solder variation, target solder
variation, and second derivative of the actual chart isometry. -/
theorem solder_covariance_fderiv_center
    (f : QuaternionicIsometries Q) (p : M) (u v : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let F := localIsometryChartMap Q f p
    let A := forwardFrameField Q f p
    let S := solder Q p
    let T := solder Q (f • p)
    (fderiv ℝ A y₀ u) (S y₀ v) + A y₀ (fderiv ℝ S y₀ u v) =
      (fderiv ℝ T (F y₀) (fderiv ℝ F y₀ u)) (fderiv ℝ F y₀ v) +
        T (F y₀) (fderiv ℝ (fderiv ℝ F) y₀ u v) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let A := forwardFrameField Q f p
  let S := solder Q p
  let T := solder Q (f • p)
  have hF : ContDiffAt ℝ 2 F y₀ :=
    localIsometryChartMap_contDiffAt_center Q f p
  have hF₁ : DifferentiableAt ℝ F y₀ := hF.differentiableAt (by norm_num)
  have hF₂ : DifferentiableAt ℝ (fderiv ℝ F) y₀ :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ A y₀ :=
    (localAdaptedDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num)
  have hS₀ : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hF₀ : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have hT₀ : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hF₀]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hS : DifferentiableAt ℝ S y₀ :=
    (solder_contDiffAt Q p y₀ hS₀).differentiableAt (by norm_num)
  have hT : DifferentiableAt ℝ T (F y₀) :=
    (solder_contDiffAt Q (f • p) (F y₀) hT₀).differentiableAt (by norm_num)
  have hTF : DifferentiableAt ℝ (fun z => T (F z)) y₀ := hT.comp y₀ hF₁
  have heq := congrArg (fun L : E →L[ℝ] (E →L[ℝ] E) => L u v)
    ((solder_covariance_eventually Q f p).fderiv_eq (𝕜 := ℝ))
  change (fderiv ℝ (fun z => (A z).comp (S z)) y₀) u v =
    (fderiv ℝ (fun z => (T (F z)).comp (fderiv ℝ F z)) y₀) u v at heq
  rw [fderiv_clm_comp hA hS, fderiv_clm_comp hTF hF₂] at heq
  have hTFderiv : fderiv ℝ (fun z => T (F z)) y₀ =
      (fderiv ℝ T (F y₀)).comp (fderiv ℝ F y₀) := by
    simpa only [Function.comp_def] using fderiv_comp y₀ hT hF₁
  rw [hTFderiv] at heq
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    add_comm] using heq

/-- Antisymmetrization removes the symmetric second derivative of the
actual isometry chart map, leaving the two solder exterior derivatives. -/
theorem solder_covariance_antisym_center
    (f : QuaternionicIsometries Q) (p : M) (u v : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let F := localIsometryChartMap Q f p
    let A := forwardFrameField Q f p
    let S := solder Q p
    let T := solder Q (f • p)
    (fderiv ℝ A y₀ u) (S y₀ v) -
      (fderiv ℝ A y₀ v) (S y₀ u) +
      A y₀ (fderiv ℝ S y₀ u v - fderiv ℝ S y₀ v u) =
    fderiv ℝ T (F y₀) (fderiv ℝ F y₀ u) (fderiv ℝ F y₀ v) -
      fderiv ℝ T (F y₀) (fderiv ℝ F y₀ v) (fderiv ℝ F y₀ u) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let A := forwardFrameField Q f p
  let S := solder Q p
  let T := solder Q (f • p)
  have h₁ := solder_covariance_fderiv_center Q f p u v
  have h₂ := solder_covariance_fderiv_center Q f p v u
  have hs := (localIsometryChartMap_contDiffAt_center Q f p).isSymmSndFDerivAt
    (by norm_num)
  have hsym : (fderiv ℝ (fderiv ℝ F) y₀ v) u =
      (fderiv ℝ (fderiv ℝ F) y₀ u) v := hs.eq v u
  dsimp only at h₁ h₂
  rw [hsym] at h₂
  simpa only [A, S, T, F, y₀, map_sub] using
    (show
      (fderiv ℝ A y₀ u) (S y₀ v) -
        (fderiv ℝ A y₀ v) (S y₀ u) +
        A y₀ (fderiv ℝ S y₀ u v - fderiv ℝ S y₀ v u) =
      fderiv ℝ T (F y₀) (fderiv ℝ F y₀ u) (fderiv ℝ F y₀ v) -
        fderiv ℝ T (F y₀) (fderiv ℝ F y₀ v) (fderiv ℝ F y₀ u) from by
      calc
        _ = ((fderiv ℝ A y₀ u) (S y₀ v) +
              A y₀ (fderiv ℝ S y₀ u v)) -
            ((fderiv ℝ A y₀ v) (S y₀ u) +
              A y₀ (fderiv ℝ S y₀ v u)) := by
            rw [map_sub]
            abel
        _ = (fderiv ℝ T (F y₀) (fderiv ℝ F y₀ u)
              (fderiv ℝ F y₀ v) +
              T (F y₀) (fderiv ℝ (fderiv ℝ F) y₀ u v)) -
            (fderiv ℝ T (F y₀) (fderiv ℝ F y₀ v)
              (fderiv ℝ F y₀ u) +
              T (F y₀) (fderiv ℝ (fderiv ℝ F) y₀ u v)) := by
            rw [h₁, h₂]
        _ = _ := by abel)

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometrySolderDerivative
