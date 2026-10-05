import QuaternionicSymmetry.GeneralLeviCivitaAdaptedKoszul
import QuaternionicSymmetry.GeneralLeviCivitaIsometryKoszulAlgebra
import QuaternionicSymmetry.ManifoldQuaternionicIsometryChartFields

/-! The actual ordinary Levi-Civita Christoffel forms at two chart centers
satisfy the isometry transformation law after pairing with every image
vector. The final vector equality uses surjectivity of the genuine chart
derivative, handled separately. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaIsometryKoszulPairing

open Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaAdaptedKoszul
open GeneralLeviCivitaIsometryKoszulAlgebra
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicIsometryCoordinateMetric
open ManifoldQuaternionicIsometryCoordinateMetricJet
open ManifoldQuaternionicIsometryChartFields
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem ordinaryLeviCivita_isometry_pairing_center
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (D : CoordinateLeviCivitaConnection g)
    (f : QuaternionicIsometries Q) (p : M) (u v w : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let F := localIsometryChartMap Q f p
    let R := fderiv ℝ F y₀
    let S := fderiv ℝ (fderiv ℝ F) y₀
    coordinateMetric Q p y₀ (D.form p y₀ u v) w =
      coordinateMetric Q (f • p) (F y₀)
        (D.form (f • p) (F y₀) (R u) (R v) + S u v) (R w) := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let R := fderiv ℝ F y₀
  let S := fderiv ℝ (fderiv ℝ F) y₀
  let Gs := coordinateMetric Q p y₀
  let Gt := coordinateMetric Q (f • p) (F y₀)
  let Ds : E → E → E → ℝ := fun a b c =>
    fderiv ℝ (fun z => coordinateMetric Q p z b c) y₀ a
  let Dt : E → E → E → ℝ := fun a b c =>
    fderiv ℝ (fun z => coordinateMetric Q (f • p) z b c) (F y₀) a
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have ht : f • ((extChartAt 𝓘(ℝ,E) p).symm y₀) ∈
      (extChartAt 𝓘(ℝ,E) (f • p)).source := by
    rw [hsrc]
    simp
  have hFy : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have htarget : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hFy]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hsym : ∀ a b, Gt a b = Gt b a := by
    intro a b
    exact real_inner_comm _ _
  have hadd : ∀ a b c, Gt (a + b) c = Gt a c + Gt b c := by
    intro a b c
    simp only [Gt, coordinateMetric, map_add, inner_add_left]
  have hS : ∀ a b, S a b = S b a := by
    intro a b
    exact ((localIsometryChartMap_contDiffAt_center Q f p).isSymmSndFDerivAt
      (by norm_num)).eq a b
  have hval : ∀ a b, Gs a b = Gt (R a) (R b) := by
    intro a b
    exact coordinateMetric_isometry Q f p y₀ hy ht a b
  have hjet : ∀ a b c, Ds a b c =
      Dt (R a) (R b) (R c) + Gt (S a b) (R c) + Gt (R b) (S a c) := by
    intro a b c
    exact coordinateMetric_isometry_first_jet_center Q f p a b c
  have hKs : ∀ a b c,
      2 * Gs (D.form p y₀ a b) c = Ds a b c + Ds b a c - Ds c a b := by
    intro a b c
    exact coordinate_koszul_adapted Q g hmetric D p y₀ a b c hy
  have hKt : ∀ a b c,
      2 * Gt (D.form (f • p) (F y₀) a b) c =
        Dt a b c + Dt b a c - Dt c a b := by
    intro a b c
    exact coordinate_koszul_adapted Q g hmetric D (f • p) (F y₀) a b c htarget
  exact koszul_transform_pairing Gs Gt Ds Dt
    (fun a b => D.form p y₀ a b)
    (fun a b => D.form (f • p) (F y₀) a b)
    R S hsym hadd hS hval hjet hKs hKt u v w

end
end QuaternionicSymmetry.GeneralLeviCivitaIsometryKoszulPairing
