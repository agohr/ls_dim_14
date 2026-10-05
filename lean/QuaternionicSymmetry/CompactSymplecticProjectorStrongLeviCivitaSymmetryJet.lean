import QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetry
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryDerivative
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTotalHorizontal

/-! At the center of an actual projector point symmetry, its genuine
coordinate first derivative is `-Id`. Levi-Civita naturality therefore
determines its second derivative exactly by the ordinary Christoffel form.
This is not a normal-coordinate assumption. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetryJet

open Manifold Bundle
open GeneralLeviCivitaSource
open CompactSymplecticProjectorStrongLeviCivitaSymmetry
open CompactSymplecticProjectorStrongPointSymmetryDerivative
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongPointSymmetry
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIsometryTotalHorizontal
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_pointSymmetry_chart_derivative_neg
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
    let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
    ∀ v : EModel q,
      fderiv ℝ (ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap Q f x)
        y₀ v = -v := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  dsimp only
  intro v
  rw [localIsometryChartMap_fderiv_center_eq_mfderiv Q f x]
  change mfderiv 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) (pointSymmetry n x) x v = -v
  exact pointSymmetry_mfderiv_neg_strong hLee hDesc hImm n d e q g a hq hn x v

theorem actual_pointSymmetry_second_jet_eq_christoffel
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (x : ProjectiveCarrier n) (u v : EModel q),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      let F := ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap Q f x
      fderiv ℝ (fderiv ℝ F) y₀ u v =
        -(D.form x y₀ u v + D.form x y₀ u v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D x u v
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  let F := ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap Q f x
  let R := fderiv ℝ F y₀
  let S := fderiv ℝ (fderiv ℝ F) y₀
  have hneg (z : EModel q) : R z = -z :=
    actual_pointSymmetry_chart_derivative_neg hLee hDesc hImm n d e q g a hq hn x z
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  have hcenter : F y₀ = y₀ := by
    change ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap Q f x
      (extChartAt 𝓘(ℝ,EModel q) x x) = extChartAt 𝓘(ℝ,EModel q) x x
    rw [ManifoldQuaternionicIsometryTotalHorizontal.localIsometryChartMap_center Q f x,
      hfix]
  have hnat := actual_pointSymmetry_leviCivita_naturality
    hLee hDesc hImm n d e q g a hq hn D x u v
  change R (D.form x y₀ u v) =
    D.form (f • x) (F y₀) (R u) (R v) +
      fderiv ℝ (fderiv ℝ F) y₀ u v at hnat
  rw [hfix, hcenter, hneg u, hneg v,
    hneg (D.form x y₀ u v)] at hnat
  have hbilinear : D.form x y₀ (-u) (-v) = D.form x y₀ u v := by
    simp
  rw [hbilinear] at hnat
  change S u v = -(D.form x y₀ u v + D.form x y₀ u v)
  have h := congrArg (fun t : EModel q => t - D.form x y₀ u v) hnat
  abel_nf at h ⊢
  exact h.symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetryJet
