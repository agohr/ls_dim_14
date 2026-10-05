import QuaternionicSymmetry.HolomorphicLineHermitianMetric
import QuaternionicSymmetry.HolomorphicDeterminantLine
import Mathlib.Analysis.Matrix.PosDef

/-! Hermitian metrics on actual finite-rank holomorphic bundle cores and
their induced determinant-line metric. The Gram matrices transform by
the genuine bundle transition; the determinant overlap law is proved.
No curvature or positivity of an anticanonical line is assumed here. -/

namespace QuaternionicSymmetry.HolomorphicVectorHermitianMetric

open HolomorphicLineCoreClasses HolomorphicLineHermitianMetric
open HolomorphicDeterminantLine HolomorphicLinePowers
open scoped Manifold ContDiff Matrix ComplexOrder
noncomputable section

local instance : ContMDiffMul 𝓘(ℝ,ℂ) ∞ ℂ where
  contMDiff_mul := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_mul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2)).contMDiff

variable {B E F ι : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (Z : VectorBundleCore ℂ B F ι)

abbrev GramMatrix := Matrix (Fin (Module.finrank ℂ F))
  (Fin (Module.finrank ℂ F)) ℂ

def transitionMatrix (i j : ι) (x : B) : GramMatrix (F := F) :=
  LinearMap.toMatrix (Module.finBasis ℂ F) (Module.finBasis ℂ F)
    (Z.coordChange i j x).toLinearMap

/-- A genuine smooth Hermitian fiber metric in local bundle frames. -/
structure HermitianBundleMetric where
  gram : ι → B → GramMatrix (F := F)
  positive : ∀ i x, x ∈ Z.baseSet i → (gram i x).PosDef
  smooth : ∀ i a b, ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞
    (fun x => gram i x a b) (Z.baseSet i)
  overlap : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
    gram i x = (transitionMatrix Z i j x)ᴴ * gram j x *
      transitionMatrix Z i j x

def determinantLine (hZ : Z.IsContMDiff 𝓘(ℂ,E) ∞) :
    LineCore (B := B) 𝓘(ℂ,E) := by
  letI := hZ
  exact ⟨ι, determinantCore Z, inferInstance⟩

namespace HermitianBundleMetric

variable (m : HermitianBundleMetric (E := E) Z)

theorem determinant_positive (i : ι) (x : B) (hx : x ∈ Z.baseSet i) :
    0 < (m.gram i x).det.re :=
  (RCLike.pos_iff.mp (m.positive i x hx).det_pos).1

theorem determinant_smooth (i : ι) :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞
      (fun x => (m.gram i x).det.re) (Z.baseSet i) := by
  have hd : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞
      (fun x => (m.gram i x).det) (Z.baseSet i) := by
    simp_rw [Matrix.det_apply']
    apply contMDiffOn_finset_sum
    intro σ _
    apply contMDiffOn_const.mul
    apply contMDiffOn_finset_prod
    intro a _
    exact m.smooth i (σ a) a
  exact Complex.reCLM.contMDiff.comp_contMDiffOn hd

theorem determinant_overlap (i j : ι) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    (m.gram i x).det.re =
      Complex.normSq (transitionDet Z i j x) * (m.gram j x).det.re := by
  rw [m.overlap i j x hx, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]
  have ht : (transitionMatrix Z i j x).det = transitionDet Z i j x :=
    LinearMap.det_toMatrix _ _
  rw [ht]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- The metric on the determinant of the actual bundle, with no supplied
determinant cocycle or positivity premise. -/
def determinantMetric (hZ : Z.IsContMDiff 𝓘(ℂ,E) ∞) :
    HermitianLineMetric (determinantLine Z hZ) where
  frameNormSq i x := (m.gram i x).det.re
  positive := m.determinant_positive Z
  smooth := m.determinant_smooth Z
  overlap i j x hx := by
    have h := m.determinant_overlap Z i j x hx
    simpa only [determinantLine, determinantCore, transitionScalar,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, mul_one] using h

/-- The logarithmic Gram-determinant potential. For the holomorphic
tangent core its Levi form is the actual Chern Ricci form, by Demailly
VIII §6, Definition (6.6) and equation (6.7), printed p.378. -/
def ricciPotential (i : ι) (x : B) : E → ℝ :=
  fun z => -Real.log (m.gram i ((chartAt E x).symm z)).det.re

/-- Positive Chern Ricci curvature, written on the actual Gram matrices.
This is a metric-curvature condition, not ampleness or a line-bundle flag. -/
def PositiveChernRicci : Prop :=
  ∀ (i : ι) (x : B), x ∈ Z.baseSet i →
    ∀ (v : E), v ≠ 0 →
    let φ := m.ricciPotential Z i x
    let z := (chartAt E x) x
    (((fderiv ℝ (fderiv ℝ φ) z) v) v) +
      (((fderiv ℝ (fderiv ℝ φ) z) ((Complex.I : ℂ) • v))
        ((Complex.I : ℂ) • v)) > 0

/-- The determinant-line curvature is the trace curvature of the input
metric: both are computed from the same genuine Gram determinant. -/
theorem determinantMetric_positive (hZ : Z.IsContMDiff 𝓘(ℂ,E) ∞)
    (hRicci : m.PositiveChernRicci Z) :
    (m.determinantMetric Z hZ).PositiveChernCurvature (determinantLine Z hZ) :=
  hRicci

end HermitianBundleMetric
end
end QuaternionicSymmetry.HolomorphicVectorHermitianMetric
