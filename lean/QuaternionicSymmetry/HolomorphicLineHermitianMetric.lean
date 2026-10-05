import QuaternionicSymmetry.HolomorphicLineCoreAmpleness
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

/-! Actual Hermitian metrics on represented holomorphic line cores. A
positive real local frame norm is supplied on each core chart; the overlap
law ensures that it measures the same fiber norm in every frame. Positivity
of Chern curvature is expressed by the real Levi Hessian of the genuine
local weight `-log h_i` in complex manifold coordinates. -/

namespace QuaternionicSymmetry.HolomorphicLineHermitianMetric

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section
universe uB uF uI

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]
  (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))

/-- Local positive squared norms of holomorphic frames, with the exact
transition law making the resulting fiber norm frame-independent. -/
structure HermitianLineMetric where
  frameNormSq : L.Index → B → ℝ
  positive : ∀ i x, x ∈ L.core.baseSet i → 0 < frameNormSq i x
  smooth : ∀ i, ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞
    (frameNormSq i) (L.core.baseSet i)
  overlap : ∀ i j x, x ∈ L.core.baseSet i ∩ L.core.baseSet j →
    frameNormSq i x =
      Complex.normSq (transitionScalar L.core i j x) * frameNormSq j x

namespace HermitianLineMetric

variable (m : HermitianLineMetric L)

/-- The actual squared norm in the distinguished fiber coordinate at `x`. -/
def fiberNormSq (x : B) (v : L.core.Fiber x) : ℝ :=
  m.frameNormSq (L.core.indexAt x) x * Complex.normSq (show ℂ from v)

theorem fiberNormSq_nonneg (x : B) (v : L.core.Fiber x) :
    0 ≤ fiberNormSq L m x v :=
  mul_nonneg (le_of_lt (m.positive _ _ (L.core.mem_baseSet_at x)))
    (Complex.normSq_nonneg _)

theorem fiberNormSq_pos (x : B) (v : L.core.Fiber x) (hv : v ≠ 0) :
    0 < fiberNormSq L m x v := by
  exact mul_pos (m.positive _ _ (L.core.mem_baseSet_at x))
    (Complex.normSq_pos.mpr hv)

/-- The overlap law says that every local frame computes the same squared
fiber norm, including when the bundle has a nontrivial cocycle. -/
theorem fiberNormSq_eq_chart (i : L.Index) (x : B)
    (hx : x ∈ L.core.baseSet i) (v : L.core.Fiber x) :
    fiberNormSq L m x v =
      m.frameNormSq i x *
        Complex.normSq (L.core.coordChange (L.core.indexAt x) i x v) := by
  have hOverlap := m.overlap (L.core.indexAt x) i x
    ⟨L.core.mem_baseSet_at x, hx⟩
  rw [fiberNormSq, hOverlap]
  rw [linear_apply_one (L.core.coordChange (L.core.indexAt x) i x) v]
  simp only [Complex.normSq_mul]
  simp only [transitionScalar, mul_comm, mul_left_comm]

theorem normSq_pow (z : ℂ) (k : ℕ) :
    Complex.normSq (z ^ k) = (Complex.normSq z) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, Complex.normSq_mul, ih]

/-- Every actual tensor power inherits the Hermitian metric with local
frame norms `h_i^k`; the overlap identity follows by taking powers of the
original nontrivial cocycle law. -/
def powerMetric (k : ℕ) :
    HermitianLineMetric (powerCoreRep 𝓘(ℂ,F) L k) where
  frameNormSq i x := (m.frameNormSq i x)^k
  positive i x hx := pow_pos (m.positive i x hx) k
  smooth i := (m.smooth i).pow k
  overlap i j x hx := by
    have h := m.overlap i j x hx
    change (m.frameNormSq i x)^k =
      Complex.normSq (((transitionScalar L.core i j x)^k •
        ContinuousLinearMap.id ℂ ℂ) 1) * (m.frameNormSq j x)^k
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, mul_one]
    rw [h, mul_pow, normSq_pow]

/-- A local Chern potential in ordinary real coordinates of a holomorphic
chart: `h_i=e^{-φ_i}`, as in Demailly V §12, (12.6)–(12.8). -/
def localChernPotential (i : L.Index) (x : B) : F → ℝ :=
  fun z => -Real.log (m.frameNormSq i ((chartAt F x).symm z))

/-- Strict positivity of the actual Chern Levi form. For each nonzero
complex tangent vector, the real Hessian on `v` and `i v` has positive
sum. This is the real-coordinate sign condition for `i∂∂̄φ_i>0`; the
irrelevant positive factor is omitted. -/
def PositiveChernCurvature : Prop :=
  ∀ (i : L.Index) (x : B), x ∈ L.core.baseSet i →
    ∀ (v : F), v ≠ 0 →
    let φ := localChernPotential L m i x
    let z := (chartAt F x) x
    (((fderiv ℝ (fderiv ℝ φ) z) v) v) +
      (((fderiv ℝ (fderiv ℝ φ) z) ((Complex.I : ℂ) • v))
        ((Complex.I : ℂ) • v)) > 0

/-- The Chern potential of the actual tensor-power metric is the original
potential multiplied by the power. This is a pointwise identity, not a
claim about formal first Chern classes. -/
theorem powerMetric_localChernPotential (k : ℕ) (i : L.Index) (x : B) :
    localChernPotential (powerCoreRep 𝓘(ℂ,F) L k) (m.powerMetric L k) i x =
      (k : ℝ) • localChernPotential L m i x := by
  funext z
  simp only [localChernPotential, powerMetric, powerCoreRep,
    Real.log_pow, Pi.smul_apply, smul_eq_mul]
  ring

/-- Positive Chern curvature survives every strictly positive genuine
tensor power, using the local Chern-potential identity and linearity of
both real derivatives. -/
theorem powerMetric_positive (k : ℕ) (hk : 0 < k)
    (hpos : m.PositiveChernCurvature L) :
    (m.powerMetric L k).PositiveChernCurvature (powerCoreRep 𝓘(ℂ,F) L k) := by
  intro i x hx v hv
  have hp := hpos i x hx v hv
  dsimp [PositiveChernCurvature] at hp ⊢
  rw [powerMetric_localChernPotential]
  simp only [fderiv_const_smul_field]
  have hSecond := fderiv_const_smul_field (𝕜 := ℝ)
    (f := fderiv ℝ (localChernPotential L m i x)) (c := (k : ℝ))
  rw [hSecond]
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith

/-- The converse positive-root calculation: a positive curvature metric
*of the form inherited from an actual metric on `L`* forces that metric on
`L` positive. This does not silently construct a metric or a gauge from
an arbitrary positive metric on an isomorphic anticanonical line. -/
theorem positive_of_powerMetric_positive (k : ℕ) (hk : 0 < k)
    (hpos : (m.powerMetric L k).PositiveChernCurvature
      (powerCoreRep 𝓘(ℂ,F) L k)) :
    m.PositiveChernCurvature L := by
  intro i x hx v hv
  have hp := hpos i x hx v hv
  dsimp [PositiveChernCurvature] at hp ⊢
  rw [powerMetric_localChernPotential] at hp
  simp only [fderiv_const_smul_field] at hp
  have hSecond := fderiv_const_smul_field (𝕜 := ℝ)
    (f := fderiv ℝ (localChernPotential L m i x)) (c := (k : ℝ))
  rw [hSecond] at hp
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hp
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith

end HermitianLineMetric
end
end QuaternionicSymmetry.HolomorphicLineHermitianMetric
