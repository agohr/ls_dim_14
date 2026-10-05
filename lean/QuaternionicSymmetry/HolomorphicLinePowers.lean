import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicContact
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Tensor powers of an actual holomorphic complex line bundle, represented
in the one-dimensional standard fiber by powers of its scalar transition
functions. This is a genuine vector-bundle core with derived cocycle and
holomorphic transition laws. -/

namespace QuaternionicSymmetry.HolomorphicLinePowers

open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι : Type*} (Z : VectorBundleCore ℂ B ℂ ι)

/-- A complex-linear endomorphism of the complex line is multiplication
by its value at one. -/
theorem linear_apply_one (T : ℂ →L[ℂ] ℂ) (v : ℂ) :
    T v = T 1 * v := by
  have h := T.map_smul v (1 : ℂ)
  simpa [mul_comm] using h

private instance : ContMDiffMul 𝓘(ℂ,ℂ) ∞ ℂ where
  contMDiff_mul := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_fst.mul contDiff_snd).contMDiff

/-- Scalar transition of a complex line core. -/
def transitionScalar (i j : ι) (x : B) : ℂ := Z.coordChange i j x 1

/-- The core of the `k`-th tensor power, using one-dimensional complex
fibers. The zero power is the trivial complex line over the same cover. -/
def powerCore (k : ℕ) : VectorBundleCore ℂ B ℂ ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := (transitionScalar Z i j x)^k • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    have h := Z.coordChange_self i x hx (1 : ℂ)
    change (transitionScalar Z i i x ^ k • ContinuousLinearMap.id ℂ ℂ) v = v
    rw [show transitionScalar Z i i x = 1 by exact h]
    simp only [one_pow, one_smul, ContinuousLinearMap.id_apply]
  continuousOn_coordChange i j := by
    have h : ContinuousOn (fun x => transitionScalar Z i j x)
        (Z.baseSet i ∩ Z.baseSet j) := by
      exact (Z.continuousOn_coordChange i j).clm_apply continuousOn_const
    exact (h.pow k).smul continuousOn_const
  coordChange_comp i j l x hx v := by
    have hcomp := Z.coordChange_comp i j l x hx (1 : ℂ)
    have hs : transitionScalar Z j l x * transitionScalar Z i j x =
        transitionScalar Z i l x := by
      change (Z.coordChange j l x 1) * (Z.coordChange i j x 1) =
        (Z.coordChange i l x 1)
      exact (linear_apply_one (Z.coordChange j l x) (Z.coordChange i j x 1)).symm.trans
        hcomp
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    calc
      transitionScalar Z j l x ^ k * (transitionScalar Z i j x ^ k * v) =
          (transitionScalar Z j l x * transitionScalar Z i j x)^k * v := by
        rw [mul_pow]
        ring
      _ = transitionScalar Z i l x ^ k * v := by rw [hs]

instance powerCore_isContMDiff [Z.IsContMDiff IB ∞] (k : ℕ) :
    (powerCore Z k).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j := by
    have h : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
        (fun x => transitionScalar Z i j x) (Z.baseSet i ∩ Z.baseSet j) := by
      exact (Z.contMDiffOn_coordChange IB i j).clm_apply contMDiffOn_const
    exact (h.pow k).smul contMDiffOn_const

end
end QuaternionicSymmetry.HolomorphicLinePowers

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The genuine holomorphic line core for `L^k` on the source complex
twistor atlas. -/
def HolomorphicContactLine.powerCore {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (k : ℕ) : VectorBundleCore ℂ (SphereBundleTotal Q) ℂ L.Index :=
  HolomorphicLinePowers.powerCore L.core k

theorem HolomorphicContactLine.powerCore_holomorphic {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (k : ℕ) :
    letI := A.charts
    (L.powerCore Q D k).IsContMDiff 𝓘(ℂ, ComplexTwistorModel n) ∞ := by
  letI := A.charts
  letI := L.holomorphic
  exact HolomorphicLinePowers.powerCore_isContMDiff (Z := L.core)
    (IB := 𝓘(ℂ, ComplexTwistorModel n)) k

/-- The power appearing in the complex-contact anticanonical relation. -/
def HolomorphicContactLine.canonicalPowerCore {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A) :
    VectorBundleCore ℂ (SphereBundleTotal Q) ℂ L.Index :=
  L.powerCore Q D (n + 1)

theorem HolomorphicContactLine.canonicalPowerCore_holomorphic {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A) :
    letI := A.charts
    (L.canonicalPowerCore Q D).IsContMDiff
      𝓘(ℂ, ComplexTwistorModel n) ∞ :=
  L.powerCore_holomorphic Q D (n + 1)

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
