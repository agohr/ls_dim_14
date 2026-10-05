import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Haar averaging gives a positive definite invariant Hermitian form on a
finite-dimensional continuous representation of a compact group. The original
norm and topology are retained; the form is also provided as a continuous
real bilinear map for differentiation. -/
namespace QuaternionicSymmetry.CompactRepresentationHermitianForm
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {G V W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (μ : Measure G) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulRightInvariant]
  (ρ : G →* Module.End ℂ V) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (q : V →L[ℂ] W) (hq : Function.Injective q)

def averaged (v w : V) : ℂ := ∫ g, ⟪q (ρ g v),q (ρ g w)⟫_ℂ ∂μ

include hρ in
lemma integrable_inner (v w : V) :
    Integrable (fun g => ⟪q (ρ g v),q (ρ g w)⟫_ℂ) μ :=
  ((q.continuous.comp (hρ v)).inner (q.continuous.comp (hρ w))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma averaged_conj (v w : V) : starRingEnd ℂ (averaged μ ρ q w v) = averaged μ ρ q v w := by
  rw [averaged, ← integral_conj]
  simp only [inner_conj_symm]
  rfl

include hρ in
lemma averaged_add_left (u v w : V) :
    averaged μ ρ q (u+v) w = averaged μ ρ q u w + averaged μ ρ q v w := by
  simp only [averaged, map_add, inner_add_left]
  exact integral_add (integrable_inner μ ρ hρ q u w) (integrable_inner μ ρ hρ q v w)

lemma averaged_smul_left (c : ℂ) (v w : V) :
    averaged μ ρ q (c • v) w = starRingEnd ℂ c * averaged μ ρ q v w := by
  simp only [averaged, map_smul, inner_smul_left]
  exact integral_const_mul _ _

include hρ in
lemma averaged_add_right (u v w : V) :
    averaged μ ρ q u (v+w) = averaged μ ρ q u v + averaged μ ρ q u w := by
  simp only [averaged, map_add, inner_add_right]
  exact integral_add (integrable_inner μ ρ hρ q u v) (integrable_inner μ ρ hρ q u w)

lemma averaged_smul_right (c : ℂ) (v w : V) :
    averaged μ ρ q v (c • w) = c * averaged μ ρ q v w := by
  simp only [averaged, map_smul, inner_smul_right]
  exact integral_const_mul _ _

include hρ in
lemma averaged_self_re (v : V) :
    (averaged μ ρ q v v).re = ∫ g, ‖q (ρ g v)‖ ^ 2 ∂μ := by
  change RCLike.re (∫ g, ⟪q (ρ g v),q (ρ g v)⟫_ℂ ∂μ) = _
  rw [← integral_re (integrable_inner μ ρ hρ q v v)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

include hρ hq in
lemma averaged_pos {v : V} (hv : v ≠ 0) : 0 < (averaged μ ρ q v v).re := by
  rw [averaged_self_re μ ρ hρ q]
  apply ((q.continuous.comp (hρ v)).norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ => sq_nonneg _) (x := 1)
  simpa only [map_one, Module.End.one_apply, ne_eq, pow_eq_zero_iff (by omega : 2 ≠ 0),
    norm_eq_zero] using fun h => hv (hq (by simpa using h))

def core : InnerProductSpace.Core ℂ V where
  inner := averaged μ ρ q
  conj_inner_symm := averaged_conj μ ρ q
  re_inner_nonneg v := by
    change 0 ≤ (averaged μ ρ q v v).re
    rw [averaged_self_re μ ρ hρ q]
    exact integral_nonneg (fun _ => sq_nonneg _)
  add_left := averaged_add_left μ ρ hρ q
  smul_left v w c := averaged_smul_left μ ρ q c v w
  definite v h := by
    by_contra hv
    have hp := averaged_pos μ ρ hρ q hq hv
    rw [h] at hp
    exact (lt_irrefl 0) hp

lemma averaged_invariant (g : G) (v w : V) :
    averaged μ ρ q (ρ g v) (ρ g w) = averaged μ ρ q v w := by
  have heq : (fun t => ⟪q (ρ t (ρ g v)),q (ρ t (ρ g w))⟫_ℂ) =
      (fun t => ⟪q (ρ (t*g) v),q (ρ (t*g) w)⟫_ℂ) := by
    funext t
    simp only [map_mul, Module.End.mul_apply]
  unfold averaged
  rw [heq]
  exact integral_mul_right_eq_self (μ := μ)
    (fun t => ⟪q (ρ t v),q (ρ t w)⟫_ℂ) g

/-- The same averaged form in a type suitable for the ordinary real chain rule. -/
def realBilinear : V →L[ℝ] V →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => LinearMap.toContinuousLinearMap
        { toFun := averaged μ ρ q v
          map_add' := averaged_add_right μ ρ hρ q v
          map_smul' := by
            intro c w
            simpa only [Complex.real_smul, Complex.ofReal_mul] using
              averaged_smul_right μ ρ q (c : ℂ) v w }
      map_add' := by
        intro u v
        apply ContinuousLinearMap.ext
        intro w
        exact averaged_add_left μ ρ hρ q u v w
      map_smul' := by
        intro c v
        apply ContinuousLinearMap.ext
        intro w
        simpa only [Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_mul] using
          averaged_smul_left μ ρ q (c : ℂ) v w }

@[simp] lemma realBilinear_apply (v w : V) :
    realBilinear μ ρ hρ q v w = averaged μ ρ q v w := rfl

end
end QuaternionicSymmetry.CompactRepresentationHermitianForm
