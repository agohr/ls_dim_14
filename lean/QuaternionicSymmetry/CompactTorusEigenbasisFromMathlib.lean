import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import QuaternionicSymmetry.CompactTorusEigenbasisSource

/-! Character bases for continuous finite-dimensional complex torus representations.

Haar integration produces Fourier projections, each a character eigenvector.
Fourier completeness and a separating linear functional show that these
vectors span; choosing a basis proves the exact `KnappTorusEigenbasis`
interface without a literature premise. The proof was first checked in
contract-audit experiment E12. -/
namespace QuaternionicSymmetry.CompactTorusEigenbasisFromMathlib
open QuaternionicSymmetry ManifoldQuaternionicTorusAction
open MeasureTheory AddCircle UnitAddTorus
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {r : ℕ}

def toTorus (a : UnitAddTorus (Fin r)) : Torus r := fun i => toCircle (a i)

theorem toTorus_continuous : Continuous (toTorus (r := r)) := by
  apply continuous_pi
  intro i
  exact continuous_toCircle.comp (continuous_apply i)

theorem toTorus_add (a b : UnitAddTorus (Fin r)) :
    toTorus (a+b) = toTorus a * toTorus b := by
  funext i
  exact toCircle_add _ _

theorem toTorus_zero : toTorus (0 : UnitAddTorus (Fin r)) = 1 := by
  funext i
  simp [toTorus]

theorem toTorus_surjective : Function.Surjective (toTorus (r := r)) := by
  intro t
  refine ⟨fun i => (homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (t i), ?_⟩
  funext i
  simpa only [toTorus, homeomorphCircle_apply] using
    (homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply (t i)

theorem mFourier_translate (n : Fin r → ℤ) (a b : UnitAddTorus (Fin r)) :
    mFourier n (a+b) = mFourier n a * mFourier n b := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_inverse (n : Fin r → ℤ) (a : UnitAddTorus (Fin r)) :
    mFourier n a * mFourier (-n) a = 1 := by
  rw [← mFourier_add, add_neg_cancel, mFourier_zero]
  rfl

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
variable (ρ : Torus r →* Module.End ℂ V)
  (hρ : Continuous (fun p : Torus r × V => ρ p.1 p.2))

def projection (n : Fin r → ℤ) (v : V) : V :=
  mFourierCoeff (fun a : UnitAddTorus (Fin r) => ρ (toTorus a) v) n

include hρ

omit [FiniteDimensional ℂ V] in
theorem orbit_continuous (v : V) :
    Continuous (fun a : UnitAddTorus (Fin r) => ρ (toTorus a) v) :=
  hρ.comp (toTorus_continuous.prodMk continuous_const)

omit [FiniteDimensional ℂ V] in
theorem projection_integrable (n : Fin r → ℤ) (v : V) :
    Integrable (fun a : UnitAddTorus (Fin r) =>
      mFourier (-n) a • ρ (toTorus a) v) :=
  ((mFourier (-n)).continuous.smul (orbit_continuous ρ hρ v)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem projection_translation (n : Fin r → ℤ) (v : V)
    (a : UnitAddTorus (Fin r)) :
    projection ρ n v = mFourier (-n) a • ρ (toTorus a) (projection ρ n v) := by
  let A : V →L[ℂ] V := LinearMap.toContinuousLinearMap (ρ (toTorus a))
  calc
    projection ρ n v = ∫ t : UnitAddTorus (Fin r),
        mFourier (-n) (a+t) • ρ (toTorus (a+t)) v := by
      exact (integral_add_left_eq_self
        (fun t : UnitAddTorus (Fin r) => mFourier (-n) t • ρ (toTorus t) v) a).symm
    _ = ∫ t : UnitAddTorus (Fin r),
        mFourier (-n) a • A (mFourier (-n) t • ρ (toTorus t) v) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [mFourier_translate, toTorus_add, map_mul, Module.End.mul_apply,
        map_smul, mul_smul]
      rfl
    _ = mFourier (-n) a • A (projection ρ n v) := by
      rw [integral_smul, A.integral_comp_comm (projection_integrable ρ hρ n v)]
      rfl
    _ = _ := rfl

theorem projection_eigen (n : Fin r → ℤ) (v : V) (a : UnitAddTorus (Fin r)) :
    ρ (toTorus a) (projection ρ n v) = mFourier n a • projection ρ n v := by
  have h := congrArg (fun w : V => mFourier n a • w)
    (projection_translation ρ hρ n v a)
  simp only [smul_smul, mFourier_inverse, one_smul] at h
  exact h.symm

def eigenvectors : Set V :=
  {v | ∃ n : Fin r → ℤ, ∀ a : UnitAddTorus (Fin r),
    ρ (toTorus a) v = mFourier n a • v}

theorem projection_mem_eigenvectors (n : Fin r → ℤ) (v : V) :
    projection ρ n v ∈ eigenvectors ρ := ⟨n, projection_eigen ρ hρ n v⟩

theorem span_eigenvectors : Submodule.span ℂ (eigenvectors ρ) = ⊤ := by
  classical
  apply top_unique
  intro v hv
  by_contra hnot
  obtain ⟨l, hlv, hl⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  let L : V →L[ℂ] ℂ := l.toContinuousLinearMap
  let f : C(UnitAddTorus (Fin r), ℂ) :=
    ⟨fun a => L (ρ (toTorus a) v), L.continuous.comp (orbit_continuous ρ hρ v)⟩
  have hcoeff (n : Fin r → ℤ) : mFourierCoeff f n = 0 := by
    have hp : l (projection ρ n v) = 0 := by
      have hm : l (projection ρ n v) ∈ (Submodule.span ℂ (eigenvectors ρ)).map l :=
        Submodule.mem_map.mpr ⟨projection ρ n v,
          Submodule.subset_span (projection_mem_eigenvectors ρ hρ n v), rfl⟩
      rwa [hl, Submodule.mem_bot] at hm
    calc
      mFourierCoeff f n = ∫ a : UnitAddTorus (Fin r),
          L (mFourier (-n) a • ρ (toTorus a) v) := by
        simp only [mFourierCoeff, f, ContinuousMap.coe_mk, map_smul]
      _ = L (projection ρ n v) := by
        exact L.integral_comp_comm (projection_integrable ρ hρ n v)
      _ = 0 := hp
  have hsum : Summable (mFourierCoeff f) := by
    rw [show mFourierCoeff f = (fun _ => (0 : ℂ)) from funext hcoeff]
    exact summable_zero
  have hs := hasSum_mFourier_series_apply_of_summable hsum (0 : UnitAddTorus (Fin r))
  simp only [hcoeff, zero_smul] at hs
  have hz : f 0 = 0 := hs.unique hasSum_zero
  apply hlv
  simpa [f, L, toTorus_zero] using hz

omit hρ in
theorem mFourier_eq_weightCharacter (n : Fin r → ℤ) (a : UnitAddTorus (Fin r)) :
    mFourier n a = (weightCharacter n (toTorus a) : ℂ) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_apply, toCircle_zsmul,
    weightCharacter, MonoidHom.coe_mk, OneHom.coe_mk, toTorus]
  exact (map_prod Circle.coeHom (fun i : Fin r => toCircle (a i) ^ n i) Finset.univ).symm

omit hρ in
/-- The literal production contract, with no literature assumptions. -/
theorem torusEigenbasisSource : CompactTorusEigenbasisSource.KnappTorusEigenbasis := by
  intro r V _ _ _ ρ hρ
  let b0 := Module.Basis.ofSpan (le_of_eq (span_eigenvectors ρ hρ).symm)
  let e := b0.indexEquiv (Module.finBasis ℂ V)
  let b := b0.reindex e
  have hb (i : Fin (Module.finrank ℂ V)) : b i ∈ eigenvectors ρ :=
    Module.Basis.ofSpan_subset (le_of_eq (span_eigenvectors ρ hρ).symm)
      ⟨e.symm i, (b0.reindex_apply e i).symm⟩
  choose n hn using hb
  refine ⟨b, (fun i =>
    { toMonoidHom := weightCharacter (n i)
      continuous_toFun := QuaternionicTorusWeightKernel.continuous_weightCharacter (n i) }), ?_⟩
  intro t i
  obtain ⟨a, rfl⟩ := toTorus_surjective t
  exact (hn i a).trans (by rw [mFourier_eq_weightCharacter]; rfl)

end
end QuaternionicSymmetry.CompactTorusEigenbasisFromMathlib
