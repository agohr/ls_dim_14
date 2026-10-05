import QuaternionicSymmetry.CompactLieOneParameterNaturality
import QuaternionicSymmetry.CompactLieOneParameterSmooth
import QuaternionicSymmetry.RealAdjointDifferentialFromMathlib
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A zero infinitesimal action fixes a vector along a one-parameter subgroup.
Applied to the genuine adjoint action, this integrates a zero Lie bracket
to commuting one-parameter subgroups. -/

namespace QuaternionicSymmetry
open Function
noncomputable section
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G]

theorem oneParameter_fixed_of_zero_derivative
    (ρ : G →* Module.End ℝ E) (γ : ℝ → G) (hzero : γ 0 = 1)
    (hadd : ∀ s t, γ (s+t) = γ s * γ t) (v : E)
    (hd : HasDerivAt (fun s => ρ (γ s) v) 0 0) :
    ∀ t, ρ (γ t) v = v := by
  let f : ℝ → E := fun s => ρ (γ s) v
  have hder (t : ℝ) : HasDerivAt f 0 t := by
    let A : E →L[ℝ] E := LinearMap.toContinuousLinearMap (ρ (γ t))
    have hh := A.hasFDerivAt.comp_hasDerivAt 0 hd
    have he : (fun s => A (f s)) = (fun s => f (t+s)) := by
      funext s
      dsimp [A,f]
      rw [hadd, map_mul]
      rfl
    have hs : HasDerivAt (fun s => f (t+s)) 0 0 := by
      simpa only [Function.comp_def, map_zero, ← he] using hh
    have hs' : HasDerivAt (fun s => f (t+s)) 0 (t-t) := by simpa using hs
    have hb := hs'.scomp (h := fun s : ℝ => s-t) t ((hasDerivAt_id t).sub_const t)
    convert hb using 1
    · funext s
      dsimp only [Function.comp_def]
      congr 1
      ring
    · simp
  have hc (t : ℝ) := is_const_of_deriv_eq_zero (fun t => (hder t).differentiableAt)
    (fun t => (hder t).deriv) t 0
  intro t
  simpa [f,hzero] using hc t

end
end QuaternionicSymmetry
namespace QuaternionicSymmetry.RealAdjointRepresentation
open GeneralRealAdjointDifferentialSource
open scoped Manifold ContDiff Topology
noncomputable section
variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G] [LieGroup 𝓘(ℝ,V) ∞ G]

lemma conjugation_smooth (g : G) :
    ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (fun h : G => g*h*g⁻¹) :=
  (contMDiff_const.mul contMDiff_id).mul contMDiff_const

def adjoint : G →* Module.End ℝ V where
  toFun g := (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (fun h : G => g*h*g⁻¹) 1).toLinearMap
  map_one' := by
    change (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (fun h : G => 1*h*1⁻¹) 1).toLinearMap = _
    rw [show (fun h : G => 1*h*1⁻¹) = id by funext h; simp]
    exact congrArg ContinuousLinearMap.toLinearMap (mfderiv_id (I := 𝓘(ℝ,V)) (x := (1 : G)))
  map_mul' g h := by
    have heq : (fun t : G => (g*h)*t*(g*h)⁻¹) =
        (fun t : G => g*t*g⁻¹) ∘ (fun t : G => h*t*h⁻¹) := by
      funext t
      simp [mul_assoc]
    have hd := mfderiv_comp (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,V)) (I'' := 𝓘(ℝ,V))
      (x := (1 : G)) ((conjugation_smooth g).mdifferentiableAt (by simp))
      ((conjugation_smooth h).mdifferentiableAt (by simp))
    change (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) _ 1).toLinearMap = _
    rw [heq, hd, show h*1*h⁻¹ = 1 by simp]
    rfl

@[simp] lemma adjoint_apply (g : G) (v : V) : adjoint (V := V) g v = adjointOrbitReal v g := rfl

end
end QuaternionicSymmetry.RealAdjointRepresentation

namespace QuaternionicSymmetry.CompactLieCommutingFlows
open CompactLieOneParameterSubgroup CompactLieOneParameterSmooth
open GeneralRealAdjointDifferentialSource GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]

theorem fixed (hClosed : LeeClosedEmbeddingTheorem)
    (u v : GroupLieAlgebra 𝓘(ℝ,E) G) (hbr : ⁅u,v⁆ = 0) :
    ∀ t, adjointOrbitReal v (curve u t) = v := by
  apply oneParameter_fixed_of_zero_derivative
    (RealAdjointRepresentation.adjoint (V := E) (G := G)) (curve u)
    (curve_zero u) (curve_add u) v
  have ha := RealAdjointDifferentialFromMathlib.adjoint_differential v
  have ha' : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (adjointOrbitReal v) (curve u 0) := by
    rw [curve_zero]
    exact ha.1
  have hh := ha'.hasMFDerivAt.comp (0 : ℝ)
    ((curve_smooth hClosed u).mdifferentiableAt (by simp)).hasMFDerivAt
  have hd := hh.hasFDerivAt.hasDerivAt
  change HasDerivAt (fun t => adjointOrbitReal v (curve u t))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (adjointOrbitReal v) (curve u 0)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (curve u) 0 (1 : ℝ))) 0 at hd
  rw [curve_derivative_zero (G := G) u, curve_zero (G := G) u, ha.2 u, hbr] at hd
  exact hd
theorem curves_commute (hClosed : LeeClosedEmbeddingTheorem)
    (u v : GroupLieAlgebra 𝓘(ℝ,E) G) (hbr : ⁅u,v⁆ = 0) (s t : ℝ) :
    Commute (curve u s) (curve v t) := by
  let g := curve u s
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f :=
    RealAdjointRepresentation.conjugation_smooth g
  have he := CompactLieOneParameterNaturality.map_curve f hf v t
  have hv : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f 1 v = v := fixed hClosed u v hbr s
  rw [hv] at he
  change g * curve v t * g⁻¹ = curve v t at he
  have hh := congrArg (fun x : G => x*g) he
  simpa [mul_assoc] using hh

end
end QuaternionicSymmetry.CompactLieCommutingFlows
