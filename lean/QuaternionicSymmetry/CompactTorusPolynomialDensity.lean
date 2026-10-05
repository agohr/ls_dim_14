import QuaternionicSymmetry.TorusLaurentRepresentation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.Connected

/-! Source-free polynomial identity on the compact torus.  This is the
elementary Zariski-density ingredient for a later algebraic projective-image
preservation argument; no projective variety or Chow premise appears here. -/

namespace QuaternionicSymmetry.CompactTorusPolynomialDensity

open ManifoldQuaternionicTorusAction TorusLaurentRepresentation MvPolynomial
noncomputable section

theorem circle_values_infinite :
    (Set.range (fun t : Circle => (t : ℂ))).Infinite := by
  have hs : (Metric.sphere (0 : ℂ) 1).Infinite := by
    apply (isPreconnected_sphere
      (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) 1).infinite_of_nontrivial
    refine ⟨1, ?_, -1, ?_, by norm_num⟩ <;> simp
  simpa [Circle, Submonoid.unitSphere, Metric.sphere, dist_eq_norm] using hs

/-- A polynomial in the complex-torus coordinates that vanishes on every
compact-torus point is identically zero. -/
theorem polynomial_eq_zero_of_compact {r : ℕ}
    (p : MvPolynomial (Fin r) ℂ)
    (h : ∀ t : Torus r, eval (fun i => ((t i : Circle) : ℂ)) p = 0) :
    p = 0 := by
  apply MvPolynomial.funext_set
    (fun _ : Fin r => Set.range (fun t : Circle => (t : ℂ)))
    (fun _ => circle_values_infinite)
  intro x hx
  have hx' : ∀ i, ∃ t : Circle, (t : ℂ) = x i := by
    intro i
    exact hx i (Set.mem_univ i)
  choose t ht using hx'
  have hxt : x = fun i => ((t i : Circle) : ℂ) := by
    funext i
    exact (ht i).symm
  subst x
  simpa using h t

end
end QuaternionicSymmetry.CompactTorusPolynomialDensity
