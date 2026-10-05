import QuaternionicSymmetry.ComplexProjectiveLineProjLocus

/-! The line-evaluation prime is unchanged by nonzero rescaling, so the
Proj point computed using `x.rep` agrees with every representative. -/

namespace QuaternionicSymmetry.ComplexProjectiveLineProjInvariant

open ComplexProjectiveTopology
open ComplexProjectiveLineProjPoint ComplexProjectiveLineProjLocus
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem linePrimeIdeal_smul (v : Coord d) (c : ℂ) (hc : c ≠ 0) :
    linePrimeIdeal (c • v) = linePrimeIdeal v := by
  ext p
  change lineEval (c • v) p = 0 ↔ lineEval v p = 0
  constructor
  · intro hp
    apply Polynomial.funext
    intro t
    have h := congrArg (Polynomial.eval (t * c⁻¹)) hp
    rw [eval_lineEval, Polynomial.eval_zero] at h
    have hs : (t * c⁻¹) • (c • v) = t • v := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [hs] at h
    simpa [eval_lineEval] using h
  · intro hp
    apply Polynomial.funext
    intro t
    have h := congrArg (Polynomial.eval (t * c)) hp
    rw [eval_lineEval, Polynomial.eval_zero] at h
    have hs : t • (c • v) = (t * c) • v := by rw [smul_smul]
    simpa [eval_lineEval, hs] using h

theorem lineHomogeneousPrime_smul (v : Coord d) (c : ℂ) (hc : c ≠ 0) :
    lineHomogeneousPrime (c • v) = lineHomogeneousPrime v := by
  unfold lineHomogeneousPrime
  rw [linePrimeIdeal_smul v c hc]

theorem projectivePointToProj_mk (v : Coord d) (hv : v ≠ 0) :
    projectivePointToProj (Projectivization.mk ℂ v hv) =
      ⟨lineHomogeneousPrime v,
        lineHomogeneousPrime_isPrime v,
        lineHomogeneousPrime_relevant v hv⟩ := by
  apply ProjectiveSpectrum.ext
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change lineHomogeneousPrime (Projectivization.mk ℂ v hv).rep =
    lineHomogeneousPrime v
  rw [← hc]
  exact lineHomogeneousPrime_smul v c c.ne_zero

end
end QuaternionicSymmetry.ComplexProjectiveLineProjInvariant
