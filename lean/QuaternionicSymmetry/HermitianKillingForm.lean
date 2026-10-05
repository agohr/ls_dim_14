import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Lie.Killing

/-! A complex Lie algebra spanned by a real form acting by skew Hermitian
adjoint operators has Killing kernel equal to its centre. This elementary
trace argument avoids the general Killing-radical inclusion theorem. -/
namespace QuaternionicSymmetry.HermitianKillingForm
open scoped InnerProductSpace
noncomputable section

section Normed
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [FiniteDimensional ℂ L]

def SkewHermitian (A : L →ₗ[ℂ] L) : Prop :=
  ∀ v w, ⟪A v,w⟫_ℂ + ⟪v,A w⟫_ℂ = 0

lemma trace_comp_eq_neg_sum (A B : L →ₗ[ℂ] L) (hA : SkewHermitian A) :
    LinearMap.trace ℂ L (A.comp B) =
      - ∑ i, ⟪A (stdOrthonormalBasis ℂ L i), B (stdOrthonormalBasis ℂ L i)⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ L), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact eq_neg_of_add_eq_zero_right (hA _ _)

lemma trace_comp_im_zero (A B : L →ₗ[ℂ] L)
    (hA : SkewHermitian A) (hB : SkewHermitian B) :
    (LinearMap.trace ℂ L (A.comp B)).im = 0 := by
  have hc : starRingEnd ℂ (LinearMap.trace ℂ L (A.comp B)) =
      LinearMap.trace ℂ L (A.comp B) := by
    conv_lhs => rw [LinearMap.trace_comp_comm', trace_comp_eq_neg_sum B A hB]
    rw [map_neg, map_sum, trace_comp_eq_neg_sum A B hA]
    simp only [inner_conj_symm]
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

lemma eq_zero_of_trace_square_zero (A : L →ₗ[ℂ] L) (hA : SkewHermitian A)
    (htr : LinearMap.trace ℂ L (A.comp A) = 0) : A = 0 := by
  have hs := congrArg Complex.re htr
  rw [trace_comp_eq_neg_sum A A hA] at hs
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, Complex.neg_re, Complex.re_sum, RCLike.ofReal_re,
    Complex.zero_re, neg_eq_zero] at hs
  have hz (i : Fin (Module.finrank ℂ L)) : A (stdOrthonormalBasis ℂ L i) = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg
      ‖A (stdOrthonormalBasis ℂ L i)‖)).mp hs i (Finset.mem_univ _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  apply (stdOrthonormalBasis ℂ L).toBasis.ext
  intro i
  exact hz i

end Normed

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- Only a decomposition into two skew-adjoint real directions is needed. -/
theorem isKilling_of_decomposition
    (c : InnerProductSpace.Core ℂ L)
    (hDecomp : ∀ z : L, ∃ a b : L, z = a + Complex.I • b ∧
      (∀ v w, c.inner ⁅a,v⁆ w + c.inner v ⁅a,w⁆ = 0) ∧
      (∀ v w, c.inner ⁅b,v⁆ w + c.inner v ⁅b,w⁆ = 0))
    (hCenter : LieAlgebra.center ℂ L = ⊥) : LieAlgebra.IsKilling ℂ L := by
  letI : InnerProductSpace.Core ℂ L := c
  letI : NormedAddCommGroup L := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ L := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ L)
  constructor
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨a,b,hzab,ha,hb⟩ := hDecomp z
  have hk (y : L) : killingForm ℂ L z y = 0 := by
    rw [LieModule.traceForm_comm]
    exact hz y (LieSubmodule.mem_top _)
  have ha' : SkewHermitian (LieAlgebra.ad ℂ L a) := ha
  have hb' : SkewHermitian (LieAlgebra.ad ℂ L b) := hb
  have hreal (x y : L) (hx : SkewHermitian (LieAlgebra.ad ℂ L x))
      (hy : SkewHermitian (LieAlgebra.ad ℂ L y)) : (killingForm ℂ L x y).im = 0 :=
    trace_comp_im_zero _ _ hx hy
  have haa := hreal a a ha' ha'
  have hba := hreal b a hb' ha'
  have hab := hreal a b ha' hb'
  have hbb := hreal b b hb' hb'
  have hza := congrArg Complex.re (hk a)
  have hzb := congrArg Complex.im (hk b)
  rw [hzab, map_add, map_smul] at hza hzb
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.mul_im, zero_mul, one_mul, zero_sub,
    zero_add, Complex.zero_re, Complex.zero_im, hba, hab] at hza hzb
  have ha0 : LieAlgebra.ad ℂ L a = 0 := eq_zero_of_trace_square_zero _ ha'
    (Complex.ext (by simpa using hza) haa)
  have hb0 : LieAlgebra.ad ℂ L b = 0 := eq_zero_of_trace_square_zero _ hb'
    (Complex.ext (by simpa using hzb) hbb)
  have hz0 : LieAlgebra.ad ℂ L z = 0 := by rw [hzab, map_add, map_smul, ha0, hb0]; simp
  have hc : z ∈ LieAlgebra.center ℂ L := by
    rw [← LieAlgebra.self_module_ker_eq_center, LieModule.mem_ker]
    intro w
    exact congrArg (fun A : L →ₗ[ℂ] L => A w) hz0
  simpa only [hCenter] using hc

end
end QuaternionicSymmetry.HermitianKillingForm
