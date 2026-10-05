import Mathlib.Tactic
import QuaternionicSymmetry.Certificates

/-!
  Certificate identities over arbitrary commutative algebras over `ℚ`.

  All rational coefficients enter through `algebraMap ℚ R`; no inverse in `R`
  is used.  This is the form suitable for evaluation in rings with nilpotents.
-/

namespace QuaternionicSymmetry
namespace AlgebraCertificates

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

abbrev P := MvPolynomial (Fin 5) ℚ

noncomputable def c (x : ℚ) : P := MvPolynomial.C x

/-- The five formal variables are `u,z₁,z₂,z₃,z₄`, in that order. -/
noncomputable def U : P := MvPolynomial.X 0
noncomputable def Z₁ : P := MvPolynomial.X 1
noncomputable def Z₂ : P := MvPolynomial.X 2
noncomputable def Z₃ : P := MvPolynomial.X 3
noncomputable def Z₄ : P := MvPolynomial.X 4

def b₁ (n : ℚ) : P := c (-(n - 1) / 12) * U + c (1 / 24) * Z₁
def b₂ (n : ℚ) : P :=
  c ((n - 7) / 1440) * U^2 - c (1 / 480) * U * Z₁ + c (1 / 2880) * Z₂
def b₃ (n : ℚ) : P :=
  c (-(n - 31) / 90720) * U^3 + c (1 / 12096) * U^2 * Z₁
    - c (1 / 12096) * U * Z₂ + c (1 / 181440) * Z₃
def b₄ (n : ℚ) : P :=
  c ((n - 127) / 4838400) * U^4 - c (1 / 345600) * U^3 * Z₁
    + c (1 / 138240) * U^2 * Z₂ - c (1 / 345600) * U * Z₃ + c (1 / 9676800) * Z₄

def A₀ : P := 1
def A₁ (n : ℚ) : P := b₁ n
def A₂ (n : ℚ) : P := b₂ n + c (1 / 2) * b₁ n ^ 2
def A₃ (n : ℚ) : P := b₃ n + b₁ n * b₂ n + c (1 / 6) * b₁ n ^ 3
def A₄ (n : ℚ) : P :=
  b₄ n + b₁ n * b₃ n + c (1 / 2) * b₂ n ^ 2
    + c (1 / 2) * b₁ n ^ 2 * b₂ n + c (1 / 24) * b₁ n ^ 4

def F₂ : P := c (1 / 1152) * Z₁^2 + c (1 / 2880) * Z₂
def F₃ : P := c (1 / 82944) * Z₁^3 + c (1 / 69120) * Z₁ * Z₂ + c (1 / 181440) * Z₃
def F₄ : P :=
  c (1 / 7962624) * Z₁^4 + c (1 / 3317760) * Z₁^2 * Z₂ + c (1 / 16588800) * Z₂^2
    + c (1 / 4354560) * Z₁ * Z₃ + c (1 / 9676800) * Z₄

def M₂₁ (r : ℚ) : P := c (1 / (r * (r + 1))) * (Z₁^2 + Z₂)
def M₃₁ (r : ℚ) : P := c (1 / (r * (r + 1) * (r + 2))) * (Z₁^3 + c 3 * Z₁ * Z₂ + c 2 * Z₃)
def M₃₂ (r : ℚ) : P :=
  c (4 / (r * (r - 1) * (r + 1) * (r + 2)))
    * (c (2 * r + 1) * Z₁^3 + c (3 * (r - 1)) * Z₁ * Z₂ + c (r - 4) * Z₃)

def K₂ : P := c 16 * U^2 * A₀
def K₃ : P := c 32 * U^2 * A₁ 3 + c (112 / 3) * U^3 * A₀
def K₄ : P := c 64 * U^3 * A₁ 4 + c 64 * U^4 * A₀
def K₅ : P := c 128 * U^3 * A₂ 5 + c 192 * U^4 * A₁ 5 + c (1936 / 15) * U^5 * A₀
def K₆ : P := c 256 * U^4 * A₂ 6 + c (1024 / 3) * U^5 * A₁ 6 + c (9728 / 45) * U^6 * A₀
def K₇ : P := c 512 * U^4 * A₃ 7 + c (2816 / 3) * U^5 * A₂ 7
  + c (35776 / 45) * U^6 * A₁ 7 + c (79136 / 189) * U^7 * A₀
def K₈ : P := c 1024 * U^5 * A₃ 8 + c (5120 / 3) * U^6 * A₂ 8
  + c (4096 / 3) * U^7 * A₁ 8 + c (44032 / 63) * U^8 * A₀
def K₉ : P := c 2048 * U^5 * A₄ 9 + c (13312 / 3) * U^6 * A₃ 9
  + c (13568 / 3) * U^7 * A₂ 9 + c (916096 / 315) * U^8 * A₁ 9 + c (3777808 / 2835) * U^9 * A₀
def K₁₀ : P := c 4096 * U^6 * A₄ 10 + c 8192 * U^7 * A₃ 10
  + c (118784 / 15) * U^8 * A₂ 10 + c (4661248 / 945) * U^9 * A₁ 10 + c (1503232 / 675) * U^10 * A₀

def RHS₂ : P := c 16 * U^2
def RHS₃ : P := c 32 * U^3 + c (4 / 3) * Z₁ * U^2
def RHS₄ : P := c 48 * U^4 + c (8 / 3) * Z₁ * U^3
def RHS₅ : P := c 72 * U^5 + c (268 / 45) * Z₁ * U^4 + c 128 * F₂ * U^3
def RHS₆ : P := c 96 * U^6 + c (416 / 45) * Z₁ * U^5 + c 256 * F₂ * U^4
def RHS₇ : P := c 128 * U^7 + c (104 / 7) * Z₁ * U^6
  + (c (50048 / 945) * M₂₁ 16 + c (334 / 945) * Z₁^2) * U^5 + c 512 * F₃ * U^4
def RHS₈ : P := c 160 * U^8 + c (6448 / 315) * Z₁ * U^7
  + (c (10792 / 105) * M₂₁ 18 + c (542 / 945) * Z₁^2) * U^6 + c 1024 * F₃ * U^5
def RHS₉ : P := c 200 * U^9 + c (45128 / 1575) * Z₁ * U^8
  + (c (8752 / 45) * M₂₁ 20 + c (14704 / 14175) * Z₁^2) * U^7
  + (c (2992 / 405) * M₃₁ 20 + c (2090 / 81) * M₃₂ 20 + c (239 / 28350) * Z₁^3) * U^6
  + c 2048 * F₄ * U^5
def RHS₁₀ : P := c 240 * U^10 + c (8288 / 225) * Z₁ * U^9
  + (c (1495736 / 4725) * M₂₁ 22 + c (21278 / 14175) * Z₁^2) * U^8
  + (c (4048 / 4725) * M₃₁ 22 + c (23276 / 405) * M₃₂ 22 + c (194 / 14175) * Z₁^3) * U^7
  + c 4096 * F₄ * U^6

abbrev F := FractionRing P

@[simp] theorem map_C (a : ℚ) : algebraMap P F (MvPolynomial.C a) = (a : F) := by
  rw [← MvPolynomial.algebraMap_eq]
  rw [← IsScalarTower.algebraMap_apply ℚ P F]
  rfl

theorem polynomial_certificate₃ : K₃ = RHS₃ := by
  apply IsFractionRing.injective P F
  simp only [K₃, RHS₃, A₁, A₀, b₁, c, U, Z₁, map_add, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₂ : K₂ = RHS₂ := by
  simp [K₂, RHS₂, A₀]

theorem polynomial_certificate₄ : K₄ = RHS₄ := by
  apply IsFractionRing.injective P F
  simp only [K₄, RHS₄, A₁, A₀, b₁, c, U, Z₁, map_add, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₅ : K₅ = RHS₅ := by
  apply IsFractionRing.injective P F
  simp only [K₅, RHS₅, A₂, A₁, A₀, b₂, b₁, F₂, c, U, Z₁, Z₂,
    map_add, map_sub, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₆ : K₆ = RHS₆ := by
  apply IsFractionRing.injective P F
  simp only [K₆, RHS₆, A₂, A₁, A₀, b₂, b₁, F₂, c, U, Z₁, Z₂,
    map_add, map_sub, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₇ : K₇ = RHS₇ := by
  apply IsFractionRing.injective P F
  simp only [K₇, RHS₇, A₃, A₂, A₁, A₀, b₃, b₂, b₁, F₃, M₂₁, c, U, Z₁, Z₂, Z₃,
    map_add, map_sub, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₈ : K₈ = RHS₈ := by
  apply IsFractionRing.injective P F
  simp only [K₈, RHS₈, A₃, A₂, A₁, A₀, b₃, b₂, b₁, F₃, M₂₁, c, U, Z₁, Z₂, Z₃,
    map_add, map_sub, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₉ : K₉ = RHS₉ := by
  apply IsFractionRing.injective P F
  simp only [K₉, RHS₉, A₄, A₃, A₂, A₁, A₀, b₄, b₃, b₂, b₁, F₄, M₃₁, M₃₂, M₂₁,
    c, U, Z₁, Z₂, Z₃, Z₄, map_add, map_sub, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

theorem polynomial_certificate₁₀ : K₁₀ = RHS₁₀ := by
  apply IsFractionRing.injective P F
  simp only [K₁₀, RHS₁₀, A₄, A₃, A₂, A₁, A₀, b₄, b₃, b₂, b₁, F₄, M₃₁, M₃₂, M₂₁,
    c, U, Z₁, Z₂, Z₃, Z₄, map_add, map_sub, map_mul, map_pow, map_one]
  simp_rw [map_C]
  norm_num
  ring

/-- Evaluate the universal certificate polynomial in any commutative `ℚ`-algebra. -/
noncomputable def evaluate (u z₁ z₂ z₃ z₄ : R) : P →ₐ[ℚ] R :=
  MvPolynomial.aeval ![u, z₁, z₂, z₃, z₄]

@[simp] theorem evaluate_U (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ U = u := by
  simp [evaluate, U]

@[simp] theorem evaluate_Z₁ (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ Z₁ = z₁ := by
  simp [evaluate, Z₁]

@[simp] theorem evaluate_Z₂ (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ Z₂ = z₂ := by
  simp [evaluate, Z₂]

@[simp] theorem evaluate_Z₃ (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ Z₃ = z₃ := by
  simp [evaluate, Z₃]

@[simp] theorem evaluate_Z₄ (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ Z₄ = z₄ := by
  simp [evaluate, Z₄]

@[simp] theorem evaluate_c (u z₁ z₂ z₃ z₄ : R) (a : ℚ) :
    evaluate u z₁ z₂ z₃ z₄ (c a) = algebraMap ℚ R a := by
  simp [evaluate, c]

theorem certificate₂_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₂ = evaluate u z₁ z₂ z₃ z₄ RHS₂ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₂

theorem certificate₃_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₃ = evaluate u z₁ z₂ z₃ z₄ RHS₃ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₃

theorem certificate₄_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₄ = evaluate u z₁ z₂ z₃ z₄ RHS₄ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₄

theorem certificate₅_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₅ = evaluate u z₁ z₂ z₃ z₄ RHS₅ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₅

theorem certificate₆_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₆ = evaluate u z₁ z₂ z₃ z₄ RHS₆ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₆

theorem certificate₇_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₇ = evaluate u z₁ z₂ z₃ z₄ RHS₇ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₇

theorem certificate₈_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₈ = evaluate u z₁ z₂ z₃ z₄ RHS₈ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₈

theorem certificate₉_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₉ = evaluate u z₁ z₂ z₃ z₄ RHS₉ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₉

theorem certificate₁₀_eval (u z₁ z₂ z₃ z₄ : R) :
    evaluate u z₁ z₂ z₃ z₄ K₁₀ = evaluate u z₁ z₂ z₃ z₄ RHS₁₀ :=
  congrArg (fun p : P => evaluate u z₁ z₂ z₃ z₄ p) polynomial_certificate₁₀

section FieldBridge

variable {S : Type*}

private theorem vector₀ (u z₁ z₂ z₃ z₄ : S) : (![u, z₁, z₂, z₃, z₄] : Fin 5 → S) 0 = u := rfl
private theorem vector₁ (u z₁ z₂ z₃ z₄ : S) : (![u, z₁, z₂, z₃, z₄] : Fin 5 → S) 1 = z₁ := rfl
private theorem vector₂ (u z₁ z₂ z₃ z₄ : S) : (![u, z₁, z₂, z₃, z₄] : Fin 5 → S) 2 = z₂ := rfl
private theorem vector₃ (u z₁ z₂ z₃ z₄ : S) : (![u, z₁, z₂, z₃, z₄] : Fin 5 → S) 3 = z₃ := rfl
private theorem vector₄ (u z₁ z₂ z₃ z₄ : S) : (![u, z₁, z₂, z₃, z₄] : Fin 5 → S) 4 = z₄ := rfl

variable [Field S] [CharZero S]

private theorem map_rat (a : ℚ) : algebraMap ℚ S a = (a : S) := map_ratCast (algebraMap ℚ S) a

theorem evaluate_RHS₂_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₂ = Certificates.K₂ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₂]
  simp only [evaluate, RHS₂, c, U, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀]
  simp_rw [map_rat]
  ring

theorem evaluate_RHS₃_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₃ = Certificates.K₃ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₃]
  simp only [evaluate, RHS₃, c, U, Z₁, map_add, map_mul, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁]
  simp_rw [map_rat]
  ring

theorem evaluate_K₂_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₂ = Certificates.K₂ u z₁ z₂ z₃ z₄ :=
  (certificate₂_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₂_field u z₁ z₂ z₃ z₄)

theorem evaluate_K₃_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₃ = Certificates.K₃ u z₁ z₂ z₃ z₄ :=
  (certificate₃_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₃_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₄_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₄ = Certificates.K₄ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₄]
  simp only [evaluate, RHS₄, c, U, Z₁, map_add, map_mul, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁]
  simp_rw [map_rat]
  ring

theorem evaluate_K₄_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₄ = Certificates.K₄ u z₁ z₂ z₃ z₄ :=
  (certificate₄_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₄_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₅_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₅ = Certificates.K₅ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₅]
  simp only [evaluate, RHS₅, F₂, Certificates.F₂, c, U, Z₁, Z₂, map_add, map_mul, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁, vector₂]
  simp_rw [map_rat]
  ring

theorem evaluate_K₅_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₅ = Certificates.K₅ u z₁ z₂ z₃ z₄ :=
  (certificate₅_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₅_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₆_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₆ = Certificates.K₆ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₆]
  simp only [evaluate, RHS₆, F₂, Certificates.F₂, c, U, Z₁, Z₂, map_add, map_mul, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁, vector₂]
  simp_rw [map_rat]
  ring

theorem evaluate_K₆_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₆ = Certificates.K₆ u z₁ z₂ z₃ z₄ :=
  (certificate₆_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₆_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₇_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₇ = Certificates.K₇ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₇]
  simp only [evaluate, RHS₇, F₃, M₂₁, Certificates.F₃, Certificates.M₂₁, c, U, Z₁, Z₂, Z₃,
    map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁, vector₂, vector₃]
  simp_rw [map_rat]
  ring

theorem evaluate_K₇_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₇ = Certificates.K₇ u z₁ z₂ z₃ z₄ :=
  (certificate₇_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₇_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₈_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₈ = Certificates.K₈ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₈]
  simp only [evaluate, RHS₈, F₃, M₂₁, Certificates.F₃, Certificates.M₂₁, c, U, Z₁, Z₂, Z₃,
    map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁, vector₂, vector₃]
  simp_rw [map_rat]
  ring

theorem evaluate_K₈_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₈ = Certificates.K₈ u z₁ z₂ z₃ z₄ :=
  (certificate₈_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₈_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₉_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₉ = Certificates.K₉ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₉]
  simp only [evaluate, RHS₉, F₄, M₃₁, M₃₂, M₂₁, Certificates.F₄, Certificates.M₃₁,
    Certificates.M₃₂, Certificates.M₂₁, c, U, Z₁, Z₂, Z₃, Z₄,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁, vector₂, vector₃, vector₄]
  simp_rw [map_rat]
  ring

theorem evaluate_K₉_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₉ = Certificates.K₉ u z₁ z₂ z₃ z₄ :=
  (certificate₉_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₉_field u z₁ z₂ z₃ z₄)

theorem evaluate_RHS₁₀_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ RHS₁₀ = Certificates.K₁₀ u z₁ z₂ z₃ z₄ := by
  rw [Certificates.certificate₁₀]
  simp only [evaluate, RHS₁₀, F₄, M₃₁, M₃₂, M₂₁, Certificates.F₄, Certificates.M₃₁,
    Certificates.M₃₂, Certificates.M₂₁, c, U, Z₁, Z₂, Z₃, Z₄,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [vector₀, vector₁, vector₂, vector₃, vector₄]
  simp_rw [map_rat]
  ring

theorem evaluate_K₁₀_field (u z₁ z₂ z₃ z₄ : S) :
    evaluate u z₁ z₂ z₃ z₄ K₁₀ = Certificates.K₁₀ u z₁ z₂ z₃ z₄ :=
  (certificate₁₀_eval u z₁ z₂ z₃ z₄).trans (evaluate_RHS₁₀_field u z₁ z₂ z₃ z₄)

end FieldBridge

end
end AlgebraCertificates
end QuaternionicSymmetry
