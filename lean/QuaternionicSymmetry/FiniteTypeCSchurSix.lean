import QuaternionicSymmetry.QuarticOrbitalEleven

/-! Finite type-C orbital polynomials through Weyl weight six, including zero.

The complete and elementary symmetric functions are constructed by Newton
recurrences in the independent power sums `p₁,…,p₆`.  The displayed Schur
functions are their Jacobi--Trudi determinants (using the dual determinant
when it is shorter).  The orbital polynomial is the finite type-C Schur sum
with factorial normalization; it is an algebraic polynomial and carries no
analytic integral interpretation. -/

namespace QuaternionicSymmetry.FiniteTypeCSchurSix

open MvPolynomial
noncomputable section

abbrev P := MvPolynomial (Fin 6) ℚ

def p1 : P := X 0
def p2 : P := X 1
def p3 : P := X 2
def p4 : P := X 3
def p5 : P := X 4
def p6 : P := X 5

def h0 : P := 1
def h1 : P := p1
def h2 : P := C (1 / 2) * (p1 * h1 + p2)
def h3 : P := C (1 / 3) * (p1 * h2 + p2 * h1 + p3)
def h4 : P := C (1 / 4) * (p1 * h3 + p2 * h2 + p3 * h1 + p4)
def h5 : P := C (1 / 5) * (p1 * h4 + p2 * h3 + p3 * h2 + p4 * h1 + p5)
def h6 : P := C (1 / 6) *
  (p1 * h5 + p2 * h4 + p3 * h3 + p4 * h2 + p5 * h1 + p6)

def e1 : P := h1
def e2 : P := h1 * e1 - h2
def e3 : P := h1 * e2 - h2 * e1 + h3
def e4 : P := h1 * e3 - h2 * e2 + h3 * e1 - h4
def e5 : P := h1 * e4 - h2 * e3 + h3 * e2 - h4 * e1 + h5
def e6 : P := h1 * e5 - h2 * e4 + h3 * e3 - h4 * e2 + h5 * e1 - h6

/-- Jacobi--Trudi Schur functions for all partitions of weights one through
six.  Every branch is an explicit determinant of size at most three, with
`h` for rows and `e` for the conjugate partition when shorter. -/
def schur : List ℕ → P
  | [] => 1
  | [1] => h1
  | [2] => h2
  | [1, 1] => e2
  | [3] => h3
  | [2, 1] => h2 * h1 - h3
  | [1, 1, 1] => e3
  | [4] => h4
  | [3, 1] => h3 * h1 - h4
  | [2, 2] => h2 ^ 2 - h3 * h1
  | [2, 1, 1] => h2 * e2 - h3 * h1 + h4
  | [1, 1, 1, 1] => e4
  | [5] => h5
  | [4, 1] => h4 * h1 - h5
  | [3, 2] => h3 * h2 - h4 * h1
  | [3, 1, 1] => h3 * e2 - h4 * h1 + h5
  | [2, 2, 1] => h1 * h2 ^ 2 - h2 * h3 - h1 ^ 2 * h3 + h1 * h4
  | [2, 1, 1, 1] => e4 * e1 - e5
  | [1, 1, 1, 1, 1] => e5
  | [6] => h6
  | [5, 1] => h5 * h1 - h6
  | [4, 2] => h4 * h2 - h5 * h1
  | [4, 1, 1] => h4 * e2 - h5 * h1 + h6
  | [3, 3] => h3 ^ 2 - h4 * h2
  | [3, 2, 1] => h3 * (h2 * h1 - h3) - h4 * h1 ^ 2 + h5 * h1
  | [3, 1, 1, 1] => e4 * (e1 ^ 2 - e2) - e5 * e1 + e6
  | [2, 2, 2] => h2 ^ 3 - C 2 * h1 * h2 * h3 + h3 ^ 2 + h4 * h1 ^ 2 - h4 * h2
  | [2, 2, 1, 1] => e4 * e2 - e5 * e1
  | [2, 1, 1, 1, 1] => e5 * e1 - e6
  | [1, 1, 1, 1, 1, 1] => e6
  | _ => 0

def partitions : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[1]]
  | 2 => [[2], [1, 1]]
  | 3 => [[3], [2, 1], [1, 1, 1]]
  | 4 => [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]]
  | 5 => [[5], [4, 1], [3, 2], [3, 1, 1], [2, 2, 1], [2, 1, 1, 1],
      [1, 1, 1, 1, 1]]
  | 6 => [[6], [5, 1], [4, 2], [4, 1, 1], [3, 3], [3, 2, 1],
      [3, 1, 1, 1], [2, 2, 2], [2, 2, 1, 1], [2, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1]]
  | _ => []

def powerSum (a : List ℕ) (j : ℕ) : ℚ :=
  (a.map fun x => (x : ℚ) ^ j).sum

def schurValue (a lam : List ℕ) : ℚ :=
  MvPolynomial.aeval (fun i => powerSum a (i.val + 1)) (schur lam)

/-- The finite type-C orbital polynomial at quaternionic dimension `n`.
The listed spectrum has implicit zero entries up to length `n`; admissibility
is checked separately for each witness. -/
def orbital (n k : ℕ) (a : List ℕ) : P :=
  ∑ lam ∈ (partitions k).toFinset,
    C ((4 : ℚ) ^ k * QuarticOrbitalEleven.factorialRho n lam * schurValue a lam) *
      schur lam

/-- The empty partition gives the unit constant term required by normalized
Haar measure. -/
theorem orbital_zero (n : ℕ) (a : List ℕ) : orbital n 0 a = 1 := by
  simp [orbital, partitions, QuarticOrbitalEleven.factorialRho,
    schurValue, schur]

end
end QuaternionicSymmetry.FiniteTypeCSchurSix
