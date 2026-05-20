import Mathlib
/-

# Brahmagupta's identity

Show [Brahmagupta's identity][brahmagupta].

[brahmagupta]: https://en.wikipedia.org/wiki/Brahmagupta%27s_identity

-/
example (n a b c d : ℝ)
  : (a^2 + n*b^2) * (c^2 + n*d^2)
    = (a*c - n*b*d)^2 + n*(a*d + b*c)^2
:= by
  -- __Solution__
  grind
/-


# Woodbury formula

Show [Woodbury formula][woodbury] for scalars.

[woodbury]: https://en.wikipedia.org/wiki/Woodbury_matrix_identity

-/
example (a c u v : ℝ)
  (h1 : a + u*c*v ≠ 0) (h2 : a ≠ 0) (h3 : c ≠ 0)
  : (a + u*c*v)⁻¹ = a⁻¹ - a⁻¹*u * (c⁻¹ + v*a⁻¹*u)⁻¹ * v*a⁻¹
:= by
  -- __Solution__
  grind
/-


# Linear equations

Show
-/
example (x y z : ℝ)
  : 1*x + 2*y + 3*z = 1 ∧
    2*x + 4*y + 5*z = 0 ∧
    3*x + 5*y + 6*z = 0
    ↔ x = 1 ∧ y = -3 ∧ z = 2
:= by
  -- __Solution__
  grind
/-

The above proof verifies that the given numbers are the unique solution of the system. The following Python code can be used to find them in the first place.

```python
import numpy as np
A = np.array([
    [1, 2, 3],
    [2, 4, 5],
    [3, 5, 6],
])
b = np.array([1, 0, 0])
np.linalg.solve(A, b)
```


# Roots of polynomials

Show
-/
example (x : ℝ)
  : x^2 - 3*x + 2 = 0
    ↔ x = 1 ∨ x = 2
:= by
  -- __Solution__
  grind
/-

The above proof verifies that the given numbers are the roots of the polynomial. The following Python code can be used to find them in the first place.

```python
import numpy as np
coeffs = [1, -3, 2]
np.roots(coeffs)
```


# Factorization of multivariate polynomials

The following example is taken from [SymPy's manual][sympy].

[sympy]: https://docs.sympy.org/latest/modules/polys/wester.html#multivariate-gcd-and-factorization

Show
-/
example (x y z : ℝ)
  : -36*x^31*y^16*z^4 - 60*x^29*y^7*z^7
    - 102*x^27*y^8*z^13 - 564*x^26*y^21*z^12
    + 72*x^24*y^25*z^6 - 940*x^24*y^12*z^15
    + 120*x^22*y^16*z^9 - 240*x^22*y^14*z
    - 1598*x^22*y^13*z^21 + 204*x^20*y^17*z^15
    - 3760*x^17*y^19*z^9 + 480*x^15*y^23*z^3
    + 288*x^10*y^35*z^12 + 60*x^9*y^16*z^4
    + 480*x^8*y^26*z^15 + 100*x^7*y^7*z^7
    + 816*x^6*y^27*z^21 + 170*x^5*y^8*z^13
    + 1920*x*y^33*z^9 + 400*y^14*z
    =
    -2*y^7*z
    * (
        6*x^9*y^9*z^3 + 10*x^7*z^6
        + 17*x^5*y*z^12 + 40*y^7
    ) * (
        3*x^22 + 47*x^17*y^5*z^8
        - 6*x^15*y^9*z^2 - 24*x*y^19*z^8 - 5
    )
:= by
  -- __Solution__
  grind
/-

The above proof verifies correctness of the factorization. The following Python code can be used to find it in the first place.

```python
import sympy as sp
from sympy.abc import x, y, z
p = (
    -36*x**31*y**16*z**4 - 60*x**29*y**7*z**7
    - 102*x**27*y**8*z**13 - 564*x**26*y**21*z**12
    + 72*x**24*y**25*z**6 - 940*x**24*y**12*z**15
    + 120*x**22*y**16*z**9 - 240*x**22*y**14*z
    - 1598*x**22*y**13*z**21 + 204*x**20*y**17*z**15
    - 3760*x**17*y**19*z**9 + 480*x**15*y**23*z**3
    + 288*x**10*y**35*z**12 + 60*x**9*y**16*z**4
    + 480*x**8*y**26*z**15 + 100*x**7*y**7*z**7
    + 816*x**6*y**27*z**21 + 170*x**5*y**8*z**13
    + 1920*x*y**33*z**9 + 400*y**14*z
)
str(sp.factor(p)).replace('**', '^')
```


# Elementary case of Young's inequality

Show an elementary case of [Young's inequality][young].

[young]: https://en.wikipedia.org/wiki/Young%27s_inequality_for_products#Elementary_case

-/
lemma elem_young (a b : ℝ) :
  a * b ≤ a^2/2 + b^2/2
:= by
  have : (a - b)^2 ≥ 0 := by positivity
  grind
/-


# Peter-Paul inequality

Show [Peter-Paul][peter-paul] inequality.

[peter-paul]: https://en.wikipedia.org/wiki/Young%27s_inequality_for_products#Elementary_case

-/
example (a b ε : ℝ) (h : ε > 0) :
  a * b ≤ a^2/(2*ε) + ε*b^2/2
:= calc
  a * b
  _ = (a*(√ε)⁻¹) * (√ε*b) := by
    -- __Solution__
    grind
  _ ≤ (a*(√ε)⁻¹)^2/2 + (√ε*b)^2/2 := by
    exact elem_young (a*(√ε)⁻¹) (√ε*b)
  _ = a^2/(2*ε) + ε*b^2/2 := by
    -- __Solution__
    grind
