import Mathlib

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

namespace ELVAE

/-
First formal check of the ELVAE canonical reduction.

For ν > 0, define

    β = cν / (1 + ν).

Then β lies on the fiber

    c = β(1 + 1/ν).
-/

theorem fiber_parameterization
    (c ν : ℝ)
    (hν : 0 < ν) :
    (c * ν / (1 + ν)) * (1 + 1 / ν) = c := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have h1ν0 : 1 + ν ≠ 0 := by
    linarith
  field_simp [hν0, h1ν0]
  <;> ring

/-
If c > 0 and ν > 0, the corresponding β is also positive.
-/

theorem beta_positive
    (c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν) :
    0 < c * ν / (1 + ν) := by
  positivity

end ELVAE
