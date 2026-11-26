import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_17999 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)), x2 ≠ x3 → x1 x2 x4 → x1 x3 x4 → x1 x2 x5 → x1 x3 x5 → x4 = x5 := by
  decide +kernel
