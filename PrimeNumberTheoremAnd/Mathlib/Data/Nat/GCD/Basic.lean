/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruben Van de Velde
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs

theorem Nat.gcd_dvd_lcm {a b : ℕ} : Nat.gcd a b ∣ Nat.lcm a b :=
  gcd_dvd_left a b |>.trans <| dvd_lcm_left a b
