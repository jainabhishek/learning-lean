import Std

def sumTo : Nat -> Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero =>
      simp [sumTo]
  | succ n ih =>
      calc
        2 * sumTo (Nat.succ n)
            = 2 * (sumTo n + Nat.succ n) := by simp [sumTo]
        _   = 2 * sumTo n + 2 * Nat.succ n := by simp [Nat.mul_add]
        _   = n * (n + 1) + 2 * Nat.succ n := by simp [ih]
        _   = n * (n + 1) + 2 * (n + 1) := by simp [Nat.succ_eq_add_one]
        _   = (n + 2) * (n + 1) := by simp [Nat.add_mul]
        _   = (n + 1) * (n + 2) := by simp [Nat.mul_comm]
        _   = Nat.succ n * (Nat.succ n + 1) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]
