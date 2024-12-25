import LeanPlusPlus.Basic
import Lean.Meta.Tactic.Grind
open Lean
-- This module serves as the root of the `LeanPlusPlus` library.
-- Import modules here that should be built as part of the library.

/-- A class for types that have a "1", usually the multiplicative identity element of the type. -/
class One (α : Type) where
  one : α

/-!
Instances converting between `One α` and `OfNat α (nat_lit 1)`.
-/

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

/-- Postfix increment operator.
    Requires both `One` and `Add` instances for the type. Uses `⁺⁺` instead of `++` because it's already used for `Append`.

    Example:
    ```
    #eval (5⁺⁺)  -- returns 6
    #eval (n⁺⁺)  -- returns n + 1
    ``` -/
postfix:max (name := increment) "⁺⁺" => (· + 1)
