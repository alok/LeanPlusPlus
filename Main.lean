import LeanPlusPlus

/-- Tests for the increment operator -/
def main : IO Unit := do
  assert! 2 ≠ 3
  assert! (5⁺⁺) = 6
  IO.println "All increment tests passed!"
