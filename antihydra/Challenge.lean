/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs

/-!
# Antihydra has no semilinear inductive safety invariant

States are pairs `(x, c)` of natural numbers, with seed `(8, 0)`.
Each successful round sends `x` to `⌊3x/2⌋`. An even input earns two
units of credit. An odd input spends one unit, and halts at zero credit.

An inductive safety invariant contains the seed and has a successful
successor within the set for every state it contains. A semilinear set
is a finite union of translates of finitely generated additive
submonoids, expressed here by Mathlib's `IsSemilinearSet`.
-/

@[expose] public section

namespace AntihydraPalomar

/-- One arithmetic round. `none` counts the attempted step that overspends. -/
def step (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  if p.1 % 2 = 0 then some (3 * p.1 / 2, p.2 + 2)
  else if p.2 = 0 then none
  else some (3 * p.1 / 2, p.2 - 1)

/-- A set containing the seed whose every member takes a successful step within the set. -/
def IsSafetyInvariant (I : Set (ℕ × ℕ)) : Prop :=
  (8, 0) ∈ I ∧ ∀ p ∈ I, ∃ q ∈ I, step p = some q

/-- No semilinear set of natural-number pairs is an inductive safety invariant
for the shifted Antihydra recurrence from `(8, 0)`. -/
theorem no_semilinear_safety_invariant (I : Set (ℕ × ℕ)) (hI : IsSemilinearSet I) :
    ¬ IsSafetyInvariant I := sorry

end AntihydraPalomar
