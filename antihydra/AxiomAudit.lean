/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Bryan Ehrlich
-/
module

import Solution

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for (decl, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? decl then
      if env.header.moduleNames[idx.toNat]! == `Solution then
        let axioms ← Lean.collectAxioms decl
        if axioms.any (fun axiomName => !allowed.contains axiomName) then
          throwError m!"{decl} depends on an unpermitted axiom: {axioms}"

/-- info: 'AntihydraPalomar.horizontal_ray_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AntihydraPalomar.horizontal_ray_halts

/-- info: 'AntihydraPalomar.no_semilinear_safety_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AntihydraPalomar.no_semilinear_safety_invariant

/-- info: 'AntihydraPalomar.no_presburger_safety_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AntihydraPalomar.no_presburger_safety_invariant

/-! Print the checked axiom lists for the build record. -/
#print axioms AntihydraPalomar.horizontal_ray_halts
#print axioms AntihydraPalomar.no_semilinear_safety_invariant
#print axioms AntihydraPalomar.no_presburger_safety_invariant
