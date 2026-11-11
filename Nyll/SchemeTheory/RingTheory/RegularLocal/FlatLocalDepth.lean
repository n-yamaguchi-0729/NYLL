/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Depth does not decrease under a flat local homomorphism

Every weakly regular sequence in the original maximal ideal remains
regular after flat base change. Locality keeps its images in the target
maximal ideal. Taking suprema gives the depth inequality without a
Noetherian hypothesis.
-/

@[expose] public section

open RingTheory IsLocalRing

namespace SchemeTheory

/-- Flat local homomorphisms preserve every lower bound on ring depth. -/
theorem depth_le_depth_of_flat_localHom
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : f.Flat) :
    Module.depth R R ≤ Module.depth S S := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  refine sSup_le_sSup ?_
  rintro _ ⟨s, hs, hmem, rfl⟩
  refine ⟨s.map f, hs.of_flat, ?_, by rw [List.length_map]⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact map_nonunit f a (hmem a ha)

end SchemeTheory
