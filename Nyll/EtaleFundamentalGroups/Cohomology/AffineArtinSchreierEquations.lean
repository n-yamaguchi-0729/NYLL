/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierCharacters
import Nyll.GaloisCohomology.GroupTheory.FiniteTorsorInvariants

/-!
# Artin–Schreier equations from an affine torsor

Bijectivity of the original torsor tensor map and faithful flatness supply
trace one and descent of invariants. Consequently every character of the
specified finite deck group is represented by an actual Artin–Schreier
equation over the original base ring. Neither a trace-one element nor an
invariant-ring comparison is an extra hypothesis of the final statement.
-/

noncomputable section

namespace EtaleFundamentalGroups.Cohomology

open GaloisCohomology.FiniteTorsor

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [Fintype G] (ρ : G →* (S ≃ₐ[R] S))
  [Module.FaithfullyFlat R S]

/-- Trace one is a consequence of the actual affine torsor properties. -/
theorem exists_trace_one_of_tensorMap_bijective
    (hTensor : Function.Bijective (tensorMap R S ρ)) :
    ∃ t : S, ∑ g, ρ g t = 1 := by
  apply exists_trace_one R S ρ _ hTensor.surjective
  intro x hx
  obtain ⟨a, ha, _⟩ := existsUnique_base_of_fixed R S ρ hTensor.injective x hx
  exact ⟨a, ha⟩

omit [Fintype G] in
/-- Every prime-field character of the finite deck action has an actual
Artin–Schreier equation over the original base, with the prescribed positive
translation on its root. This statement also covers the zero character. -/
theorem exists_artinSchreierEquation_of_tensorMap_bijective
    [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP S p]
    (hTensor : Function.Bijective (tensorMap R S ρ))
    (χ : G →* Multiplicative (ZMod p)) :
    ∃ (a : R) (β : S), β ^ p - β = algebraMap R S a ∧
      ∀ g, ρ g β - β = (ZMod.castHom (dvd_refl p) S) (χ g).toAdd := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨t, ht⟩ := exists_trace_one_of_tensorMap_bijective R S ρ hTensor
  let act : G → S →+* S := fun g => (ρ g).toRingHom
  have hact (g h : G) (x : S) : act g (act h x) = act (g * h) x := by
    change ρ g (ρ h x) = ρ (g * h) x
    rw [map_mul]
    rfl
  obtain ⟨β, hβ⟩ := exists_translation_of_trace_one p act hact t ht χ
  obtain ⟨a, ha, _⟩ := existsUnique_artinSchreier_base_of_translation
    R S ρ p hTensor.injective χ β hβ
  exact ⟨a, β, ha.symm, hβ⟩

end EtaleFundamentalGroups.Cohomology
