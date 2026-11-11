/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.FiniteTorsorTrace
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Descent of invariant sections of an affine torsor

Faithfully flat equalizer descent and injectivity of the actual torsor tensor
map descend invariant elements to the original base ring. Applied to an
Artin–Schreier section this supplies its base equation. Sections with the same
deck translations give the same class in the original Artin–Schreier quotient.
No invariant-ring comparison is an additional input.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace GaloisCohomology.FiniteTorsor

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] (ρ : G →* (S ≃ₐ[R] S))
  [Module.FaithfullyFlat R S]

/-- The actual tensor-map criterion for a torsor, together with faithfully
flat descent, recovers every invariant in the original base ring. Only
injectivity of the tensor map is needed for this direction. -/
theorem existsUnique_base_of_fixed
    (hinj : Function.Injective (tensorMap R S ρ)) (x : S)
    (hx : ∀ g, ρ g x = x) :
    ∃! a : R, algebraMap R S a = x := by
  have heq : x ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] x := by
    apply hinj
    funext g
    rw [tensorMap_tmul, tensorMap_tmul, map_one, hx, mul_one, one_mul]
  have hzero : Algebra.TensorProduct.includeLeftSubRight R S x = 0 :=
    sub_eq_zero.mpr heq
  obtain ⟨a, ha⟩ := (Algebra.IsEffective.of_faithfullyFlat R S x).mp hzero
  refine ⟨a, ha, fun b hb => ?_⟩
  exact (FaithfulSMul.algebraMap_injective R S) (hb.trans ha.symm)

/-- The image of the original coefficient map is exactly the fixed elements
of the specified action; the converse uses that the action is by R-algebra
automorphisms. -/
theorem mem_range_algebraMap_iff_fixed
    (hinj : Function.Injective (tensorMap R S ρ)) (x : S) :
    x ∈ Set.range (algebraMap R S) ↔ ∀ g, ρ g x = x := by
  constructor
  · rintro ⟨a, rfl⟩ g
    exact (ρ g).commutes a
  · intro hx
    obtain ⟨a, ha, _⟩ := existsUnique_base_of_fixed R S ρ hinj x hx
    exact ⟨a, ha⟩

variable (p : ℕ) [Fact p.Prime] [CharP S p]

/-- A section with prime-field deck translations has its Artin–Schreier
value in the original base ring. This applies to the section constructed by
trace-one averaging. -/
theorem existsUnique_artinSchreier_base_of_translation
    (hinj : Function.Injective (tensorMap R S ρ))
    (χ : G →* Multiplicative (ZMod p)) (β : S)
    (hβ : ∀ g, ρ g β - β = (ZMod.castHom (dvd_refl p) S) (χ g).toAdd) :
    ∃! a : R, algebraMap R S a = β ^ p - β := by
  apply existsUnique_base_of_fixed R S ρ hinj
  intro g
  have ht := (sub_eq_iff_eq_add).mp (hβ g)
  have hp : ((ZMod.castHom (dvd_refl p) S) (χ g).toAdd) ^ p =
      (ZMod.castHom (dvd_refl p) S) (χ g).toAdd := by
    rw [← map_pow, ZMod.pow_card]
  rw [map_sub, map_pow, ht, add_pow_char, hp]
  ring

/-- Changing the trace-one section without changing its deck translations
does not change the resulting class in R/(Frobenius−id)R. Both base elements
and both upstairs roots are the original ones. -/
theorem artinSchreier_class_eq_of_translation_eq [CharP R p]
    (hinj : Function.Injective (tensorMap R S ρ))
    (a b : R) (β γ : S)
    (hβ : β ^ p - β = algebraMap R S a)
    (hγ : γ ^ p - γ = algebraMap R S b)
    (htranslation : ∀ g, ρ g β - β = ρ g γ - γ) :
    (a : R ⧸ ((frobenius R p).toAddMonoidHom - AddMonoidHom.id R).range) =
      (b : R ⧸ ((frobenius R p).toAddMonoidHom - AddMonoidHom.id R).range) := by
  have hfixed (g : G) : ρ g (γ - β) = γ - β := by
    rw [map_sub]
    have h := htranslation g
    linear_combination -h
  obtain ⟨c, hc, _⟩ := existsUnique_base_of_fixed R S ρ hinj (γ - β) hfixed
  apply QuotientAddGroup.eq.mpr
  refine ⟨c, ?_⟩
  change c ^ p - c = -a + b
  apply FaithfulSMul.algebraMap_injective R S
  rw [map_sub, map_pow, map_add, map_neg, hc, sub_pow_char]
  linear_combination hγ - hβ

end GaloisCohomology.FiniteTorsor
