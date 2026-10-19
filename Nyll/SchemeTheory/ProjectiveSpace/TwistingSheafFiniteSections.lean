/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafSectionExtension
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.Tensor.ModuleTwistSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.Choose

/-!
# Extending finite affine generators in a common twist degree

For a finite-type quasicoherent module on projective space, each actual
standard-chart section module has finitely many generators. Each generator
extends after twisting. A common bound over the finite collection of all
these generators, followed by multiplication by coordinate sections,
extends every generator in each degree beyond this bound.

The output includes the original finite generating sections and the actual
global sections with their restriction equations. No presentation of the
quasicoherent module by a graded module is an input.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped BigOperators

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Every finite-type quasicoherent module admits finite generators on all
standard charts that extend to actual global tensor-twist sections in every
sufficiently large degree. -/
theorem exists_finite_generators_twisting_extensions (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) F] :
    ∃ r : Fin (n + 1) → ℕ,
      ∃ s : ∀ i : Fin (n + 1), Fin (r i) → Γ(F, standardOpen R n i),
        (∀ i : Fin (n + 1),
          Submodule.span Γ(Proj 𝒜, standardOpen R n i) (Set.range (s i)) = ⊤) ∧
        ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
          ∃ z : ∀ i : Fin (n + 1),
            Fin (r i) → Γ(F ⊗ (twistingSheaf R n).tensorPow d, ⊤),
            ∀ (i : Fin (n + 1)) (a : Fin (r i)),
              (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map
                  (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (z i a) =
                tensorSections (s i a)
                  (((twistingSheaf R n).tensorPow d).presheaf.map
                    (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
                    (tensorPowSection (twistingCoordinateSection R n i) d)) := by
  classical
  have hgens : ∀ i : Fin (n + 1),
      ∃ r : ℕ, ∃ s : Fin r → Γ(F, standardOpen R n i),
        Submodule.span Γ(Proj 𝒜, standardOpen R n i) (Set.range s) = ⊤ := by
    intro i
    have : Module.Finite Γ(Proj 𝒜, standardOpen R n i) Γ(F, standardOpen R n i) :=
      moduleFinite_sections_of_isFiniteType F (standardOpen R n i)
        (Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos)
    exact Module.Finite.exists_fin (R := Γ(Proj 𝒜, standardOpen R n i))
      (M := Γ(F, standardOpen R n i))
  choose r s hs using hgens
  have hext := fun (i : Fin (n + 1)) (a : Fin (r i)) =>
    exists_twisting_section_extension R n F i (s i a)
  choose e z hz using hext
  let N : ℕ := ∑ i : Fin (n + 1), ∑ a : Fin (r i), e i a
  refine ⟨r, s, hs, N, ?_⟩
  intro d hd
  have he : ∀ (i : Fin (n + 1)) (a : Fin (r i)), e i a ≤ d := by
    intro i a
    have h₁ : e i a ≤ ∑ b : Fin (r i), e i b :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have h₂ : (∑ b : Fin (r i), e i b) ≤ N := by
      change (∑ b : Fin (r i), e i b) ≤ ∑ j : Fin (n + 1), ∑ b : Fin (r j), e j b
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (∑ b : Fin (r j), e j b))
        (Finset.mem_univ i)
    exact h₁.trans (h₂.trans hd)
  have hlarge := fun (i : Fin (n + 1)) (a : Fin (r i)) =>
    exists_tensor_twist_extension_of_le (twistingCoordinateSection R n i)
      (s i a) (he i a) (z i a) (hz i a)
  choose w hw using hlarge
  exact ⟨w, hw⟩

end AlgebraicGeometry.ProjSpace
