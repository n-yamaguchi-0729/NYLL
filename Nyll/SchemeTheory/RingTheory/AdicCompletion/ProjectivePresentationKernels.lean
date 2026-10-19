/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveQuotientLifting
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Actual kernels of projective presentations under reduction

A commutative square restricts the original source map to the actual
presentation kernels. A lift in the source can be corrected inside an
ideal multiple whenever the target transition has that ideal as kernel.
This proves surjectivity of the induced kernel transition.

Projectivity over the actual quotient ring supplies a splitting of the
original presentation. Its kernel retraction proves that the ideal
filtration on the kernel is the filtration induced from the source.
Thus the restricted transition has precisely its original ideal multiple
as kernel. The finite projective kernel is constructed from this same
splitting; it is not supplied as an extra hypothesis.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w v' w'

variable {R : Type u} [CommRing R]
  {F : Type v} [AddCommGroup F] [Module R F]
  {P : Type w} [AddCommGroup P] [Module R P]

private def splitKernelRetraction (φ : F →ₗ[R] P) (s : P →ₗ[R] F)
    (hs : φ.comp s = LinearMap.id) : F →ₗ[R] φ.ker :=
  (LinearMap.id - s.comp φ).codRestrict φ.ker (by
    intro x
    change φ (x - s (φ x)) = 0
    have hsx : φ (s (φ x)) = φ x := LinearMap.congr_fun hs (φ x)
    rw [map_sub, hsx, sub_self])

private theorem splitKernelRetraction_subtype (φ : F →ₗ[R] P) (s : P →ₗ[R] F)
    (hs : φ.comp s = LinearMap.id) (x : φ.ker) :
    splitKernelRetraction φ s hs x.val = x := by
  apply Subtype.ext
  change x.val - s (φ x.val) = x.val
  rw [LinearMap.mem_ker.mp x.property, map_zero, sub_zero]

/-- A surjection from a finite projective module to a projective module has an actual
finite projective kernel, by the constructed kernel retraction. -/
theorem presentationKernel_finite_projective [Module.Finite R F]
    [Module.Projective R F] [Module.Projective R P]
    (φ : F →ₗ[R] P) (hφ : Function.Surjective φ) :
    Module.Finite R φ.ker ∧ Module.Projective R φ.ker := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ (LinearMap.id : P →ₗ[R] P) hφ
  let r : F →ₗ[R] φ.ker := splitKernelRetraction φ s hs
  have hr : r.comp φ.ker.subtype = LinearMap.id :=
    LinearMap.ext (fun x => splitKernelRetraction_subtype φ s hs x)
  have hsurj : Function.Surjective r :=
    fun x => ⟨x.val, splitKernelRetraction_subtype φ s hs x⟩
  exact ⟨Module.Finite.of_surjective r hsurj, Module.Projective.of_split φ.ker.subtype r hr⟩

variable {F' : Type v'} [AddCommGroup F'] [Module R F']
  {P' : Type w'} [AddCommGroup P'] [Module R P']

/-- The source transition restricted to the actual kernels of a commutative square. -/
def presentationKernelTransition (φ : F →ₗ[R] P) (ψ : F' →ₗ[R] P')
    (a : F →ₗ[R] F') (b : P →ₗ[R] P') (h : ψ.comp a = b.comp φ) :
    φ.ker →ₗ[R] ψ.ker :=
  (a.comp φ.ker.subtype).codRestrict ψ.ker (by
    intro x
    change ψ (a x.val) = 0
    have hx : ψ (a x.val) = b (φ x.val) := LinearMap.congr_fun h x.val
    rw [hx, LinearMap.mem_ker.mp x.property, map_zero])

/-- The induced transition retains the literal source transition on kernel elements. -/
theorem presentationKernelTransition_val (φ : F →ₗ[R] P) (ψ : F' →ₗ[R] P')
    (a : F →ₗ[R] F') (b : P →ₗ[R] P') (h : ψ.comp a = b.comp φ) (x : φ.ker) :
    (presentationKernelTransition φ ψ a b h x).val = a x.val := rfl

/-- Correcting a lifted source element in the original ideal multiple lifts every
element of the next presentation kernel. -/
theorem presentationKernelTransition_surjective (I : Ideal R)
    (φ : F →ₗ[R] P) (ψ : F' →ₗ[R] P') (a : F →ₗ[R] F') (b : P →ₗ[R] P')
    (h : ψ.comp a = b.comp φ) (hφ : Function.Surjective φ)
    (ha : Function.Surjective a) (hb : b.ker = I • (⊤ : Submodule R P))
    (hIa : I • (⊤ : Submodule R F) ≤ a.ker) :
    Function.Surjective (presentationKernelTransition φ ψ a b h) := by
  intro y
  obtain ⟨x, hx⟩ := ha y.val
  have hφx : φ x ∈ I • (⊤ : Submodule R P) := by
    rw [← hb]
    change b (φ x) = 0
    have hcomm : ψ (a x) = b (φ x) := LinearMap.congr_fun h x
    rw [← hcomm, hx]
    exact LinearMap.mem_ker.mp y.property
  have hmap : (I • (⊤ : Submodule R F)).map φ = I • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
  obtain ⟨c, hc, hcφ⟩ := Submodule.mem_map.mp (hmap.symm ▸ hφx)
  have hac : a c = 0 := LinearMap.mem_ker.mp (hIa hc)
  have hxc : x - c ∈ φ.ker := by
    change φ (x - c) = 0
    rw [map_sub, hcφ, sub_self]
  refine ⟨⟨x - c, hxc⟩, ?_⟩
  apply Subtype.ext
  change a (x - c) = y.val
  rw [map_sub, hac, sub_zero, hx]

/-- Projectivity over the actual coefficient quotient makes the original ideal
filtration on the presentation kernel agree with its induced source filtration. -/
theorem presentationKernelTransition_ker_of_projective_quotient (J I : Ideal R)
    [Module (R ⧸ J) P] [IsScalarTower R (R ⧸ J) P]
    [Module.Projective (R ⧸ J) P]
    (φ : F →ₗ[R] P) (ψ : F' →ₗ[R] P') (a : F →ₗ[R] F') (b : P →ₗ[R] P')
    (h : ψ.comp a = b.comp φ) (hφ : Function.Surjective φ)
    (hJF : Module.IsTorsionBySet R F J) (ha : a.ker = I • (⊤ : Submodule R F)) :
    (presentationKernelTransition φ ψ a b h).ker = I • (⊤ : Submodule R φ.ker) := by
  obtain ⟨s, hs⟩ := exists_lift_of_projective_quotient J hJF φ
    (LinearMap.id : P →ₗ[R] P) hφ
  let r : F →ₗ[R] φ.ker := splitKernelRetraction φ s hs
  ext x
  change (presentationKernelTransition φ ψ a b h) x = 0 ↔
    x ∈ I • (⊤ : Submodule R φ.ker)
  constructor
  · intro hx
    have hax : a x.val = 0 := congrArg Subtype.val hx
    have hxI : x.val ∈ I • (⊤ : Submodule R F) := by
      rw [← ha]
      exact hax
    have hrx : r x.val ∈ I • (⊤ : Submodule R φ.ker) :=
      Submodule.smul_top_le_comap_smul_top I r hxI
    exact (splitKernelRetraction_subtype φ s hs x) ▸ hrx
  · intro hx
    apply Subtype.ext
    change a x.val = 0
    apply LinearMap.mem_ker.mp
    rw [ha]
    exact Submodule.smul_top_le_comap_smul_top I φ.ker.subtype hx

end AdicModuleSystem
