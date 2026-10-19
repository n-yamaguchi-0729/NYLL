/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveSplittingLift
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Projective lifting over the actual quotient ring

The modules at level `n` of an adic system are projective over the quotient
ring, rather than over the original ring. This file uses precisely that
projectivity. Linear maps between quotient-ring modules are upgraded along
the surjective coefficient map. Torsion modules acquire their canonical
quotient-ring action, so projective lifting constructs maps which are then
restricted to the original scalars.

The resulting splitting lift keeps a prescribed further reduction. It is
the successive-step construction for compatible projective adic systems.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w z

variable {R : Type u} [CommRing R]

/-- An original-ring linear map between modules over a quotient ring is
linear over that quotient, because every coefficient has a representative. -/
def overQuotientLinearMap (J : Ideal R)
    {N : Type v} [AddCommGroup N] [Module R N] [Module (R ⧸ J) N]
    [IsScalarTower R (R ⧸ J) N]
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module (R ⧸ J) Q]
    [IsScalarTower R (R ⧸ J) Q] (f : N →ₗ[R] Q) : N →ₗ[R ⧸ J] Q where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro a x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change f (algebraMap R (R ⧸ J) r • x) = algebraMap R (R ⧸ J) r • f x
    rw [IsScalarTower.algebraMap_smul, f.map_smul, IsScalarTower.algebraMap_smul]

theorem overQuotientLinearMap_apply (J : Ideal R)
    {N : Type v} [AddCommGroup N] [Module R N] [Module (R ⧸ J) N]
    [IsScalarTower R (R ⧸ J) N]
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module (R ⧸ J) Q]
    [IsScalarTower R (R ⧸ J) Q] (f : N →ₗ[R] Q) (x : N) :
    overQuotientLinearMap J f x = f x := rfl

/-- Projectivity over `R/J` lifts original-ring linear maps through a
surjection whose source is annihilated by `J`. The quotient-ring structures
on the target modules are constructed from this annihilation. -/
theorem exists_lift_of_projective_quotient (J : Ideal R)
    {P : Type v} [AddCommGroup P] [Module R P] [Module (R ⧸ J) P]
    [IsScalarTower R (R ⧸ J) P] [Module.Projective (R ⧸ J) P]
    {N : Type w} [AddCommGroup N] [Module R N]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (hJN : Module.IsTorsionBySet R N J)
    (f : N →ₗ[R] Q) (g : P →ₗ[R] Q) (hf : Function.Surjective f) :
    ∃ s : P →ₗ[R] N, f.comp s = g := by
  have hJQ : Module.IsTorsionBySet R Q J := by
    intro q a
    obtain ⟨x, rfl⟩ := hf q
    calc
      (a : R) • f x = f ((a : R) • x) := (f.map_smul (a : R) x).symm
      _ = f 0 := congrArg f (hJN (x := x) (a := a))
      _ = 0 := f.map_zero
  let moduleN : Module (R ⧸ J) N := hJN.module
  let moduleQ : Module (R ⧸ J) Q := hJQ.module
  have towerN : IsScalarTower R (R ⧸ J) N := hJN.isScalarTower
  have towerQ : IsScalarTower R (R ⧸ J) Q := hJQ.isScalarTower
  let fJ : N →ₗ[R ⧸ J] Q := overQuotientLinearMap J f
  let gJ : P →ₗ[R ⧸ J] Q := overQuotientLinearMap J g
  obtain ⟨s, hs⟩ := Module.projective_lifting_property fJ gJ hf
  refine ⟨s.restrictScalars R, ?_⟩
  exact LinearMap.ext (fun p => LinearMap.congr_fun hs p)

/-- A quotient-ring projective module admits a splitting with any
prescribed further reduction. All maps in the conclusion use the original
ring scalars, as do the transition maps of the adic module system. -/
theorem exists_splitting_lift_of_projective_quotient (J I : Ideal R)
    {F : Type v} [AddCommGroup F] [Module R F]
    {P : Type w} [AddCommGroup P] [Module R P] [Module (R ⧸ J) P]
    [IsScalarTower R (R ⧸ J) P] [Module.Projective (R ⧸ J) P]
    (hJF : Module.IsTorsionBySet R F J)
    (f : F →ₗ[R] P) (hf : Function.Surjective f)
    (s₀ : P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R] F ⧸ (I • (⊤ : Submodule R F)))
    (hs₀ : (reduceMap I f).comp s₀ = LinearMap.id) :
    ∃ s : P →ₗ[R] F,
      f.comp s = LinearMap.id ∧
      (I • (⊤ : Submodule R F)).mkQ.comp s =
        s₀.comp (I • (⊤ : Submodule R P)).mkQ := by
  let U : Submodule R F := I • (⊤ : Submodule R F)
  let V : Submodule R P := I • (⊤ : Submodule R P)
  obtain ⟨l, hl⟩ := exists_lift_of_projective_quotient J hJF U.mkQ
    (s₀.comp V.mkQ) (Submodule.mkQ_surjective U)
  have hl_apply : ∀ p : P, U.mkQ (l p) = s₀ (V.mkQ p) :=
    fun p => LinearMap.congr_fun hl p
  have hs_apply : ∀ p : P, reduceMap I f (s₀ (V.mkQ p)) = V.mkQ p :=
    fun p => LinearMap.congr_fun hs₀ (V.mkQ p)
  have herr : ∀ p : P, f (l p) - p ∈ V := by
    intro p
    apply (Submodule.Quotient.eq V).mp
    calc
      V.mkQ (f (l p)) = reduceMap I f (U.mkQ (l p)) :=
        (reduceMap_mk I f (l p)).symm
      _ = reduceMap I f (s₀ (V.mkQ p)) := congrArg (reduceMap I f) (hl_apply p)
      _ = V.mkQ p := hs_apply p
  let e : P →ₗ[R] V :=
    ((f.comp l) - (LinearMap.id : P →ₗ[R] P)).codRestrict V herr
  let fI : U →ₗ[R] V :=
    (f.comp U.subtype).codRestrict V
      (fun a => Submodule.smul_top_le_comap_smul_top I f a.property)
  have hfI : Function.Surjective fI := by
    have hmap : U.map f = V := by
      change (I • (⊤ : Submodule R F)).map f = I • (⊤ : Submodule R P)
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    intro p
    have hp : p.val ∈ U.map f := by
      rw [hmap]
      exact p.property
    obtain ⟨a, ha, hap⟩ := Submodule.mem_map.mp hp
    exact ⟨⟨a, ha⟩, Subtype.ext hap⟩
  have hJU : Module.IsTorsionBySet R U J := by
    intro a r
    exact Subtype.ext (hJF (x := a.val) (a := r))
  obtain ⟨c, hc⟩ := exists_lift_of_projective_quotient J hJU fI e hfI
  have hc_apply : ∀ p : P, f (c p).val = f (l p) - p :=
    fun p => congrArg Subtype.val (LinearMap.congr_fun hc p)
  let s : P →ₗ[R] F := l - U.subtype.comp c
  refine ⟨s, ?_, ?_⟩
  · apply LinearMap.ext
    intro p
    change f (l p - (c p).val) = p
    rw [map_sub, hc_apply, sub_sub_cancel]
  · apply LinearMap.ext
    intro p
    change U.mkQ (l p - (c p).val) = s₀ (V.mkQ p)
    have hq : U.mkQ (c p).val = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr (c p).property
    rw [map_sub, hq, sub_zero, hl_apply]

end AdicModuleSystem
