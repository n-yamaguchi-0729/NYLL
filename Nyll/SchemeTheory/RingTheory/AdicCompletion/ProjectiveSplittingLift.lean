/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Lifting a prescribed splitting modulo an ideal

For a projective module `P`, a surjection `F → P`, and a prescribed splitting
after reduction modulo `I`, this file constructs a splitting over the ring
whose reduction is the prescribed one. A projective lift first produces a
map with the desired reduction. Its failure to be a section lies in `IP`;
lifting that error through `IF → IP` and subtracting it makes the map a
section without changing its reduction.

Applied over successive ideal-power quotient rings, this supplies compatible
splittings for a system of finite projective modules. No splitting over the
original ring is an input to the construction.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R]
  {F : Type v} [AddCommGroup F] [Module R F]
  {P : Type w} [AddCommGroup P] [Module R P]

/-- Reduction of a linear map modulo the action of an ideal. -/
def reduceMap (I : Ideal R) (f : F →ₗ[R] P) :
    F ⧸ (I • (⊤ : Submodule R F)) →ₗ[R] P ⧸ (I • (⊤ : Submodule R P)) :=
  Submodule.mapQ (I • (⊤ : Submodule R F)) (I • (⊤ : Submodule R P)) f
    (Submodule.smul_top_le_comap_smul_top I f)

theorem reduceMap_mk (I : Ideal R) (f : F →ₗ[R] P) (x : F) :
    reduceMap I f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  Submodule.mapQ_apply _ _ f x

/-- The given quotient-level splitting extends to an actual splitting
with exactly that reduction. -/
theorem exists_splitting_lift [Module.Projective R P]
    (I : Ideal R) (f : F →ₗ[R] P) (hf : Function.Surjective f)
    (s₀ : P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R] F ⧸ (I • (⊤ : Submodule R F)))
    (hs₀ : (reduceMap I f).comp s₀ = LinearMap.id) :
    ∃ s : P →ₗ[R] F,
      f.comp s = LinearMap.id ∧
      (I • (⊤ : Submodule R F)).mkQ.comp s =
        s₀.comp (I • (⊤ : Submodule R P)).mkQ := by
  let U : Submodule R F := I • (⊤ : Submodule R F)
  let V : Submodule R P := I • (⊤ : Submodule R P)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property U.mkQ (s₀.comp V.mkQ)
    (Submodule.mkQ_surjective U)
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
  obtain ⟨c, hc⟩ := Module.projective_lifting_property fI e hfI
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
