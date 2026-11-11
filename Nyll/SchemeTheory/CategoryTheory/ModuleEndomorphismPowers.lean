/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Logic.Function.Iterate

/-! # Powers of functorial module actions -/

@[expose] public section

universe v

open CategoryTheory

namespace CategoryTheory.Functor

/-- An actual intertwining of a module endomorphism and a functorial action
intertwines every power, using the existing iterate and endomorphism laws. -/
theorem moduleAction_semiconj_pow
    {S : Type*} [CommRing S] {P : Type*} [AddCommGroup P] [Module S P]
    {D : Type*} [Category D] (H : D ⥤ ModuleCat.{v} S) {A : D}
    (a : Module.End S P) (b : End A) (e : P → H.obj A)
    (h : ∀ x, e (a x) = H.map b.asHom (e x)) (m : ℕ) (x : P) :
    e ((a ^ m) x) = H.map (b ^ m).asHom (e x) := by
  let φ : End A →* Module.End S (H.obj A) :=
    (ModuleCat.endRingEquiv (H.obj A)).toMonoidHom.comp (Functor.mapEnd A H)
  have hs : Function.Semiconj e a (φ b) := h
  have hp : e ((a ^ m) x) = ((φ b) ^ m) (e x) := by
    simpa only [Module.End.pow_apply] using hs.iterate_right m x
  exact hp.trans (congrArg (fun t : Module.End S (H.obj A) => t (e x))
    (φ.map_pow b m).symm)

end CategoryTheory.Functor
