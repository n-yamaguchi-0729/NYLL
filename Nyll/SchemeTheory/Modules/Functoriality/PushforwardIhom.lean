/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Internal Hom and the original direct-image functor

The monoidal comparison for actual pullback identifies its tensor-left
composites. Uniqueness of their right adjoints then identifies internal
Hom into the original direct image with the direct image of internal Hom.
For an open immersion, the existing pullback-restriction comparison gives
the same result for the native restriction functor.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual closed-adjunction comparison for direct image. -/
def ihomPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules) :
    (ihom M).obj ((pushforward f).obj N) ≅
      (pushforward f).obj ((ihom ((pullback f).obj M)).obj N) :=
  (Adjunction.rightAdjointUniq
    ((ihom.adjunction M).comp (pullbackPushforwardAdjunction f))
    (((pullbackPushforwardAdjunction f).comp
      (ihom.adjunction ((pullback f).obj M))).ofNatIsoLeft
        (Functor.Monoidal.commTensorLeft (pullback f) M))).app N

/-- The same actual direct-image comparison, using native open restriction. -/
def ihomPushforwardRestrictIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (N : X.Modules) :
    (ihom M).obj ((pushforward j).obj N) ≅
      (pushforward j).obj ((ihom (M.restrict j)).obj N) :=
  ihomPushforwardIso j M N ≪≫
    (pushforward j).mapIso
      (((MonoidalClosed.internalHom (C := X.Modules)).mapIso
        ((restrictFunctorIsoPullback j).app M).op).app N)

end AlgebraicGeometry.Scheme.Modules
