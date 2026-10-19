/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.FrameFromTrivialization
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Tensor.FrameCoverExactness
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Topology.Sets.Opens

/-!
# Exactness of the original tensor functor for an invertible module sheaf

The local trivializations in the definition of invertibility give actual
sections that frame the sheaf on a cover indexed by points. The existing
frame-cover exactness theorem then proves finite-limit preservation for
the original tensor functor. The same frames, raised to their actual
tensor powers, supply this for every nonnegative tensor power.

Consequently the original short complex tensored with an invertible
sheaf remains short exact. Its arrows are precisely the original arrows
tensored with the identity, and their action on local tensor sections
is retained. No separate flatness hypothesis is imposed.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules}

/-- The original local trivializations of an invertible sheaf supply an actual cover by frames. -/
theorem IsInvertible.exists_frame_cover (hL : IsInvertible L) :
    ∃ (U : X → X.Opens) (s : ∀ x : X, Γ(L, U x)),
      (∀ x : X, IsFrameOn (s x) (U x)) ∧ ⨆ x : X, U x = ⊤ := by
  have hpoint : ∀ x : X, ∃ (U : X.Opens) (s : Γ(L, U)), x ∈ U ∧ IsFrameOn s U := by
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := hL.exists_trivialization x
    obtain ⟨s, hs⟩ := exists_isFrameOn_of_pullback_iso_unit U e
    exact ⟨U, s, hx, hs⟩
  choose U s hx hs using hpoint
  refine ⟨U, s, hs, ?_⟩
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- Tensoring with the original invertible sheaf preserves finite limits. -/
theorem IsInvertible.tensorRight_preservesFiniteLimits (hL : IsInvertible L) :
    PreservesFiniteLimits (tensorRight L) := by
  obtain ⟨U, s, hs, hcover⟩ := hL.exists_frame_cover
  exact tensorRight_preservesFiniteLimits_of_frame_cover L U s hs hcover

/-- The actual tensor powers of local frames prove exactness for every nonnegative twist. -/
theorem IsInvertible.tensorRight_tensorPow_preservesFiniteLimits (hL : IsInvertible L)
    (d : ℕ) : PreservesFiniteLimits (tensorRight (L.tensorPow d)) := by
  obtain ⟨U, s, hs, hcover⟩ := hL.exists_frame_cover
  exact tensorRight_preservesFiniteLimits_of_frame_cover (L.tensorPow d) U
    (fun x => tensorPowSection (s x) d) (fun x => (hs x).tensorPowSection_monoidalV2 d) hcover

/-- The original short complex remains short exact after tensoring with an invertible sheaf. -/
theorem IsInvertible.shortExact_tensorRight (hL : IsInvertible L)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (tensorRight L)).ShortExact := by
  have : (tensorRight L).IsLeftAdjoint := inferInstance
  have : PreservesFiniteLimits (tensorRight L) := hL.tensorRight_preservesFiniteLimits
  exact hS.map_of_exact (tensorRight L)

/-- The original short complex remains short exact after every nonnegative invertible twist. -/
theorem IsInvertible.shortExact_tensorRight_tensorPow (hL : IsInvertible L)
    (d : ℕ) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (tensorRight (L.tensorPow d))).ShortExact := by
  have : (tensorRight (L.tensorPow d)).IsLeftAdjoint := inferInstance
  have : PreservesFiniteLimits (tensorRight (L.tensorPow d)) :=
    hL.tensorRight_tensorPow_preservesFiniteLimits d
  exact hS.map_of_exact (tensorRight (L.tensorPow d))

variable (L) (S : ShortComplex X.Modules)

/-- The first arrow is the original first arrow tensored with the original identity. -/
theorem tensorRight_shortComplex_f : (S.map (tensorRight L)).f = S.f ⊗ₘ 𝟙 L :=
  (MonoidalCategory.tensorHom_id S.f L).symm

/-- The second arrow is the original second arrow tensored with the original identity. -/
theorem tensorRight_shortComplex_g : (S.map (tensorRight L)).g = S.g ⊗ₘ 𝟙 L :=
  (MonoidalCategory.tensorHom_id S.g L).symm

/-- The first tensored arrow acts on the original first factor of a local tensor section. -/
theorem tensorRight_shortComplex_f_tensorSections (U : X.Opens)
    (x : Γ(S.X₁, U)) (t : Γ(L, U)) :
    (S.map (tensorRight L)).f.app U (tensorSections x t) = tensorSections (S.f.app U x) t :=
  whiskerRight_app_tensorSections S.f L x t

/-- The second tensored arrow acts on the original first factor of a local tensor section. -/
theorem tensorRight_shortComplex_g_tensorSections (U : X.Opens)
    (x : Γ(S.X₂, U)) (t : Γ(L, U)) :
    (S.map (tensorRight L)).g.app U (tensorSections x t) = tensorSections (S.g.app U x) t :=
  whiskerRight_app_tensorSections S.g L x t

end AlgebraicGeometry.Scheme.Modules
