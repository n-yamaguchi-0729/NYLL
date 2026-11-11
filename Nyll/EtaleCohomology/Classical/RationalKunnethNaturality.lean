/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleCohomology.Classical.RationalExternalCupPullback
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Naturality of the actual rational Künneth map

A map between the actual scheme fibre products, induced by commuting
maps on the factors and base, pulls external cup back to the external cup
of the original factor pullbacks. Consequently both the original tensor
component and full direct-sum Künneth map commute with those pullbacks.
No Künneth isomorphism or duality assertion is used.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped DirectSum TensorProduct

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y S X' Y' S' : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
  (v : X' ⟶ X) (w : Y' ⟶ Y) (s : S' ⟶ S)
  (hf : f' ≫ s = v ≫ f) (hg : g' ≫ s = w ≫ g)

/-- The original fibre-product map preserves the actual external cup
after pullback of its two factors by the original scheme morphisms. -/
theorem rationalEllAdicExternalCup_map (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicCohomologyPullback ℓ (pullback.map f' g' f g v w s hf hg) c
        (rationalEllAdicExternalCup ℓ f g a b c h x y) =
      rationalEllAdicExternalCup ℓ f' g' a b c h
        (rationalEllAdicCohomologyPullback ℓ v a x)
        (rationalEllAdicCohomologyPullback ℓ w b y) := by
  rw [rationalEllAdicExternalCup_pullback]
  simp only [pullback.map, pullback.lift_fst, pullback.lift_snd,
    rationalEllAdicCohomologyPullback_comp, LinearMap.comp_apply,
    rationalEllAdicExternalCup_apply]

/-- The actual Künneth component is natural for the original map
between the scheme fibre products and the tensor of factor pullbacks. -/
theorem rationalEllAdicKunnethComponent_naturality (a b c : ℕ) (h : a + b = c) :
    (rationalEllAdicCohomologyPullback ℓ (pullback.map f' g' f g v w s hf hg) c).comp
        (rationalEllAdicKunnethComponent ℓ f g a b c h) =
      (rationalEllAdicKunnethComponent ℓ f' g' a b c h).comp
        (TensorProduct.map (rationalEllAdicCohomologyPullback ℓ v a)
          (rationalEllAdicCohomologyPullback ℓ w b)) := by
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, rationalEllAdicKunnethComponent_tmul,
    TensorProduct.map_tmul] using
    rationalEllAdicExternalCup_map ℓ f g f' g' v w s hf hg a b c h x y

/-- The full original Künneth map is natural in both factors and the
base. The domain map is the actual tensor pullback in each summand. -/
theorem rationalEllAdicKunnethMap_naturality (n : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (pullback.map f' g' f g v w s hf hg) n).comp
        (rationalEllAdicKunnethMap ℓ f g n) =
      (rationalEllAdicKunnethMap ℓ f' g' n).comp
        (DirectSum.lmap (fun d : Fin (n + 1) =>
          TensorProduct.map (rationalEllAdicCohomologyPullback ℓ v d.val)
            (rationalEllAdicCohomologyPullback ℓ w (n - d.val)))) := by
  apply DirectSum.linearMap_ext
  intro d
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, rationalEllAdicKunnethMap_lof_tmul,
    DirectSum.lmap_lof, TensorProduct.map_tmul] using
    rationalEllAdicExternalCup_map ℓ f g f' g' v w s hf hg d.val (n - d.val) n
      (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)) x y

end EtaleCohomology.Classical
