/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafAffSESConnectingHom
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exactness and lifting for compatible affine sections

An affine short exact sequence is left exact on the actual module of
compatible sections of an ordered affine cover. To construct a lift, one
first lifts the sections on individual charts. Their differences on the
overlaps form the existing connecting cocycle. Vanishing of the first
cohomology of the kernel corrects this lift to a compatible family.

These results retain the original component maps of the given sequence.
They are used when lifting sections through successive ideal-power
reductions in formal algebraization.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.OModulePresheaf.AffSES

universe u

open AlgebraicCurves.Cohomology.Sheaves.Proofs
open OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of R)} [IsSeparated f]
  {F₁ F₂ F₃ : OModulePresheaf f}
  (S : AffSES F₁ F₂ F₃) (K : X.OrderedAffineCover)

/-- The inclusion is injective on compatible chart sections. -/
theorem H0Map_inc_injective : Function.Injective (S.inc.H0Map K) := by
  intro x y h
  apply Subtype.ext
  exact (LES.cochain_ses K S 0).1 (congrArg Subtype.val h)

/-- Exactness on compatible chart sections uses the original maps. -/
theorem H0Map_range_inc_eq_ker_proj :
    LinearMap.range (S.inc.H0Map K) = LinearMap.ker (S.proj.H0Map K) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    have hz : S.inc.cochainMap K 0 x.val ∈
        LinearMap.ker (S.proj.cochainMap K 0) := by
      rw [← (LES.cochain_ses K S 0).2.2]
      exact ⟨x.val, rfl⟩
    exact hz
  · intro y hy
    have hproj : S.proj.cochainMap K 0 y.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hy)
    have hrange : y.val ∈ LinearMap.range (S.inc.cochainMap K 0) := by
      rw [(LES.cochain_ses K S 0).2.2]
      exact hproj
    obtain ⟨x, hx⟩ := hrange
    have hcycle : F₁.d K 0 x = 0 := by
      apply (LES.cochain_ses K S 1).1
      rw [map_zero]
      calc
        S.inc.cochainMap K 1 (F₁.d K 0 x) =
            F₂.d K 0 (S.inc.cochainMap K 0 x) :=
          LinearMap.congr_fun (AffHom.cochainMap_comp_d K S.inc 0) x
        _ = F₂.d K 0 y.val := congrArg (F₂.d K 0) hx
        _ = 0 := y.property
    exact ⟨⟨x, hcycle⟩, Subtype.ext hx⟩

/-- Vanishing of the actual first cohomology of the kernel lifts every
compatible family of quotient sections. -/
theorem H0Map_proj_surjective_of_subsingleton_H1 [Subsingleton (F₁.HSucc K 0)] :
    Function.Surjective (S.proj.H0Map K) := by
  obtain ⟨δ₀, _, hzero, _, _, _⟩ := S.exists_connectingHom K
  intro z
  exact hzero (LinearMap.mem_ker.mpr (Subsingleton.elim (δ₀ z) 0))

/-- The analogous lifting statement in positive degree comes from the
same connecting maps, with no change of the original cohomology maps. -/
theorem HSuccMap_proj_surjective_of_subsingleton (i : ℕ)
    [Subsingleton (F₁.HSucc K (i + 1))] :
    Function.Surjective (S.proj.HSuccMap K i) := by
  obtain ⟨_, δ, _, hpos, _, _⟩ := S.exists_connectingHom K
  intro z
  exact hpos i (LinearMap.mem_ker.mpr (Subsingleton.elim (δ i z) 0))

end AlgebraicGeometry.OModulePresheaf.AffSES
