/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerSectionProduct
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionAssociator
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Multiplying sections of tensor twists

The native associator and tensor-power comparison multiply a section of
`F ⊗ Lᵐ` by a section of `Lⁿ`. This multiplication commutes with restriction.
When both powers arise from one section of `L`, the result is its power of
degree `m + n`. Thus an extension obtained in one degree gives extensions
in every larger degree, with their restrictions computed in the original
module sheaves.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F L : X.Modules} {U : X.Opens}

/-- Multiply a section of a tensor twist by a section of a tensor power,
using the actual associator and addition comparison. -/
def tensorTwistSections (m n : ℕ) (s : Γ(F ⊗ L.tensorPow m, U))
    (t : Γ(L.tensorPow n, U)) : Γ(F ⊗ L.tensorPow (m + n), U) :=
  ((α_ F (L.tensorPow m) (L.tensorPow n)).hom ≫
    F ◁ (tensorPowAdd L m n).hom).app U (tensorSections s t)

/-- Multiplication of tensor-twist sections is compatible with restriction
to any smaller open subset. -/
theorem map_tensorTwistSections (m n : ℕ) {V : X.Opens} (i : V ⟶ U)
    (s : Γ(F ⊗ L.tensorPow m, U)) (t : Γ(L.tensorPow n, U)) :
    (F ⊗ L.tensorPow (m + n)).presheaf.map i.op (tensorTwistSections m n s t) =
      tensorTwistSections m n ((F ⊗ L.tensorPow m).presheaf.map i.op s)
        ((L.tensorPow n).presheaf.map i.op t) := by
  let φ : (F ⊗ L.tensorPow m) ⊗ L.tensorPow n ⟶ F ⊗ L.tensorPow (m + n) :=
    (α_ F (L.tensorPow m) (L.tensorPow n)).hom ≫ F ◁ (tensorPowAdd L m n).hom
  have hφ := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op)
    (tensorSections s t)
  change (F ⊗ L.tensorPow (m + n)).presheaf.map i.op
      (φ.app U (tensorSections s t)) =
    φ.app V (tensorSections ((F ⊗ L.tensorPow m).presheaf.map i.op s)
      ((L.tensorPow n).presheaf.map i.op t))
  exact hφ.symm.trans (congrArg (φ.app V) (map_tensorSections i s t))

/-- The multiplication sends two powers of the same section to its power
of the sum degree, keeping the original module section unchanged. -/
theorem tensorTwistSections_tensorPowSection (s : Γ(F, U)) (g : Γ(L, U))
    (m n : ℕ) :
    tensorTwistSections m n (tensorSections s (tensorPowSection g m))
        (tensorPowSection g n) =
      tensorSections s (tensorPowSection g (m + n)) := by
  rw [tensorTwistSections, Hom.comp_app, CategoryTheory.comp_apply,
    associator_hom_app_tensorSections, whiskerLeft_app_tensorSections,
    tensorPowAdd_hom_app_tensorSections_tensorPowSection]

/-- A twisted extension in degree `m` yields an extension in degree `m + n`
by multiplication by the `n`-th power of the same global section. -/
theorem exists_tensor_twist_extension_add (g : Γ(L, ⊤)) (s : Γ(F, U)) (m n : ℕ)
    (z : Γ(F ⊗ L.tensorPow m, ⊤))
    (hz : (F ⊗ L.tensorPow m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op z =
      tensorSections s
        ((L.tensorPow m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (tensorPowSection g m))) :
    ∃ w : Γ(F ⊗ L.tensorPow (m + n), ⊤),
      (F ⊗ L.tensorPow (m + n)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op w =
        tensorSections s
          ((L.tensorPow (m + n)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            (tensorPowSection g (m + n))) := by
  refine ⟨tensorTwistSections m n z (tensorPowSection g n), ?_⟩
  rw [map_tensorTwistSections, hz, map_tensorPowSection, map_tensorPowSection,
    map_tensorPowSection, tensorTwistSections_tensorPowSection]

/-- Once a twisted extension exists, it exists in every larger degree. -/
theorem exists_tensor_twist_extension_of_le (g : Γ(L, ⊤)) (s : Γ(F, U))
    {m d : ℕ} (hmd : m ≤ d) (z : Γ(F ⊗ L.tensorPow m, ⊤))
    (hz : (F ⊗ L.tensorPow m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op z =
      tensorSections s
        ((L.tensorPow m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (tensorPowSection g m))) :
    ∃ w : Γ(F ⊗ L.tensorPow d, ⊤),
      (F ⊗ L.tensorPow d).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op w =
        tensorSections s
          ((L.tensorPow d).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            (tensorPowSection g d)) := by
  have h := exists_tensor_twist_extension_add g s m (d - m) z hz
  rw [Nat.add_sub_of_le hmd] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
