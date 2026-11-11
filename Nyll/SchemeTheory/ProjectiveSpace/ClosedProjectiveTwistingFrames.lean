/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf

/-!
# Actual twisting frames on closed-projective Čech intersections

Restrict the pullback of the first coordinate frame of an increasing
Čech tuple. Its tensor powers give frames of every nonnegative twist on
the original intersection; no compatibility of chosen frames is needed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom j]

/-- Every original coordinate-cover intersection carries an actual
frame of each tensor power of the pulled-back twisting sheaf. -/
theorem exists_twistingPow_frame_stdCoverPullback_inter
    (d k : ℕ) (s : (stdCoverPullback (A := R) (n := n) j).Idx k) :
    ∃ t : Γ(((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d,
      (stdCoverPullback (A := R) (n := n) j).inter s),
      IsFrameOn t ((stdCoverPullback (A := R) (n := n) j).inter s) := by
  let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
  let C : Y.OrderedAffineCover := stdCoverPullback (A := R) (n := n) j
  let σ : Γ(L, j ⁻¹ᵁ (⊤ : (Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Opens)) :=
    pullbackLocalSection j (twistingCoordinateSection R n (s.val 0).down)
  have hσ : IsFrameOn σ (C.U (s.val 0)) :=
    (isFrameOn_twistingCoordinateSection R n (s.val 0).down).pullbackLocalSection j
  have htop : C.inter s ≤ j ⁻¹ᵁ (⊤ : (Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Opens) := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  let t : Γ(L, C.inter s) := L.presheaf.map (homOfLE htop).op σ
  have ht : IsFrameOn t (C.inter s) :=
    (hσ.map (homOfLE htop)).mono (C.inter_le s 0)
  exact ⟨tensorPowSection t d, ht.tensorPowSection_monoidalV2 d⟩

end AlgebraicGeometry.ProjSpace
