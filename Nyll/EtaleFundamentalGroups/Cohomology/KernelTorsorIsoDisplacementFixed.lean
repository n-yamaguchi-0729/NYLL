/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Cohomology.KernelTorsorIsom

/-! # Equivariance of the same Isom witness after killing its displacement

For the scalar supplied by the arithmetic transport, restricting to a field
containing its chosen radical makes this displacement one. This lemma retains
the original isomorphism rather than selecting another one.
-/
noncomputable section
namespace EtaleFundamentalGroups.Cohomology

/-- A trivial conjugation displacement at one point makes the original
coefficient-equivariant isomorphism equivariant for that arithmetic element. -/
theorem KernelTorsorIso.equivariant_of_displacement_eq_one
    {P G A X Y : Type*} [Group P] [Group G] [CommGroup A]
    [MulDistribMulAction G A] [Torsor A X] [Torsor A Y]
    [MulAction P X] [MulAction P Y]
    (q : P →* G)
    (hX : ∀ (p : P) (a : A) (x : X), p • (a • x) = (q p • a) • (p • x))
    (hY : ∀ (p : P) (a : A) (y : Y), p • (a • y) = (q p • a) • (p • y))
    (e : KernelTorsorIso (X := X) (Y := Y) q A) (x₀ : X) (p : P)
    (hd : ((p • e.val (p⁻¹ • x₀)) /ₛ e.val x₀ : A) = 1) :
    ∀ x, e.val (p • x) = p • e.val x := by
  have he : kernelTorsorIsoConjugate q hX hY p e = e := by
    apply KernelTorsorIso.ext_at q _ _ x₀
    change p • e.val (p⁻¹ • x₀) = e.val x₀
    calc
      _ = ((p • e.val (p⁻¹ • x₀)) /ₛ e.val x₀ : A) • e.val x₀ :=
        (sdiv_smul _ _).symm
      _ = _ := by rw [hd, one_smul]
  intro x
  have hx := congrArg (fun f : KernelTorsorIso (X := X) (Y := Y) q A =>
    f.val (p • x)) he
  change p • e.val (p⁻¹ • (p • x)) = e.val (p • x) at hx
  simpa only [inv_smul_smul] using hx.symm

end EtaleFundamentalGroups.Cohomology
